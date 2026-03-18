/**
 * LLMClient — Anthropic API wrapper for candidate generation.
 *
 * Drives the proposal side of the LLM ↔ CAS feedback loop.
 * The LLM client is fully generic: it uses the ProblemSpec's answerSchema
 * to dynamically build the tool the LLM calls, and uses verifier-provided
 * feedback text (not hardcoded diff formatting) to refine proposals.
 *
 * Design decisions:
 *   - Claude Sonnet 4.6 with thinking disabled + forced tool_choice.
 *   - Streaming with finalMessage(): prevents HTTP timeouts.
 *   - JSON extracted via tool_use (not code blocks) for reliability.
 *   - The system prompt is cached (cache_control: ephemeral).
 */

import Anthropic from "@anthropic-ai/sdk";
import type { ProblemSpec, VerificationResult, HistoryEntry } from "./types";

// ── Default TheoryJson schema (used when verifier doesn't provide one) ───────

const DEFAULT_ANSWER_SCHEMA: Record<string, unknown> = {
  type: "object",
  properties: {
    name:      { type: "string", description: "Theory name" },
    doctrine:  { type: "string", description: "Doctrine string, e.g. MonoidalCategory" },
    objects:   { type: "array",  description: "List of {name, description?} objects",
                 items: { type: "object" } },
    morphisms: { type: "array",  description: "List of {name, domain, codomain, description?}",
                 items: { type: "object" } },
    axioms:    { type: "array",  description: "List of {name, lhs, rhs, description?}",
                 items: { type: "object" } },
  },
  required: ["name", "objects", "morphisms", "axioms"],
};

// ── System prompt (sent once, cached) ────────────────────────────────────────

const SYSTEM_PROMPT = `You are a mathematical problem solver working with a rigorous Computer Algebra System (CAS) for categorical theories.

Your task is to propose candidate solutions in JSON format. The CAS will verify each proposal and return structured feedback describing what is wrong.

**What "≅" means here:** The CAS checks structural equivalence — same number of objects, morphisms with matching domain/codomain shapes (position-normalized, ignoring names), and axioms that reduce to the same normal forms under rewriting. Generator names do NOT matter; only structural shapes do. §0 = first object, §1 = second, etc.

You will receive structured feedback describing exactly what is wrong with your previous proposal.

## Operator Glossary

| Operator | What it does |
|----------|-------------|
| \`identity\` | No-op. X = target verbatim. |
| \`opposite\` | Reverses all morphism directions. Swap domain↔codomain, reverse \`comp\` order. Involution. |
| \`mirror\` | Stone duality. Swap \`prod\`↔\`coprod\`, \`terminal\`↔\`initial\`. Preserves direction. Involution. |
| \`decategorify_iso\` | Collapse one categorical level via iso classes. Objects→generators, morphism iso classes→equations. |
| \`decategorify_K0\` | Grothendieck group K₀. Objects→formal generators, short exact sequences→relations. |
| \`decategorify_chi\` | Euler characteristic. Collapse graded structure to alternating sum. |
| \`arrow\` | Arrow category C^→. Objects are morphisms of C, morphisms are commutative squares. |
| \`twisted_arrow\` | Twisted arrow category Tw(C). Like arrow but with contravariant source. |
| \`karoubi\` | Karoubi envelope / idempotent completion. Adds formal images of all idempotents. |
| \`morita\` | Morita envelope / Cauchy completion. Idempotent completion + absolute colimits. |
| \`macneille\` | MacNeille completion. Embeds a poset into a complete lattice. |
| \`reg_completion\` | Regular completion. Freely add coequalizers of kernel pairs. |
| \`ex_completion\` | Exact completion. Freely add quotients of equivalence relations. |
| \`ind_completion\` | Ind-completion. Freely add filtered colimits. |
| \`pro_completion\` | Pro-completion. Freely add cofiltered limits. |
| \`presheaf\` | Presheaf category PSh(C) = [C^op, Set]. |
| \`family\` | Family construction Fam(C). Objects are families of objects of C. |
| \`scone\` | Freyd cover / scone. Comma category (Set ↓ Γ) for global sections Γ. |
| \`syntactic\` | Syntactic / classifying category of a theory. |
| \`chain_complex\` | Category of chain complexes Ch(C) with differentials d∘d = 0. |
| \`homotopy\` | Homotopy category K(C). Chain complexes modulo homotopy equivalence. |
| \`derived\` | Derived category D(C). Localize K(C) at quasi-isomorphisms. |
| \`stabilize\` | Stabilization / spectra. Formal desuspension. |
| \`center\` | Monoidal center Z(C). Objects are pairs (X, half-braiding). |
| \`drinfeld_center\` | Drinfeld center. Braided monoidal center with explicit braiding data. |
| \`booleanize\` | Booleanization. Forces double negation elimination (Heyting → Boolean). |
| \`span\` | Span category Span(C). Morphisms are spans A ← S → B. |
| \`cospan\` | Cospan category Cospan(C). Morphisms are cospans A → S ← B. |
| \`nerve\` | Simplicial nerve N(C). Produces a simplicial set from a category. |
| \`realize\` | Realization / fundamental category. Left adjoint to nerve. |
| \`isbell_spec\` | Isbell spectrum (left adjoint of Isbell duality). |
| \`isbell_cospec\` | Isbell costructure spectrum (right adjoint). |
| \`isbell\` | Full Isbell adjunction O ⊣ Spec. |
| \`matrix\` | Matrix category Mat(C). Formal biproducts of objects. |
| \`int\` | Int construction. Produces a compact closed category from a traced one. |
| \`internal_cat\` | Internal categories Cat(C). Categories internal to C. |
| \`path\` | Path category / free category on a graph. |
| \`operad_envelope\` | Operadic envelope. From a multicategory to a monoidal category. |

## Theory JSON Format

\`\`\`json
{
  "name": "MyTheory",
  "doctrine": "MonoidalCategory",
  "objects": [
    { "name": "A", "description": "The carrier object" }
  ],
  "morphisms": [
    { "name": "μ", "domain": {"prod": ["A", "A"]}, "codomain": "A", "description": "multiplication" },
    { "name": "η", "domain": "terminal", "codomain": "A", "description": "unit" }
  ],
  "axioms": [
    {
      "name": "assoc",
      "lhs": {"comp": [{"prod": [{"atom":"μ"}, {"id":"A"}]}, {"atom":"μ"}]},
      "rhs": {"comp": [{"prod": [{"id":"A"}, {"atom":"μ"}]}, {"atom":"μ"}]}
    }
  ]
}
\`\`\`

## Expr JSON Reference

| JSON | Meaning |
|------|---------|
| \`"A"\` | Object atom named A (shorthand) |
| \`{"atom": "f"}\` | Morphism atom named f |
| \`{"comp": [e1, e2]}\` | e1 ∘ e2 |
| \`{"tensor": [e1, e2]}\` | e1 ⊗ e2 |
| \`{"prod": [e1, e2]}\` | e1 × e2 |
| \`{"hom": [e1, e2]}\` | Hom(e1, e2) |
| \`{"id": e}\` | id_e |
| \`"unit"\` | Unit object I |
| \`"terminal"\` | Terminal object 1 |
| \`"initial"\` | Initial object 0 |

## Doctrine Strings

Valid values: Category, CartesianCategory, MonoidalCategory, BraidedMonoidal, SymmetricMonoidal, FinitelyComplete, Abelian, Topos, LawvereTheory, ElementaryTopos, MartinLofTypeTheory, ModelCategory, and others.

## Rules

1. Submit your proposal by calling the provided tool. Do not output text —
   your entire response should be the tool call with your answer as its argument.
2. List objects in the ORDER they appear in the target theory. The CAS uses positional
   matching — wrong order causes false structural failures even if the names are right.
3. Keep the candidate as simple as possible. The CAS verifies by forward-applying an
   operator to your candidate, not by inspecting it directly.
4. Axiom LHS and RHS must be Exprs built from the theory's own morphism and object atoms.
5. When fixing a diff, address EVERY error listed in the feedback.
6. DO NOT redefine doctrine-native structures as custom generators. If your doctrine is
   \`MonoidalCategory\`, do NOT add a \`tensor\` or \`unit\` morphism to the \`morphisms\` array.
   Use the built-in \`{"tensor": [...]}\` and \`"unit"\` Exprs directly in domains/codomains.
   Generators are strictly for custom algebraic/topological data beyond what the doctrine provides.
8. ORIENT YOUR AXIOMS to prevent infinite rewriting loops (Timeouts). Write axioms as
   left-to-right reduction rules (Complex → Simple). Avoid symmetric axioms like
   \`f ∘ g = g ∘ f\` — if commutativity is needed, break it into intermediate steps
   or use a canonical ordering.
9. IMPLICIT MORPHISMS: The target theory's axioms may reference morphism atoms that are
   NOT listed in the target's \`morphisms\` array (e.g. "eq" appearing in axioms but not
   in the morphisms list). These are real morphisms — include them in YOUR candidate
   (with appropriately transformed domain/codomain).
10. VERIFY YOUR SHAPE: Before submitting, count your objects, morphisms, and axioms.
    Compare against the expected shape shown in the problem description. A mismatch in
    counts is almost always wrong.`;

// ── LLMClient ─────────────────────────────────────────────────────────────────

export class LLMClient {
  private client: Anthropic;

  constructor(apiKey?: string) {
    this.client = new Anthropic({ apiKey: apiKey ?? process.env.ANTHROPIC_API_KEY });
  }

  /**
   * Round 1: generate an initial proposal from a ProblemSpec.
   * Returns the opaque JSON payload matching the spec's answerSchema.
   */
  async generateInitial(spec: ProblemSpec): Promise<unknown> {
    const style = spec.stylePrompt ? `\n\nStyle guidance: ${spec.stylePrompt}` : "";

    const userPrompt =
      `## Problem\n\n${spec.problemDescription}\n\n` +
      `${spec.contextJson}\n\n` +
      `## What to do\n\n${spec.hint}` +
      `\n\nOutput your proposal as a single JSON code block.${style}`;

    return this.callAndParse(userPrompt, spec);
  }

  /**
   * Rounds 2+: refine a previous proposal given feedback text.
   * feedbackText is verifier-formatted (not hardcoded).
   */
  async refineWithFeedback(
    spec: ProblemSpec,
    feedbackText: string,
    prevPayload: unknown,
    round: number,
  ): Promise<unknown> {
    const style = spec.stylePrompt ? `\nStyle guidance: ${spec.stylePrompt}` : "";
    const prevName = (prevPayload as Record<string, unknown>)?.name ?? "previous";
    const userPrompt =
      `Round ${round}: Your previous proposal "${prevName}" ` +
      `failed verification.\n\n` +
      `Previous candidate:\n\`\`\`json\n${JSON.stringify(prevPayload, null, 2)}\n\`\`\`\n\n` +
      feedbackText +
      `\nPlease provide a corrected answer that fixes ALL of the above errors. ` +
      `Respond with the corrected JSON object only — no prose.${style}`;

    return this.callAndParse(userPrompt, spec);
  }

  /**
   * Post-solve reflection: ask the LLM what would have made the problem clearer.
   */
  async reflectOnSolve(
    spec: ProblemSpec,
    rounds: number,
    history: HistoryEntry[],
  ): Promise<string> {
    const historyStr = history.map((h) => {
      const status = h.result.verified ? "✓ Success" : h.result.verificationStatus;
      const payload = h.payload as Record<string, unknown>;
      return `Round ${h.round}: "${payload?.name ?? "?"}" → ${status}`;
    }).join("\n");

    const prompt =
      `You just solved a problem: ${spec.problemDescription.split("\n")[0]}\n` +
      `It took ${rounds} round(s). Here's the history:\n\n${historyStr}\n\n` +
      `Now reflect on the experience. Answer these questions concisely:\n\n` +
      `1. **What was confusing about the problem description or system prompt?**\n` +
      `2. **What information was missing?**\n` +
      `3. **How useful were the structured diffs?**\n` +
      `4. **What specific changes to the system prompt would help future solvers?**\n` +
      `5. **What "dictionary" or "recipe" did you discover?**`;

    const response = await this.client.messages.create({
      model: "claude-sonnet-4-6",
      max_tokens: 4096,
      system: "You are reflecting on your experience solving a mathematical problem. Be specific and actionable.",
      messages: [{ role: "user", content: prompt }],
    });

    return response.content
      .filter((b): b is Anthropic.TextBlock => b.type === "text")
      .map((b) => b.text)
      .join("");
  }

  /**
   * Core: call Claude with tool_choice forced to the answer tool.
   * The tool schema comes from the ProblemSpec (verifier-defined).
   */
  private async callAndParse(userPrompt: string, spec: ProblemSpec): Promise<unknown> {
    const toolName = spec.answerToolName ?? "propose_theory";
    const toolDescription = spec.answerToolDescription ??
      "Submit a candidate Theory for verification by the CAS. " +
      "The CAS will apply the forward operator and diff the result against the target.";
    const schema = spec.answerSchema ?? DEFAULT_ANSWER_SCHEMA;

    const tool: Anthropic.Tool = {
      name: toolName,
      description: toolDescription,
      input_schema: schema as Anthropic.Tool.InputSchema,
    };

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const stream = this.client.messages.stream({
      model: "claude-sonnet-4-6",
      max_tokens: 4096,
      thinking: { type: "disabled" },
      tools: [tool],
      tool_choice: { type: "tool", name: toolName },
      system: [
        {
          type: "text",
          text: SYSTEM_PROMPT,
          cache_control: { type: "ephemeral" },
        },
      ],
      messages: [{ role: "user", content: userPrompt }],
    } as any);

    const message = await stream.finalMessage();
    console.error(`[llm] stop_reason=${message.stop_reason} usage=${JSON.stringify(message.usage)}`);

    const toolUse = message.content.find(
      (b): b is Anthropic.ToolUseBlock => b.type === "tool_use",
    );

    if (toolUse) {
      const parsed = toolUse.input as unknown;
      const keys = Object.keys(parsed as Record<string, unknown>);
      console.error(`[llm] tool input keys: ${keys.join(", ")}`);
      console.error(`[llm] preview: ${JSON.stringify(parsed).slice(0, 400)}`);
      return parsed;
    }

    const textBlocks = message.content
      .filter((b): b is Anthropic.TextBlock => b.type === "text")
      .map((b) => b.text)
      .join("");
    const types = message.content.map((b) => b.type).join(", ");
    throw new Error(
      `LLM did not output a valid answer.\n` +
      `Response had no tool_use block (got: ${types}).\n` +
      `Response preview: ${textBlocks.slice(0, 300)}`,
    );
  }
}

// ── Default diff formatter (used when verifier doesn't provide formatFeedback) ─

export function formatStructuralDiff(result: VerificationResult): string {
  const lines: string[] = [];

  // Generic feedback strings (from any problem type)
  if (result.feedbackStrings && result.feedbackStrings.length > 0) {
    lines.push("### CAS Feedback\n");
    for (const fb of result.feedbackStrings) {
      lines.push(`  • ${fb}`);
    }
    lines.push("");
  }

  // Distance signal
  if (result.distance !== undefined) {
    lines.push(`### Distance Score: ${result.distance} (0 = perfect match)\n`);
  }

  if (result.verificationStatus.startsWith("⏱")) {
    lines.push(
      "⚠️  TIMEOUT WARNING: The proof engine could not converge within its " +
        "depth limit. Your axioms may form circular rewriting patterns (e.g. " +
        "A → B and B → A). Simplify your axioms or break them into smaller " +
        "non-circular steps.\n",
    );
  }

  if (result.missingSignatures.length > 0) {
    lines.push("### Missing Morphisms (structural shapes, not names)");
    lines.push(
      "The CAS identifies morphisms by their structural type (§0 = first object, §1 = second, etc.).",
    );
    lines.push("Your theory is missing the following required morphism types:\n");
    for (const sig of result.missingSignatures) {
      lines.push(
        `  • Required: ${sig.domainShape} → ${sig.codomainShape}` +
          `  (originally named '${sig.sourceName}' in the target)`,
      );
    }
    lines.push(
      "\n💡 STRATEGY: Add new generators to your `morphisms` array that exactly match " +
      "these domain/codomain shapes. Do not guess names; use the structural shapes above.",
    );
    lines.push("");
  }

  if (result.unmappedObjects.length > 0) {
    lines.push("### Spurious Objects (hallucinated generators)");
    lines.push(
      "Your theory has MORE objects than the target requires. " +
        "The following objects have no structural counterpart in the target:\n",
    );
    for (const obj of result.unmappedObjects) {
      lines.push(`  • '${obj}' — remove this object or merge it with an existing one`);
    }
    lines.push(
      "\n💡 STRATEGY: Remove these extra objects entirely. The target has a fixed number " +
      "of objects — your theory must have exactly that many, no more.",
    );
    lines.push("");
  }

  if (result.axiomViolations.length > 0) {
    lines.push("### Axiom Violations");
    lines.push(
      "The following axioms are required by the target but do not hold (or could not be verified) in your theory:\n",
    );
    for (const v of result.axiomViolations) {
      const isTimeout = v.status.startsWith("⏱");
      const verdict = isTimeout ? "TIMEOUT (may be correct but unprovable)" : "FAILED";
      lines.push(`  • Axiom '${v.sourceAxiom}': ${verdict}`);
      if (!isTimeout) {
        lines.push(`    LHS reduced to: ${v.lhsReduced}`);
        lines.push(`    RHS reduced to: ${v.rhsReduced}`);
        lines.push(`    → These must reduce to the SAME normal form`);
        lines.push(
          `    💡 STRATEGY: You are missing an intermediate axiom. Add a new axiom ` +
          `that explicitly rewrites '${v.lhsReduced}' into '${v.rhsReduced}'.`,
        );
      } else {
        lines.push(
          `    💡 STRATEGY: Timeout means your axioms may form circular rewriting loops. ` +
          `Rewrite this axiom so LHS is strictly more complex than RHS (left-to-right reduction).`,
        );
      }
    }
    lines.push("");
  }

  if (lines.length === 0) {
    lines.push("No specific errors reported (unknown failure). Try restructuring the theory.");
  }

  return lines.join("\n");
}

/** Minimal structural validation for TheoryJson payloads. */
export function validateTheoryPayload(obj: unknown): void {
  if (typeof obj !== "object" || obj === null) {
    throw new Error("Response is not a JSON object");
  }
  const t = obj as Record<string, unknown>;
  const keys = Object.keys(t);
  if (typeof t.name !== "string") throw new Error(`Missing 'name' field (keys: ${keys.join(", ")})`);
  if (!Array.isArray(t.objects)) throw new Error(`Missing 'objects' array (keys: ${keys.join(", ")})`);
  if (!Array.isArray(t.morphisms)) throw new Error(`Missing 'morphisms' array (keys: ${keys.join(", ")})`);
  if (!Array.isArray(t.axioms)) {
    if (typeof t.name === "string" && Array.isArray(t.objects) && Array.isArray(t.morphisms)) {
      (t as Record<string, unknown>).axioms = [];
      return;
    }
    throw new Error(`Missing 'axioms' array (keys: ${keys.join(", ")})`);
  }
}
