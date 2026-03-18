/**
 * LLMClient — Anthropic API wrapper for theory candidate generation.
 *
 * Drives the proposal side of the LLM ↔ CAS inverse problem loop.
 * Given a target theory, a forward operator, and (on rounds > 1) a structured
 * VerificationResult diff from the CAS, it asks Claude to propose or revise
 * a candidate Theory JSON.
 *
 * Design decisions:
 *   - Claude Opus 4.6 with adaptive thinking: the mathematical reasoning
 *     required for categorification is exactly what extended thinking is for.
 *   - Streaming with finalMessage(): prevents HTTP timeouts on long outputs.
 *   - JSON is extracted from a ```json ... ``` code block in the response,
 *     not via structured outputs, because Expr is a recursive type that's
 *     difficult to express as a static JSON Schema.
 *   - The system prompt is cached (cache_control: ephemeral) since it's
 *     identical across all rounds.
 */

import Anthropic from "@anthropic-ai/sdk";
import type { TheoryJson, VerificationResult } from "./types";

// ── System prompt (sent once, cached) ────────────────────────────────────────

const SYSTEM_PROMPT = `You are a mathematical problem solver working with a rigorous Computer Algebra System (CAS) for categorical theories.

Your task is to propose candidate theories in JSON format. The CAS will verify each proposal by applying a forward operator to your candidate and checking whether the result is **structurally equivalent** (≅) to a target theory.

**What "≅" means here:** The CAS checks structural equivalence — same number of objects, morphisms with matching domain/codomain shapes (position-normalized, ignoring names), and axioms that reduce to the same normal forms under rewriting. Generator names do NOT matter; only structural shapes do. §0 = first object, §1 = second, etc.

You will receive structured diffs describing exactly what is wrong with your previous proposal.

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

1. Submit your proposal by calling the propose_theory tool. Do not output text —
   your entire response should be the tool call with the theory as its argument.
2. List objects in the ORDER they appear in the target theory. The CAS uses positional
   matching — wrong order causes false structural failures even if the names are right.
3. Keep the candidate as simple as possible. The CAS verifies by forward-applying an
   operator to your candidate, not by inspecting it directly.
4. Axiom LHS and RHS must be Exprs built from the theory's own morphism and object atoms.
5. When fixing a diff, address EVERY missingSignature and axiomViolation listed.
6. The "reasoning" field in the tool schema is for your mathematical scratchpad — use it.
7. DO NOT redefine doctrine-native structures as custom generators. If your doctrine is
   \`MonoidalCategory\`, do NOT add a \`tensor\` or \`unit\` morphism to the \`morphisms\` array.
   Use the built-in \`{"tensor": [...]}\` and \`"unit"\` Exprs directly in domains/codomains.
   Generators are strictly for custom algebraic/topological data beyond what the doctrine provides.
8. ORIENT YOUR AXIOMS to prevent infinite rewriting loops (Timeouts). Write axioms as
   left-to-right reduction rules (Complex → Simple). Avoid symmetric axioms like
   \`f ∘ g = g ∘ f\` — if commutativity is needed, break it into intermediate steps
   or use a canonical ordering.`;

// ── Inverse problem descriptions ─────────────────────────────────────────────

/**
 * Translate a forwardOp into a human-readable description of what the LLM
 * needs to find.  This is the key to making the prompts operator-agnostic:
 * the *same* code path generates correct prompts for categorification,
 * Stone duality, opposite functors, and any other CAS operator.
 */
function describeInverseProblem(
  forwardOp: string,
  targetName: string,
): { problem: string; hint: string } {
  switch (forwardOp) {

    case "decategorify_iso":
      return {
        problem:
          `Find a theory C such that **decategorify(C, isoClasses) ≅ "${targetName}"**.\n\n` +
          `**What \`decategorify_iso\` does:** Collapses a higher theory down one categorical level:\n` +
          `  • Objects of C       → generators of the target\n` +
          `  • Isomorphism classes of morphisms → equations of the target\n` +
          `  • 2-cells / axioms   → discarded (lost in decategorification)\n\n` +
          `**Worked example:** decategorify_iso(FinSet) ≅ CommutativeMonoid\n` +
          `  • FinSet objects (finite sets) → generators of CommutativeMonoid\n` +
          `  • Bijections between sets → equations (|A×B| = |A|·|B|, |A⊔B| = |A|+|B|)`,
        hint:
          `**The Categorification Dictionary (apply mechanically):**\n` +
          `1. Each target **object** → Create an **Object** in your theory.\n` +
          `2. Each target **morphism** f: A → B → Create a **Morphism** between corresponding objects.\n` +
          `3. Each target **axiom** (LHS = RHS) → Create **TWO Morphisms** (f: LHS → RHS, g: RHS → LHS) ` +
          `and **TWO Axioms** making them an isomorphism (f ∘ g = id, g ∘ f = id).\n\n` +
          `Apply this dictionary to every generator, morphism, and equation in the target.`,
      };

    case "decategorify_K0":
      return {
        problem:
          `Find a theory C such that **decategorify(C, grothendieckGroup) ≅ "${targetName}"**.\n\n` +
          `**What \`decategorify_K0\` does:** Computes the Grothendieck group K₀:\n` +
          `  • Objects of C      → formal generators [X] in K₀\n` +
          `  • Short exact sequences 0→A→B→C→0 → relations [B] = [A] + [C]\n` +
          `  • Morphisms         → group homomorphisms\n\n` +
          `**Worked example:** decategorify_K0(VectorBundles) ≅ K-Theory\n` +
          `  • Vector bundles E → generators [E]\n` +
          `  • Direct sum E⊕F → addition [E]+[F]`,
        hint:
          `**Recipe for K₀ categorification:**\n` +
          `1. Each target generator → an Object (representing an isomorphism class).\n` +
          `2. Target addition → direct sum / coproduct in your theory.\n` +
          `3. Target relations → short exact sequences as axioms.\n` +
          `Think of this as lifting an abelian group to a category of modules or bundles.`,
      };

    case "decategorify_chi":
      return {
        problem:
          `Find a theory C such that **decategorify(C, eulerCharacteristic) ≅ "${targetName}"**.\n\n` +
          `**What \`decategorify_chi\` does:** Computes the Euler characteristic:\n` +
          `  • Collapses all objects into a single alternating sum\n` +
          `  • Result has exactly one object and one morphism (the characteristic)\n\n` +
          `**Worked example:** decategorify_chi(ChainComplex) ≅ Z\n` +
          `  • Chain complex C_0 → C_1 → C_2 → ... collapses to χ = Σ(-1)^n rank(C_n)`,
        hint:
          `**Recipe for Euler characteristic categorification:**\n` +
          `1. Create a **graded** theory with objects for each degree.\n` +
          `2. Add differential morphisms d: C_n → C_{n-1} with d∘d = 0.\n` +
          `3. The alternating sum of ranks must produce the target.`,
      };

    case "mirror":
      return {
        problem:
          `Find a theory C such that **mirror(C) ≅ "${targetName}"**.\n\n` +
          `**What \`mirror\` does:** Stone duality — it swaps categorical duals:\n` +
          `  • \`{"prod": [A, B]}\` ↔ \`{"coprod": [A, B]}\`\n` +
          `  • \`"terminal"\` ↔ \`"initial"\`\n` +
          `  • Limits ↔ Colimits\n` +
          `  • Morphism directions are preserved (unlike \`opposite\`).\n\n` +
          `**Worked example:** mirror(BooleanAlgebra) ≈ BooleanAlgebra (self-dual)\n` +
          `  • ∧ (meet, prod) becomes ∨ (join, coprod) and vice versa\n` +
          `  • ⊤ (terminal) becomes ⊥ (initial) and vice versa`,
        hint:
          `**Recipe for \`mirror\`:** Since mirror is an involution, C = mirror(target).\n` +
          `1. Keep the SAME objects and morphism directions.\n` +
          `2. Replace every \`{"prod": [...]}\` with \`{"coprod": [...]}\` and vice versa.\n` +
          `3. Replace \`"terminal"\` with \`"initial"\` and vice versa.\n` +
          `4. Replace \`"unit"\` with the dual unit if applicable.\n` +
          `Apply this substitution to all morphism domains, codomains, and axiom expressions.`,
      };

    case "opposite":
      return {
        problem:
          `Find a theory C such that **opposite(C) ≅ "${targetName}"**.\n\n` +
          `**What \`opposite\` does:** It reverses all morphism directions. Every morphism ` +
          `f: A → B in C becomes f^op: B → A in C^op. Composition order reverses: ` +
          `if C has \`comp([f, g])\`, then C^op has \`comp([g, f])\`.\n\n` +
          `**Worked example:** opposite(Monoid) = CoMonoid\n` +
          `  • Monoid has μ: M×M → M (multiplication) and η: 1 → M (unit)\n` +
          `  • CoMonoid has δ: M → M×M (comultiplication) and ε: M → 1 (counit)\n` +
          `  • Axioms reverse composition order: assoc becomes coassoc, unit laws become counit laws`,
        hint:
          `**Recipe for \`opposite\`:** Since opposite is an involution, C = opposite(target).\n` +
          `1. Keep the SAME objects.\n` +
          `2. For each morphism f: A → B in the target, create f: B → A in your candidate (swap domain/codomain).\n` +
          `3. For each axiom, reverse the order inside every \`comp([...])\` (swap the array elements).\n` +
          `4. Non-comp expressions (prod, tensor, id, atom) stay the same.\n` +
          `Apply this mechanically to every morphism and axiom.`,
      };

    case "identity":
      return {
        problem:
          `Find a theory C such that **C ≅ "${targetName}"** (direct structural match).\n\n` +
          `**What \`identity\` does:** Nothing — no transformation is applied. Your candidate ` +
          `must be structurally equivalent to the target as-is.\n\n` +
          `**Worked example:** identity(Monoid) = Monoid\n` +
          `  • Same objects, same morphism shapes, same axiom normal forms\n` +
          `  • Names can differ: your "mul" matches target's "μ" if the shapes match`,
        hint:
          `**Recipe for \`identity\`:** Copy the target structure exactly.\n` +
          `1. Same number of objects, in the same order.\n` +
          `2. Same number of morphisms, with matching domain/codomain shapes.\n` +
          `3. Same axioms (LHS and RHS must reduce to the same normal forms).\n` +
          `You may rename generators freely — the CAS uses positional/shape matching, not name matching.`,
      };

    default:
      // Unknown operator: give a general description without misleading the LLM
      return {
        problem:
          `Find a theory C such that **${forwardOp}(C) ≅ "${targetName}"**.\n\n` +
          `The CAS will apply the "${forwardOp}" operator to your candidate and check ` +
          `structural equivalence with the target. Structural equivalence means: same ` +
          `number of objects, morphisms with matching domain/codomain shapes, and axioms ` +
          `that reduce to the same normal forms.`,
        hint:
          `**General strategy:**\n` +
          `1. Study the target structure (objects, morphism shapes, axiom patterns).\n` +
          `2. Reason about what pre-image under "${forwardOp}" would produce this structure.\n` +
          `3. Start simple — propose the minimal theory that could work.\n` +
          `4. Use the diff feedback to iteratively fix mismatches.`,
      };
  }
}

// ── LLMClient ─────────────────────────────────────────────────────────────────

export class LLMClient {
  private client: Anthropic;

  constructor(apiKey?: string) {
    this.client = new Anthropic({ apiKey: apiKey ?? process.env.ANTHROPIC_API_KEY });
  }

  /**
   * Round 1: generate an initial proposal.
   *
   * @param targetName     Name of the target theory (e.g. "Monoid")
   * @param targetJson     The target theory JSON (shown to the LLM for structure)
   * @param forwardOp      Which CAS operator will be applied to the candidate
   * @param stylePrompt    Optional style hint (e.g. "prefer cobordisms")
   */
  async generateInitial(
    targetName: string,
    targetJson: string,
    forwardOp: string,
    stylePrompt?: string,
  ): Promise<TheoryJson> {
    const { problem, hint } = describeInverseProblem(forwardOp, targetName);
    const style = stylePrompt ? `\n\nStyle guidance: ${stylePrompt}` : "";

    const userPrompt =
      `## Inverse Problem\n\n${problem}\n\n` +
      `## Target Theory: "${targetName}"\n\n` +
      `\`\`\`json\n${targetJson}\n\`\`\`\n\n` +
      `## What to do\n\n${hint}` +
      `\n\nOutput your proposal as a single JSON code block.${style}`;

    return this.callAndParse(userPrompt);
  }

  /**
   * Rounds 2+: refine a previous proposal given the CAS diff.
   *
   * @param targetName    Name of the target theory
   * @param diff          The VerificationResult from the previous round
   * @param prevCandidate The theory the LLM proposed last round
   * @param forwardOp     The CAS operator being applied
   * @param round         Current round number (for logging)
   */
  async refineWithDiff(
    targetName: string,
    diff: VerificationResult,
    prevCandidate: TheoryJson,
    forwardOp: string,
    round: number,
  ): Promise<TheoryJson> {
    const userPrompt =
      `Round ${round}: Your previous proposal "${prevCandidate.name}" ` +
      `failed verification against target "${targetName}".\n\n` +
      `Previous candidate:\n\`\`\`json\n${JSON.stringify(prevCandidate, null, 2)}\n\`\`\`\n\n` +
      formatDiff(diff) +
      `\nPlease provide a corrected Theory JSON that fixes ALL of the above errors. ` +
      `Respond with the corrected JSON object only — no prose.`;

    return this.callAndParse(userPrompt);
  }

  /**
   * Post-solve reflection: ask the same conversation chain what would have
   * made the problem clearer. Returns free-text suggestions for improving
   * the system prompt, diff format, and problem descriptions.
   */
  async reflectOnSolve(
    targetName: string,
    forwardOp: string,
    rounds: number,
    history: Array<{ round: number; candidate: TheoryJson; result: VerificationResult }>,
  ): Promise<string> {
    const historyStr = history.map((h) => {
      const status = h.result.verified ? "✓ Success" : h.result.verificationStatus;
      return `Round ${h.round}: "${h.candidate.name}" (${h.candidate.objects.length} obj / ` +
        `${h.candidate.morphisms.length} mor / ${h.candidate.axioms.length} ax) → ${status}`;
    }).join("\n");

    const prompt =
      `You just solved an inverse problem: find X such that ${forwardOp}(X) ≅ "${targetName}".\n` +
      `It took ${rounds} round(s). Here's the history:\n\n${historyStr}\n\n` +
      `Now reflect on the experience. Answer these questions concisely:\n\n` +
      `1. **What was confusing about the problem description or system prompt?** ` +
      `What phrasing led you astray, if anything?\n` +
      `2. **What information was missing?** What facts about the forward operator, ` +
      `the target theory, or the CAS would have helped you solve it in fewer rounds?\n` +
      `3. **How useful were the structured diffs?** Did the missing-signature shapes, ` +
      `axiom violation details, and fix strategies help you converge?\n` +
      `4. **What specific changes to the system prompt would help future solvers?** ` +
      `Suggest concrete wording changes or new rules.\n` +
      `5. **What "dictionary" or "recipe" did you discover** for this operator? ` +
      `(e.g., "for opposite: reverse all morphism domains and codomains")`;

    const response = await this.client.messages.create({
      model: "claude-sonnet-4-6",
      max_tokens: 4096,
      system: "You are reflecting on your experience solving a mathematical inverse problem. Be specific and actionable.",
      messages: [{ role: "user", content: prompt }],
    });

    return response.content
      .filter((b): b is Anthropic.TextBlock => b.type === "text")
      .map((b) => b.text)
      .join("");
  }

  /**
   * Core: call Claude with tool_choice forced to "propose_theory".
   *
   * Why tool_use instead of output_config / code block extraction:
   *   - output_config json_object: doesn't exist in the API (only json_schema)
   *   - output_config json_schema: doesn't support recursive types (ExprJson is recursive)
   *   - Code block extraction: with adaptive thinking, Claude may return only a
   *     thinking block and empty text — extracting from text is unreliable
   *
   * tool_choice: {type:"tool", name:"propose_theory"} forces Claude to emit a
   * ToolUseBlock whose `input` is pre-parsed JSON. No text parsing needed, no
   * recursion schema constraints, and thinking blocks coexist happily.
   *
   * The tool schema uses `type: "object"` with loose item types for the arrays
   * (no `additionalProperties: false` on inner objects) so ExprJson can be
   * nested arbitrarily without schema violations.
   */
  private async callAndParse(userPrompt: string): Promise<TheoryJson> {
    const proposeTool: Anthropic.Tool = {
      name: "propose_theory",
      description:
        "Submit a candidate Theory for verification by the CAS. " +
        "The CAS will apply the forward operator and diff the result against the target.",
      input_schema: {
        type: "object",
        properties: {
          reasoning: {
            type: "string",
            description: "Your mathematical reasoning and approach (scratchpad — ignored by CAS)",
          },
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
      },
    };

    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const stream = this.client.messages.stream({
      model: "claude-sonnet-4-6",
      max_tokens: 16384,
      thinking: { type: "disabled" },
      tools: [proposeTool],
      tool_choice: { type: "tool", name: "propose_theory" },
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
      validateTheoryShape(parsed);
      return parsed as TheoryJson;
    }

    // Fallback: Claude responded with text instead of calling the tool.
    // Log the prose (ignore it for parsing) and throw so the retry loop can try again.
    const textBlocks = message.content
      .filter((b): b is Anthropic.TextBlock => b.type === "text")
      .map((b) => b.text)
      .join("");
    const types = message.content.map((b) => b.type).join(", ");
    throw new Error(
      `LLM did not output a valid Theory JSON.\n` +
      `Response had no tool_use block (got: ${types}).\n` +
      `Response preview: ${textBlocks.slice(0, 300)}`,
    );
  }
}

// ── Diff formatter ────────────────────────────────────────────────────────────

/**
 * Translate a VerificationResult into a structured, actionable LLM prompt.
 * This is where the CAS's rigid structural graph becomes semantic feedback.
 * The LLM doesn't receive "missingSignatures[0]" — it receives
 * "Target requires a morphism §0 → §1 ⊗ §0 (originally named 'η')".
 */
export function formatDiff(result: VerificationResult): string {
  const lines: string[] = [];

  // ── Timeout warning ──────────────────────────────────────────────────────
  if (result.verificationStatus.startsWith("⏱")) {
    lines.push(
      "⚠️  TIMEOUT WARNING: The proof engine could not converge within its " +
        "depth limit. Your axioms may form circular rewriting patterns (e.g. " +
        "A → B and B → A). Simplify your axioms or break them into smaller " +
        "non-circular steps.\n",
    );
  }

  // ── Missing morphism signatures ──────────────────────────────────────────
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

  // ── Unmapped / spurious objects ──────────────────────────────────────────
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

  // ── Axiom violations ─────────────────────────────────────────────────────
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


/** Minimal structural validation — catch obvious errors before sending to Lean.
 *  Logs the actual keys so we can debug schema mismatches. */
function validateTheoryShape(obj: unknown): void {
  if (typeof obj !== "object" || obj === null) {
    throw new Error("Response is not a JSON object");
  }
  const t = obj as Record<string, unknown>;
  const keys = Object.keys(t);
  console.error(`[llm] tool input keys: [${keys.join(", ")}]`);
  if (typeof t.name !== "string") throw new Error(`Missing 'name' field (keys: ${keys.join(", ")})`);
  if (!Array.isArray(t.objects)) throw new Error(`Missing 'objects' array (keys: ${keys.join(", ")})`);
  if (!Array.isArray(t.morphisms)) throw new Error(`Missing 'morphisms' array (keys: ${keys.join(", ")})`);
  if (!Array.isArray(t.axioms)) {
    // Default axioms to empty if everything else is present — the CAS handles missing axioms gracefully
    if (typeof t.name === "string" && Array.isArray(t.objects) && Array.isArray(t.morphisms)) {
      (t as Record<string, unknown>).axioms = [];
      return;
    }
    throw new Error(`Missing 'axioms' array (keys: ${keys.join(", ")})`);
  }
}
