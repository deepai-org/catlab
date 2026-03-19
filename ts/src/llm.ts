/**
 * LLMClient — Anthropic API wrapper for candidate generation.
 *
 * Drives the proposal side of the LLM ↔ CAS feedback loop.
 * The LLM client is fully generic: it uses the ProblemSpec's answerSchema
 * to dynamically build the tool the LLM calls, and uses verifier-provided
 * feedback text (not hardcoded diff formatting) to refine proposals.
 *
 * Design decisions:
 *   - Claude Sonnet 4.6 with adaptive thinking + forced tool_choice.
 *   - Conversation history preserved across rounds (thinking blocks included).
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

## CAS Normalization Behavior (CRITICAL)

The CAS checks axioms by **normalizing both sides using all axioms as rewrite rules, then comparing normal forms**. This has several important consequences:

1. **Axioms cannot be omitted even if logically derivable.** The CAS uses term-rewriting, not full equational reasoning. Every target axiom must hold as a rewriting identity.
2. **Compositions may collapse.** \`comp([f, f])\` may simplify to \`f\` if axioms allow it. The normal form shown in error messages is ground truth — write your axiom to produce exactly that equation.
3. **Same-shaped morphisms are position-normalized — in YOUR axioms too.** When two morphisms share the same domain/codomain type (e.g. \`mul: R×R→R\` and \`add: R×R→R\`), the CAS normalizes the later one to the earlier one EVERYWHERE — in target axioms AND in your own candidate axioms. If you define \`mul\` after \`add\` with the same type, all uses of \`mul\` in your axioms are silently rewritten to \`add\` before verification. Write axioms using the canonical (earlier) morphism name. This means you cannot add a morphism as a "placeholder" for another structure if it has the same type as an existing one — it will vanish.
4. **Commutativity cascades.** Adding \`f = swap ∘ f\` causes the normalizer to rewrite \`f\` throughout all axioms. Downstream axioms referencing \`f\` inside \`prod(...)\` expressions will have their normal forms changed. You must restate those axioms using the post-normalization shapes.
5. **When the CAS diff says "LHS reduced to X, RHS reduced to Y" — take X and Y literally as the axiom you need.** Don't try to mechanically derive them from the target theory's axiom text. The error message IS the axiom; encode it directly.
6. **Axiom minimization is usually impossible.** The CAS cannot perform multi-step equational derivations with substitution into contexts (the Word Problem). An axiom like \`right_unit\` cannot be derived from \`assoc + left_unit + left_inv\` even though this is a standard theorem — the CAS lacks the equational closure to prove it. If removing an axiom causes a verification failure, add it back. The only reliable way to reduce generator count is eliminating morphisms (expressing one as a composition of others) or objects.

## Structural Equivalence (\`≅\`) Semantics

The CAS checks if the target's morphisms are **embeddable** into your theory via positional shape-matching, not strict count equality. A theory with MORE morphisms/axioms than the target can still match — extra generators are ignored if they don't affect the target substructure. This means:
- For multi-constraint problems, your candidate may need the **union** of all structural requirements
- A 5-morphism theory can satisfy \`f(X) ≅ Group\` (3 morphisms) if the first 3 positions match

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
| \`tensor\` | Tensor product of Lawvere theories. X-morphisms become \`f⊗id_Y\`, Y-morphisms become \`id_X⊗g\`. Cross-distributivity axioms are NOT auto-generated — they must appear explicitly in one factor. Normal forms in error messages are in the post-tensor theory; substitute \`f⊗id → f\` to find the pre-tensor axiom needed. **Warning:** If X has morphisms f and g with identical domain/codomain types, g is position-normalized to f — you cannot use g as a "placeholder" for Y's structure in cross-axioms. Write cross-axioms using only X's canonical morphisms (e.g. \`(id×add)∘add = (add×add)∘add\`). |
| \`pullback\` | Fibered product of two theories over a shared base. \`X ×_B Y\` has all generators/axioms from both X and Y with shared base identified. |
| \`drop_inverses\` | Removes inverse morphisms from a theory. If the theory has no categorical inverses, this is a no-op (identity). |

## How Operators Transform Axiom Expressions

| Operator | \`comp([e1, e2])\` | \`prod([e1, e2])\` | morphism \`f: A→B\` | \`id(A)\` |
|----------|-------------------|-------------------|---------------------|----------|
| \`opposite\` | \`comp([opp(e2), opp(e1)])\` (reversed) | preserved, components flipped | becomes \`f': B→A\` | preserved |
| \`mirror\` | preserved | becomes \`coprod([...]) \` | preserved direction | preserved |
| \`tensor(X,Y)\` | preserved per-factor | \`prod\` lifted into tensor product | X's \`f\` → \`f⊗id_Y\`, Y's \`g\` → \`id_X⊗g\` | \`id(A⊗B)\` |
| \`identity\` | preserved | preserved | preserved | preserved |

Key insight for \`opposite\`: endomorphisms (\`f: A→A\`) are self-dual. \`comp([f, f])\` under opposite is \`comp([f, f])\` — symmetric lists are preserved.

### Worked Example: \`opposite\` Applied to Monoid → CoMonoid

**Input (Monoid):**
- \`μ: M×M → M\` (multiplication), \`η: 1 → M\` (unit)
- Axiom \`assoc\`: \`comp([prod([μ, id(M)]), μ]) = comp([prod([id(M), μ]), μ])\`

**Output (\`opposite(Monoid)\` = CoMonoid):**
- \`δ: M → M×M\` (comultiplication — μ flipped), \`ε: M → 1\` (counit — η flipped)
- Axiom \`coassoc\`: \`comp([δ, prod([δ, id(M)])]) = comp([δ, prod([id(M), δ])])\`

**How it transforms:** Each \`comp([e1, e2])\` becomes \`comp([opp(e2), opp(e1)])\`. Each morphism \`f: A→B\` becomes \`f': B→A\`. Apply recursively into \`prod\` arguments: \`prod([opp(e1), opp(e2)])\`.

**To find X such that \`opposite(X) ≅ Target\`:** Take each target axiom, replace morphisms with their domain/codomain-flipped versions, and reverse every \`comp\` list (applying recursively into \`prod\`).

**Note:** \`terminal\` and \`initial\` are preserved (NOT swapped) under \`opposite\`. So \`η: terminal → M\` dualizes to \`ε: M → terminal\` (not \`initial\`).

## Property Glossary

| Property | Meaning |
|----------|---------|
| \`commutative\` | The primary binary operation satisfies \`f = swap ∘ f\`. When added as a quotient axiom, this causes normalization cascades on all axioms referencing that operation. |
| \`additive_only\` | Keep only the additive structure (add, zero, neg, swap) and their axioms. Drop all multiplicative morphisms. |
| \`drop_inverses\` | Remove inverse morphisms. If the theory has no inverses, this is a no-op. |
| \`has_inverses\` | The theory must include inverse elements for its primary operation. |
| \`idempotent\` | The primary operation satisfies \`f ∘ f = f\`. |
| \`minimize generators\` | Find a structurally equivalent theory with the fewest total morphism generators. |

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
7. QUOTIENT PROBLEMS: Adding a commutativity axiom (\`f = swap ∘ f\`) may require
   rewriting OTHER axioms that reference \`f\`. The CAS normalizes all axioms together,
   so adding commutativity can invalidate distributivity or other cross-operation axioms.
   Re-derive those axioms using the post-normalization shapes the CAS reports.
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
  /** Accumulated conversation history across rounds (includes thinking blocks). */
  private messages: Anthropic.MessageParam[] = [];
  private tool: Anthropic.Tool | undefined;
  private toolName: string = "propose_theory";
  /** Pending tool_use_id from the last assistant response (needs a tool_result). */
  private pendingToolUseId: string | undefined;

  constructor(apiKey?: string) {
    this.client = new Anthropic({ apiKey: apiKey ?? process.env.ANTHROPIC_API_KEY });
  }

  /** Reset conversation state (called at start of each solve). */
  resetConversation(): void {
    this.messages = [];
    this.pendingToolUseId = undefined;
  }

  /**
   * Round 1: generate an initial proposal from a ProblemSpec.
   * Returns the opaque JSON payload matching the spec's answerSchema.
   */
  async generateInitial(spec: ProblemSpec): Promise<unknown> {
    // Reset conversation for a fresh solve
    this.resetConversation();

    const style = spec.stylePrompt ? `\n\nStyle guidance: ${spec.stylePrompt}` : "";

    const userPrompt =
      `## Problem\n\n${spec.problemDescription}\n\n` +
      `${spec.contextJson}\n\n` +
      `## What to do\n\n${spec.hint}` +
      `\n\nOutput your proposal as a single JSON code block.${style}`;

    // Set up the tool for this problem
    this.toolName = spec.answerToolName ?? "propose_theory";
    const toolDescription = spec.answerToolDescription ??
      "Submit a candidate Theory for verification by the CAS. " +
      "The CAS will apply the forward operator and diff the result against the target.";
    const schema = spec.answerSchema ?? DEFAULT_ANSWER_SCHEMA;

    this.tool = {
      name: this.toolName,
      description: toolDescription,
      input_schema: schema as Anthropic.Tool.InputSchema,
    };

    return this.callWithHistory(userPrompt);
  }

  /**
   * Rounds 2+: refine a previous proposal given feedback text.
   * The conversation history is preserved so thinking carries over.
   *
   * Combines the tool_result (for the prior tool_use) and the feedback
   * into a single user message to maintain proper turn alternation.
   */
  async refineWithFeedback(
    spec: ProblemSpec,
    feedbackText: string,
    prevPayload: unknown,
    round: number,
  ): Promise<unknown> {
    const style = spec.stylePrompt ? `\nStyle guidance: ${spec.stylePrompt}` : "";

    const feedbackText2 =
      `Round ${round}: Your previous proposal failed verification.\n\n` +
      feedbackText +
      `\nPlease provide a corrected answer that fixes ALL of the above errors. ` +
      `Think carefully about what went wrong and why before proposing.${style}`;

    // Combine tool_result + feedback into one user message (proper turn alternation)
    if (this.pendingToolUseId) {
      this.messages.push({
        role: "user",
        content: [
          {
            type: "tool_result",
            tool_use_id: this.pendingToolUseId,
            content: feedbackText,
          } as any,
          {
            type: "text",
            text: feedbackText2,
          },
        ],
      });
      this.pendingToolUseId = undefined;
    } else {
      // No pending tool_use (shouldn't happen, but handle gracefully)
      this.messages.push({ role: "user", content: feedbackText2 });
    }

    return this.callApi();
  }

  /**
   * Post-solve reflection: ask the LLM what would have made the problem clearer.
   * Uses the existing conversation history so it has full context.
   */
  async reflectOnSolve(
    spec: ProblemSpec,
    rounds: number,
    history: HistoryEntry[],
  ): Promise<string> {
    const prompt =
      `Now reflect on the experience of solving this problem. It took ${rounds} round(s).\n\n` +
      `Answer these questions concisely:\n\n` +
      `1. **What was confusing about the problem description or system prompt?**\n` +
      `2. **What information was missing?**\n` +
      `3. **How useful were the structured diffs?**\n` +
      `4. **What specific changes to the system prompt would help future solvers?**\n` +
      `5. **What "dictionary" or "recipe" did you discover?**`;

    // Close out any pending tool_result before adding the reflection prompt
    if (this.pendingToolUseId) {
      this.messages.push({
        role: "user",
        content: [
          {
            type: "tool_result",
            tool_use_id: this.pendingToolUseId,
            content: "Verification passed.",
          } as any,
          { type: "text", text: prompt },
        ],
      });
      this.pendingToolUseId = undefined;
    } else {
      this.messages.push({ role: "user", content: prompt });
    }

    // For reflection, don't force tool use — let it respond with text
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const stream = this.client.messages.stream({
      model: "claude-sonnet-4-6",
      max_tokens: 4096,
      thinking: { type: "enabled", budget_tokens: 1024 },
      system: [
        {
          type: "text",
          text: SYSTEM_PROMPT,
          cache_control: { type: "ephemeral" },
        },
      ],
      messages: this.messages,
    } as any);

    const message = await stream.finalMessage();

    // Append assistant response to history (preserving thinking blocks)
    this.messages.push({ role: "assistant", content: message.content as any });

    return message.content
      .filter((b): b is Anthropic.TextBlock => b.type === "text")
      .map((b) => b.text)
      .join("");
  }

  /**
   * Append a user message then call the API.
   * Used by generateInitial (round 1).
   */
  private async callWithHistory(userPrompt: string): Promise<unknown> {
    this.messages.push({ role: "user", content: userPrompt });
    return this.callApi();
  }

  /**
   * Core API call: sends the current conversation history to Claude,
   * appends the assistant response, and extracts the tool payload.
   *
   * Does NOT manage user messages — callers must push their own
   * user message before calling this method.
   *
   * If the assistant responds with a tool_use block, stores the
   * tool_use_id in pendingToolUseId so the next refineWithFeedback()
   * can include the tool_result in its user message.
   */
  private async callApi(): Promise<unknown> {
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    const stream = this.client.messages.stream({
      model: "claude-sonnet-4-6",
      max_tokens: 32000,
      thinking: { type: "enabled", budget_tokens: 10000 },
      tools: [this.tool!],
      tool_choice: { type: "auto" },
      system: [
        {
          type: "text",
          text: SYSTEM_PROMPT,
          cache_control: { type: "ephemeral" },
        },
      ],
      messages: this.messages,
    } as any);

    const message = await stream.finalMessage();
    const u = message.usage as unknown as Record<string, unknown>;
    console.error(
      `[llm] stop_reason=${message.stop_reason}` +
      ` in=${u.input_tokens} out=${u.output_tokens}` +
      ` cache_read=${u.cache_read_input_tokens ?? 0}` +
      ` cache_create=${u.cache_creation_input_tokens ?? 0}`,
    );

    // Append assistant response to history (includes thinking + tool_use blocks)
    this.messages.push({ role: "assistant", content: message.content as any });

    // Log thinking if present
    const thinkingBlocks = message.content.filter((b) => b.type === "thinking");
    if (thinkingBlocks.length > 0) {
      const thinkingText = thinkingBlocks
        .map((b) => (b as any).thinking ?? "")
        .join("\n");
      console.error(`[llm] thinking (${thinkingText.length} chars): ${thinkingText.slice(0, 300)}...`);
    }

    const toolUse = message.content.find(
      (b): b is Anthropic.ToolUseBlock => b.type === "tool_use",
    );

    if (toolUse) {
      const parsed = toolUse.input as unknown;
      const keys = Object.keys(parsed as Record<string, unknown>);
      console.error(`[llm] tool input keys: ${keys.join(", ")}`);
      console.error(`[llm] preview: ${JSON.stringify(parsed).slice(0, 400)}`);

      // Store the pending tool_use_id — refineWithFeedback will include
      // the tool_result in its combined user message.
      this.pendingToolUseId = toolUse.id;

      return parsed;
    }

    // Fallback: try to extract JSON from text response (happens with tool_choice: auto)
    const textBlocks = message.content
      .filter((b): b is Anthropic.TextBlock => b.type === "text")
      .map((b) => b.text)
      .join("");

    const jsonMatch = textBlocks.match(/```(?:json)?\s*([\s\S]*?)```/);
    if (jsonMatch) {
      try {
        const parsed = JSON.parse(jsonMatch[1].trim());
        console.error(`[llm] extracted JSON from text response (no tool_use block)`);
        return parsed;
      } catch {
        // Fall through to error
      }
    }

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
          `    💡 STRATEGY: The CAS has shown you the exact normal forms. Your theory needs ` +
          `the equation '${v.lhsReduced} = ${v.rhsReduced}' to hold after normalization. ` +
          `Take these normal forms LITERALLY — encode this equation directly as an axiom ` +
          `(or fix an existing one). Do not try to derive the "mathematically correct" form; ` +
          `the CAS normal form IS the ground truth. If morphisms with the same type signature ` +
          `appear collapsed (e.g. mul→add), this is position-normalization — use the canonical name.`,
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
