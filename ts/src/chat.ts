/**
 * ChatAgent — LLM-driven conversational interface to the CAS.
 *
 * The user types natural language. Claude interprets intent and calls CAS tools
 * (list theories, get summaries, apply operators, validate, solve inverse problems).
 * Results stream back as structured messages for the UI to render.
 *
 * This is NOT the solver loop — it's a conversational agent that can invoke
 * the solver as one of its tools.
 */

import Anthropic from "@anthropic-ai/sdk";
import type { CatlabClient } from "./client";
import type { TheoryJson, SolverResult, SolverProgressEvent } from "./types";
import { LLMClient } from "./llm";
import { GenericSolver } from "./solver";
import {
  InverseVerifier,
  PushoutComplementVerifier,
  ExtensionVerifier,
  MultiObjectiveVerifier,
  FixedPointVerifier,
  PullbackComplementVerifier,
  SimplificationVerifier,
  ModelFindingVerifier,
  SubobjectVerifier,
  SynthesisVerifier,
  QuotientVerifier,
  DecompositionVerifier,
  RelaxationVerifier,
  CatalystVerifier,
} from "./verifiers";
import * as api from "./api";

// ── Chat message types (sent to UI via SSE) ──────────────────────────────────

export interface ChatEvent {
  type: "text" | "status" | "theory" | "error" | "thinking" | "solver_progress" | "done";
  content: string;
  /** Structured theory data when type === "theory" */
  theory?: TheoryJson;
  /** Solver progress data when type === "solver_progress" */
  solverProgress?: SolverProgressEvent;
}

// ── Reusable schema fragments ────────────────────────────────────────────────

const theoryParam = {
  type: "string" as const,
  description: "Theory name — either a library theory (e.g. 'Monoid', 'Group', 'Ring', 'Category') or a stored variable name from store_theory",
};

const candidateSchema = {
  type: "object" as const,
  description: "A theory definition in TheoryJson format",
  properties: {
    name: { type: "string" as const },
    doctrine: {
      type: "string" as const,
      description:
        "Doctrine: LawvereTheory, Category, MonoidalCategory, CartesianCategory, " +
        "SymmetricMonoidal, BraidedMonoidal, FinitelyComplete, FinitelyCocomplete, " +
        "Abelian, Topos, ElementaryTopos, GrothendieckTopos, ModelCategory, " +
        "MartinLofTypeTheory, CubicalTypeTheory, LinearLogic, GeometricLogic, Operad, " +
        "EnrichedCategory, TriangulatedCategory, Locale, DifferentialGraded, " +
        "StableCategory, Derivator, InfinityNCategory, PresentableInfinityCategory, " +
        "CohesiveHomotopyTypeTheory, CartesianClosed, SymmetricMonoidalClosed",
    },
    objects: {
      type: "array" as const,
      items: {
        type: "object" as const,
        properties: { name: { type: "string" as const }, description: { type: "string" as const } },
        required: ["name"],
      },
    },
    morphisms: {
      type: "array" as const,
      items: {
        type: "object" as const,
        properties: {
          name: { type: "string" as const },
          domain: { description: "ExprJson: string | {atom:s} | {comp:[e,e]} | {prod:[e,e]} | {tensor:[e,e]} | {hom:[e,e]} | {coprod:[e,e]} | {id:e} | 'terminal' | 'initial' | 'unit'" },
          codomain: { description: "ExprJson (same format as domain)" },
          description: { type: "string" as const },
        },
        required: ["name", "domain", "codomain"],
      },
    },
    axioms: {
      type: "array" as const,
      items: {
        type: "object" as const,
        properties: {
          name: { type: "string" as const },
          lhs: { description: "ExprJson (left-hand side of equation)" },
          rhs: { description: "ExprJson (right-hand side of equation)" },
          description: { type: "string" as const },
        },
        required: ["name", "lhs", "rhs"],
      },
    },
  },
  required: ["name", "doctrine", "objects", "morphisms", "axioms"],
};

const operatorEnum =
  "Operators: adjunction, arrow, arrow_category, artin_gluing, assembly, " +
  "booleanize, bousfield, center, change_of_base, chain_complex, chu, cleavage, " +
  "collage, comma, core, coproduct, cwf, day_convolution, decategorify_iso, " +
  "decategorify_K0, decategorify_chi, derived, dialectica, drinfeld_center, " +
  "eilenberg_moore, ends_coends, ex_completion, factorization, family, fractions, " +
  "free, freyd, functor_category, grothendieck, homotopy, ind_completion, int, " +
  "internal_cat, isbell, isbell_spec, isbell_cospec, kan, left_kan, right_kan, " +
  "karoubi, kleisli, lawvere, limits, localize, macneille, matrix, mirror, monad, " +
  "morita, nerve, operad_envelope, opposite, path, per, presheaf, product, " +
  "pro_completion, quotient, realize, realizability, reg_completion, scone, " +
  "sheafify, skolem, slice, span, cospan, stabilize, subcategory, syntactic, " +
  "tripos_to_topos, twisted_arrow, ultrapower, yoneda";

// ── CAS tools available to the LLM ──────────────────────────────────────────

const CAS_TOOLS: Anthropic.Tool[] = [
  // ── Exploration tools ──────────────────────────────────────────────────────
  {
    name: "list_theories",
    description:
      "List all available theories in the CatLab library. Returns: Monoid, Group, Ring, " +
      "Semiring, Module, LieAlgebra, HopfAlgebra, DifferentialGradedAlgebra, Poset, Lattice, " +
      "BooleanAlgebra, GeometricLogic, LinearLogic, Locale, Category, SymmetricMonoidalCategory, " +
      "AbelianCategory, TriangulatedCategory, ModelCategory, EnrichedCategory, Derivator, " +
      "ElementaryTopos, InfinityTopos, CohesiveHoTT, CategoriesWithAttributes, " +
      "InfinityNCategory, Operad, HoTT, CubicalTypeTheory, Basic.",
    input_schema: { type: "object" as const, properties: {}, required: [] },
  },
  {
    name: "get_summary",
    description:
      "Get the full CAS summary of a theory: doctrine, objects, morphisms (with domain/codomain), " +
      "and axioms (with lhs/rhs equations). Essential for understanding a theory before transforming it.",
    input_schema: {
      type: "object" as const,
      properties: { theory: theoryParam },
      required: ["theory"],
    },
  },
  {
    name: "validate_theory",
    description: "Check if a named library theory is well-formed. Returns valid/invalid + error details.",
    input_schema: {
      type: "object" as const,
      properties: { theory: theoryParam },
      required: ["theory"],
    },
  },

  // ── Operator application ───────────────────────────────────────────────────
  {
    name: "apply_operator",
    description:
      "Apply a unary operator to a theory and get the resulting theory. " +
      "Results from previous operations are automatically available by name for chaining. " +
      operatorEnum,
    input_schema: {
      type: "object" as const,
      properties: {
        operator: { type: "string" as const, description: "Operator name (lowercase with underscores). " + operatorEnum },
        theory: theoryParam,
      },
      required: ["operator", "theory"],
    },
  },
  {
    name: "compute_pushout",
    description:
      "Compute the pushout (amalgamation) of two theories over a shared base. " +
      "The pushout glues theory1 and theory2 together, identifying the structure they share via base. " +
      "Results from previous operations are automatically available by name.",
    input_schema: {
      type: "object" as const,
      properties: {
        theory1: { ...theoryParam, description: "First theory name" },
        theory2: { ...theoryParam, description: "Second theory name" },
        base: { ...theoryParam, description: "Base theory (shared sub-structure)" },
      },
      required: ["theory1", "theory2", "base"],
    },
  },

  // ── Theory construction & validation ───────────────────────────────────────
  {
    name: "submit_theory",
    description:
      "Submit a CUSTOM theory definition to the CAS for validation. Use when the user asks " +
      "to construct/create/define/make a new theory (e.g. 'make a non-commutative group', " +
      "'define a monoid with two generators', 'create a category with a braiding'). " +
      "The CAS validates well-formedness and returns structured feedback.",
    input_schema: {
      type: "object" as const,
      properties: { theory: candidateSchema },
      required: ["theory"],
    },
  },

  // ── Solver: delegates to a sub-LLM loop for search problems ─────────────
  {
    name: "solve",
    description:
      "Launch a dedicated solver to find a theory satisfying a constraint. " +
      "The solver runs an autonomous LLM↔CAS feedback loop (up to 5 rounds of propose→verify→refine). " +
      "Use this for ALL search/inverse/construction problems — it is much more capable than manual attempts.\n\n" +
      "Problem types:\n" +
      "- inverse: find X such that op(X) ≅ target (e.g. 'find X whose opposite is Ring')\n" +
      "- pushout_complement: find X such that pushout(base, X) ≅ target\n" +
      "- extension: find X extending base with a property (has_inverses, commutative, etc.)\n" +
      "- multi_objective: find X satisfying multiple op(X)≅T constraints simultaneously\n" +
      "- fixed_point: find X such that op(X) ≅ X\n" +
      "- pullback_complement: find X such that pullback(base, X) ≅ target\n" +
      "- simplification: find minimal X ≅ target\n" +
      "- model: find a concrete model/instance of a theory\n" +
      "- subobject: find sub-theory of target satisfying a property\n" +
      "- synthesis: find morphism composition within a theory\n" +
      "- quotient: find minimal quotient of base satisfying a property\n" +
      "- decomposition: decompose target into independent components\n" +
      "- relaxation: find X closest to target satisfying a property\n" +
      "- catalyst: find C such that source⊗C → target⊗C",
    input_schema: {
      type: "object" as const,
      properties: {
        problem_type: {
          type: "string" as const,
          description: "Problem type (see list above)",
          enum: [
            "inverse", "pushout_complement", "extension", "multi_objective",
            "fixed_point", "pullback_complement", "simplification", "model",
            "subobject", "synthesis", "quotient", "decomposition", "relaxation", "catalyst",
          ],
        },
        // All params are optional — the solver uses whichever ones are relevant
        target: { ...theoryParam, description: "Target theory name" },
        forward_op: { type: "string" as const, description: "Operator name (for inverse/fixed_point). " + operatorEnum },
        base: { ...theoryParam, description: "Base theory name (for pushout_complement/extension/quotient)" },
        source: { ...theoryParam, description: "Source theory name (for catalyst)" },
        property: { type: "string" as const, description: "Property string (for extension/subobject/quotient/relaxation)" },
        objectives: {
          type: "array" as const,
          description: "For multi_objective: list of {target, forward_op} pairs",
          items: {
            type: "object" as const,
            properties: {
              target: theoryParam,
              forward_op: { type: "string" as const },
            },
            required: ["target", "forward_op"],
          },
        },
        theory: { ...theoryParam, description: "Theory name (for model/synthesis)" },
        max_rounds: { type: "number" as const, description: "Max solver rounds (default 5)" },
      },
      required: ["problem_type"],
    },
  },

];

// ── System prompt for the chat agent ─────────────────────────────────────────

const CHAT_SYSTEM_PROMPT = `You are CatLab Studio's interactive assistant. You help users explore and construct categorical theories using a rigorous Computer Algebra System (CAS) backed by Lean 4.

You have tools to interact with the CAS. Use them proactively — don't just describe what something is, show the user by calling the CAS.

## Your capabilities:
- **Explore**: List theories, get summaries, validate theories
- **Transform**: Apply operators (opposite, free, center, etc.) to existing theories
- **Combine**: Compute pushouts of theories over a shared base
- **Construct**: Define new theories from scratch and validate them with the CAS
- **Verify**: Check if a candidate theory satisfies operator(X) ≅ target

## Theory JSON Format
When constructing theories, use this format:
\`\`\`json
{
  "name": "MyTheory",
  "doctrine": "LawvereTheory",
  "objects": [{ "name": "X" }],
  "morphisms": [
    { "name": "μ", "domain": {"prod": ["X", "X"]}, "codomain": "X" }
  ],
  "axioms": [
    { "name": "assoc", "lhs": {...}, "rhs": {...} }
  ]
}
\`\`\`

## Expr JSON:
| JSON | Meaning |
|------|---------|
| \`"X"\` | Object atom |
| \`{"atom": "f"}\` | Morphism atom |
| \`{"comp": [e1, e2]}\` | e1 ∘ e2 |
| \`{"prod": [e1, e2]}\` | e1 × e2 |
| \`{"id": "X"}\` | identity on X |
| \`"terminal"\` | terminal object 1 |

## Doctrines:
LawvereTheory (single-sorted algebraic), Category, MonoidalCategory, CartesianCategory, SymmetricMonoidal, Abelian, Topos, etc.

## Multi-step computation:
Results from apply_operator, compute_pushout, and submit_theory are automatically stored by name.
You can reference computed results in subsequent operations just like library theories.
For example: apply_operator("free", "Monoid") → stores result as "Free_Monoid" →
then apply_operator("opposite", "Free_Monoid") works automatically.
Chain operations freely — the session remembers all intermediate results.

## When to use each tool:

| User intent | Tool to use |
|-------------|-------------|
| "What theories exist?" | list_theories |
| "Tell me about Monoid" | get_summary |
| "Is Ring valid?" | validate_theory |
| "Apply opposite to Monoid" | apply_operator |
| "Combine Group and Lattice" | compute_pushout |
| "Make/create/define a new theory" | submit_theory |
| "Find X whose opposite is Ring" | **solve** (problem_type: "inverse") |
| "Find X extending Monoid with inverses" | **solve** (problem_type: "extension") |
| "Find a theory unchanged by opposite" | **solve** (problem_type: "fixed_point") |
| Any "find X such that..." problem | **solve** (choose appropriate problem_type) |

**CRITICAL**: For ANY search/inverse/construction problem, use the **solve** tool.
It launches a dedicated sub-LLM solver that runs an autonomous propose→verify→refine loop
with the CAS (up to 5 rounds). It is FAR more capable than manually constructing theories
with submit_theory. Do NOT try to solve inverse problems by hand — always delegate to solve.

## Deep Verification (Lean/Mathlib)

When enabled (via --deep flag), theories are also type-checked against Lean 4 / Mathlib after passing structural checks. Results:
- **✓ success**: Fully verified by Lean's kernel
- **✗ semantic_error**: Type mismatch — a morphism's domain/codomain is incompatible with its usage
- **⚠ unverified_axiom**: Well-typed but aesop_cat couldn't auto-prove some axioms

## Inequality Axioms

For Dialectica/Preorder doctrines, axioms can use \`"relation": "ineq"\` for ≤ constraints instead of =.

## Guidelines:
- When asked to "make" or "create" something, actually construct the theory JSON and submit it
- Explain your reasoning in plain English alongside the CAS results
- If validation fails, read the feedback carefully and fix the theory
- For questions about existing theories, always fetch the real CAS summary — don't guess
- Be concise but educational — this is a learning tool
- When showing theory results, highlight the key mathematical structure`;

// ── ChatAgent class ──────────────────────────────────────────────────────────

export class ChatAgent {
  private client: Anthropic;
  private casClient: CatlabClient;
  private history: Anthropic.MessageParam[] = [];
  /** Session-local theory variable store: name → TheoryJson */
  private theoryStore = new Map<string, TheoryJson>();

  constructor(casClient: CatlabClient, apiKey?: string) {
    this.client = new Anthropic({ apiKey: apiKey ?? process.env.ANTHROPIC_API_KEY });
    this.casClient = casClient;
  }

  /**
   * Process a user message through the LLM agent loop.
   * The agent may call CAS tools multiple times before responding.
   * Returns an array of events for the UI to render.
   */
  async processMessage(
    userMessage: string,
    onEvent?: (event: ChatEvent) => void,
  ): Promise<ChatEvent[]> {
    const events: ChatEvent[] = [];
    const emit = (ev: ChatEvent) => {
      events.push(ev);
      onEvent?.(ev);
    };

    this.trimHistory();
    this.history.push({ role: "user", content: userMessage });

    // Agent loop: keep calling until we get a final text response
    let iterations = 0;
    const MAX_ITERATIONS = 10;

    while (iterations < MAX_ITERATIONS) {
      iterations++;

      const response = await this.client.messages.create({
        model: "claude-sonnet-4-6",
        max_tokens: 16000,
        // First iteration needs more thinking (intent interpretation, tool selection).
        // Follow-up iterations are mostly "here's the tool result, format the answer".
        thinking: { type: "enabled", budget_tokens: iterations === 1 ? 4096 : 1024 },
        system: [
          {
            type: "text",
            text: CHAT_SYSTEM_PROMPT,
            cache_control: { type: "ephemeral" },
          },
        ],
        tools: CAS_TOOLS,
        messages: this.history,
      } as any);

      // Collect text and tool_use blocks
      const textParts: string[] = [];
      const toolUses: Anthropic.ToolUseBlock[] = [];

      for (const block of response.content) {
        if (block.type === "thinking") {
          const text = (block as any).thinking ?? "";
          if (text) {
            emit({ type: "thinking", content: text });
          }
          continue;
        } else if ((block as any).type === "redacted_thinking") {
          emit({ type: "thinking", content: "(reasoning redacted)" });
          continue;
        } else if (block.type === "text" && (block as any).text?.trim()) {
          textParts.push((block as any).text);
        } else if (block.type === "tool_use") {
          toolUses.push(block as Anthropic.ToolUseBlock);
        }
      }

      // Emit any text
      if (textParts.length > 0) {
        emit({ type: "text", content: textParts.join("\n") });
      }

      // Append assistant response to history
      this.history.push({ role: "assistant", content: response.content });

      // Only break when there are no tool calls to execute.
      // The model can emit text + tool_use in the same turn with stop_reason "end_turn" —
      // we still need to execute those tools.
      if (toolUses.length === 0) {
        break;
      }

      // Execute tool calls and collect results
      const toolResults: Anthropic.ToolResultBlockParam[] = [];

      for (const toolUse of toolUses) {
        emit({
          type: "status",
          content: `Calling ${toolUse.name}...`,
        });

        const result = await this.executeTool(toolUse.name, toolUse.input as Record<string, unknown>, emit);

        // If we got a theory back, auto-store it and emit it
        if (result.theory) {
          this.theoryStore.set(result.theory.name, result.theory);
          emit({
            type: "theory",
            content: result.theory.name,
            theory: result.theory,
          });
        }

        toolResults.push({
          type: "tool_result",
          tool_use_id: toolUse.id,
          content: result.text,
        });
      }

      // Add tool results to history
      this.history.push({ role: "user", content: toolResults });
    }

    emit({ type: "done", content: "" });
    return events;
  }

  /**
   * Execute a single CAS tool call and return the result as text.
   */
  private async executeTool(
    name: string,
    input: Record<string, unknown>,
    emit?: (ev: ChatEvent) => void,
  ): Promise<{ text: string; theory?: TheoryJson }> {
    try {
      switch (name) {
        case "list_theories": {
          const r = await api.listTheories(this.casClient);
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          const stored = [...this.theoryStore.keys()];
          let text = `Available theories (${r.data.theories.length}):\n${r.data.theories.join(", ")}`;
          if (stored.length > 0) {
            text += `\n\nStored variables (${stored.length}):\n${stored.join(", ")}`;
          }
          return { text };
        }

        case "get_summary": {
          const theoryName = input.theory as string;
          // Check stored theories first
          const stored = this.theoryStore.get(theoryName);
          if (stored) {
            return { text: `Stored theory '${theoryName}':\n${JSON.stringify(stored, null, 2)}`, theory: stored };
          }
          const r = await api.getTheorySummary(this.casClient, theoryName);
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          return { text: r.data.summary };
        }

        case "validate_theory": {
          const r = await api.validateTheory(this.casClient, input.theory as string);
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          return {
            text: r.data.valid
              ? `Theory '${input.theory}' is valid.`
              : `Theory '${input.theory}' is invalid: ${r.data.errors.join(", ")}`,
          };
        }

        case "apply_operator": {
          const theoryName = input.theory as string;
          // Resolve: check session store first, then pass to CAS (which checks library)
          const stored = this.theoryStore.get(theoryName);
          if (stored) {
            const res = await this.casClient.request(
              { command: "apply_operator", operator: input.operator, theory: JSON.stringify(stored) } as any,
              30_000
            );
            if (res.status === "error") return { text: `CAS error: ${res.message}` };
            const theory = (res as any).theory ?? null;
            if (!theory) return { text: (res as any).message ?? "Operator returned no theory." };
            return { text: JSON.stringify(theory, null, 2), theory };
          }
          const r = await api.applyOperator(this.casClient, input.operator as string, theoryName);
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          const theory = r.data.theory;
          if (!theory) return { text: r.data.message ?? "Operator returned no theory." };
          return { text: JSON.stringify(theory, null, 2), theory };
        }

        case "compute_pushout": {
          // Resolve each theory: session store first, then pass name to CAS
          const resolve = (key: string): string => {
            const name = input[key] as string;
            const stored = this.theoryStore.get(name);
            return stored ? JSON.stringify(stored) : name;
          };
          const res = await this.casClient.request(
            { command: "compute_pushout", theory1: resolve("theory1"), theory2: resolve("theory2"), base: resolve("base") } as any,
            30_000
          );
          if (res.status === "error") return { text: `CAS error: ${res.message}` };
          const theory = (res as any).theory ?? null;
          if (!theory) return { text: (res as any).message ?? "Pushout returned no theory." };
          return { text: JSON.stringify(theory, null, 2), theory };
        }

        case "submit_theory": {
          const theoryJson = input.theory as TheoryJson;
          const r = await api.submitTheory(this.casClient, theoryJson);
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          if (r.data.valid) {
            return {
              text: `Theory '${theoryJson.name}' is VALID.\n${JSON.stringify(theoryJson, null, 2)}`,
              theory: theoryJson,
            };
          }
          return {
            text: `Theory '${theoryJson.name}' INVALID:\n${r.data.errors.join("\n")}\n\nSubmitted:\n${JSON.stringify(theoryJson, null, 2)}`,
          };
        }

        case "solve":
          return this.runSolver(input, emit);

        default:
          return { text: `Unknown tool: ${name}` };
      }
    } catch (e) {
      return { text: `Tool execution error: ${(e as Error).message}` };
    }
  }

  /**
   * Delegate a search problem to the GenericSolver, which runs its own
   * inner LLM↔CAS feedback loop with a dedicated sub-LLM.
   */
  private async runSolver(
    input: Record<string, unknown>,
    emit?: (ev: ChatEvent) => void,
  ): Promise<{ text: string; theory?: TheoryJson }> {
    const type = input.problem_type as string;
    const maxRounds = (input.max_rounds as number) || 5;

    // Build the appropriate verifier
    let verifier;
    switch (type) {
      case "inverse":
        verifier = new InverseVerifier(input.target as string, input.forward_op as string);
        break;
      case "pushout_complement":
        verifier = new PushoutComplementVerifier(input.base as string, input.target as string);
        break;
      case "extension":
        verifier = new ExtensionVerifier(input.base as string, input.property as string);
        break;
      case "multi_objective": {
        const rawObjs = input.objectives as Array<{ target: string; forward_op: string }>;
        verifier = new MultiObjectiveVerifier(
          rawObjs.map(o => ({ target: o.target, forwardOp: o.forward_op }))
        );
        break;
      }
      case "fixed_point":
        verifier = new FixedPointVerifier(input.target as string || "Basic", input.forward_op as string);
        break;
      case "pullback_complement":
        verifier = new PullbackComplementVerifier(input.base as string, input.target as string);
        break;
      case "simplification":
        verifier = new SimplificationVerifier(input.target as string);
        break;
      case "model":
        verifier = new ModelFindingVerifier(input.theory as string || input.target as string);
        break;
      case "subobject":
        verifier = new SubobjectVerifier(input.target as string, input.property as string);
        break;
      case "synthesis":
        verifier = new SynthesisVerifier(input.theory as string || input.target as string, input.source as string || "", input.target as string || "");
        break;
      case "quotient":
        verifier = new QuotientVerifier(input.base as string, input.property as string);
        break;
      case "decomposition":
        verifier = new DecompositionVerifier(input.target as string);
        break;
      case "relaxation":
        verifier = new RelaxationVerifier(input.target as string, input.property as string);
        break;
      case "catalyst":
        verifier = new CatalystVerifier(input.source as string, input.target as string);
        break;
      default:
        return { text: `Unknown problem type: ${type}` };
    }

    const llm = new LLMClient();
    const solver = new GenericSolver(this.casClient, llm, verifier);

    try {
      const result: SolverResult = await solver.solve({
        maxRounds,
        onProgress: emit ? (ev) => {
          emit({ type: "solver_progress", content: ev.message, solverProgress: ev });
        } : undefined,
      });

      if (result.success && result.winner) {
        const winner = result.winner as TheoryJson;
        return {
          text: `Solver succeeded in ${result.rounds} round(s).\n\n` +
            `Solution: "${winner.name}"\n` +
            JSON.stringify(winner, null, 2),
          theory: winner,
        };
      } else {
        // Return best attempt with feedback
        const last = result.history[result.history.length - 1];
        let text = `Solver exhausted ${result.rounds} round(s) without finding a verified solution.\n`;
        if (last) {
          text += `\nBest attempt: ${JSON.stringify(last.payload, null, 2)}`;
          text += `\n\nFinal verification: ${last.result.verificationStatus}`;
          if (last.result.distance !== undefined) {
            text += `\nDistance: ${last.result.distance}`;
          }
        }
        if (result.reflection) {
          text += `\n\nReflection: ${result.reflection}`;
        }
        return { text, theory: last?.payload as TheoryJson | undefined };
      }
    } catch (e) {
      return { text: `Solver error: ${(e as Error).message}` };
    }
  }

  /**
   * Trim history to stay within context limits.
   * Trims at exchange boundaries (user+assistant pairs) to avoid breaking
   * turn alternation or orphaning tool_result references.
   */
  private trimHistory(): void {
    const MAX_HISTORY = 40;
    if (this.history.length <= MAX_HISTORY) return;

    // Find safe cut points: indices where a user message starts a new exchange
    // (i.e., the previous message is an assistant message without pending tool_use).
    const safeCuts: number[] = [];
    for (let i = 2; i < this.history.length; i++) {
      if (
        this.history[i].role === "user" &&
        this.history[i - 1].role === "assistant"
      ) {
        // Check the assistant message doesn't contain tool_use that needs a tool_result
        const content = this.history[i - 1].content;
        const hasToolUse = Array.isArray(content) &&
          content.some((b: any) => b.type === "tool_use");
        const nextIsToolResult = Array.isArray(this.history[i].content) &&
          (this.history[i].content as any[]).some((b: any) => b.type === "tool_result");
        // If assistant used tools and next user msg has tool_results, skip this cut point
        if (hasToolUse && nextIsToolResult) continue;
        safeCuts.push(i);
      }
    }

    // Find the latest safe cut that brings us under the limit
    const keep = MAX_HISTORY - 2;
    const targetStart = this.history.length - keep;
    let cutAt = 2; // fallback: keep first exchange
    for (const idx of safeCuts) {
      if (idx >= targetStart) break;
      cutAt = idx;
    }

    const head = this.history.slice(0, 2);
    const tail = this.history.slice(cutAt);
    this.history = [...head, ...tail];
  }

  /** Reset conversation history and theory store */
  reset(): void {
    this.history = [];
    this.theoryStore.clear();
  }

  /** Get conversation history length (for testing) */
  get historyLength(): number {
    return this.history.length;
  }
}
