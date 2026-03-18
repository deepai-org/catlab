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
import type { TheoryJson } from "./types";
import * as api from "./api";

// ── Chat message types (sent to UI via SSE) ──────────────────────────────────

export interface ChatEvent {
  type: "text" | "status" | "theory" | "error" | "done";
  content: string;
  /** Structured theory data when type === "theory" */
  theory?: TheoryJson;
}

// ── Reusable schema fragments ────────────────────────────────────────────────

const theoryParam = {
  type: "string" as const,
  description: "Library theory name (e.g. 'Monoid', 'Group', 'Ring', 'Category')",
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
  "Operators: adjunction, algebraize, amalgamate, arrow, artin_gluing, assembly, " +
  "booleanize, bousfield, center, change_of_base, chu, cleavage, collage, comma, " +
  "coproduct, core, cwf, day_convolution, decategorify, derived, dialectica, " +
  "drinfeld_center, eilenberg_moore, ends_coends, exact_completion, factorization, " +
  "family, fractions, free, freyd, functor_category, grothendieck, ind_pro, int, " +
  "internal, isbell, kan, karoubi, kleisli, lawvere, limits, localize, macneille, " +
  "matrix, mirror, monad, morita, nerve, operad_envelope, opposite, per, product, " +
  "pushout, quotient, realizability, sheafify, skolem, slice, span, stabilize, " +
  "subcategory, syntactic, tripos_to_topos, twisted_arrow, ultrapower, yoneda";

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
      "Apply a unary operator to a library theory and get the resulting theory. " + operatorEnum,
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
      "The pushout glues theory1 and theory2 together, identifying the structure they share via base.",
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

  // ── Inverse problem: find X such that op(X) ≅ target ──────────────────────
  {
    name: "evaluate_inverse",
    description:
      "Check if a candidate theory X satisfies operator(X) ≅ target. " +
      "Returns verification result with missing morphisms, axiom violations, distance score. " +
      "Use this to iteratively refine a candidate.",
    input_schema: {
      type: "object" as const,
      properties: {
        target: theoryParam,
        forward_op: { type: "string" as const, description: "Forward operator name. " + operatorEnum },
        candidate: candidateSchema,
      },
      required: ["target", "forward_op", "candidate"],
    },
  },

  // ── Pushout complement: find X such that pushout(base, X) ≅ target ────────
  {
    name: "evaluate_pushout_complement",
    description:
      "Check if a candidate X satisfies pushout(base, X) ≅ target. " +
      "Use when asking: 'what do I need to add to base to get target?'",
    input_schema: {
      type: "object" as const,
      properties: {
        base: theoryParam,
        target: theoryParam,
        candidate: candidateSchema,
      },
      required: ["base", "target", "candidate"],
    },
  },

  // ── Extension: find X extending base with property P ──────────────────────
  {
    name: "evaluate_extension",
    description:
      "Check if candidate X extends a base theory and satisfies a property. " +
      "Properties: has_inverses, commutative, idempotent, distributive, etc.",
    input_schema: {
      type: "object" as const,
      properties: {
        base: theoryParam,
        property: { type: "string" as const, description: "Property to check (e.g. 'has_inverses', 'commutative')" },
        candidate: candidateSchema,
      },
      required: ["base", "property", "candidate"],
    },
  },

  // ── Multi-objective: find X satisfying op₁(X)≅T₁ ∧ op₂(X)≅T₂ ────────────
  {
    name: "evaluate_multi_objective",
    description:
      "Check if candidate X simultaneously satisfies multiple operator-target pairs. " +
      "E.g., find X where opposite(X)≅Monoid AND mirror(X)≅Monoid.",
    input_schema: {
      type: "object" as const,
      properties: {
        objectives: {
          type: "array" as const,
          items: {
            type: "object" as const,
            properties: {
              target: theoryParam,
              forward_op: { type: "string" as const, description: "Operator name" },
            },
            required: ["target", "forward_op"],
          },
          description: "List of {target, forward_op} pairs",
        },
        candidate: candidateSchema,
      },
      required: ["objectives", "candidate"],
    },
  },

  // ── Fixed point: find X such that op(X) ≅ X ──────────────────────────────
  {
    name: "evaluate_fixed_point",
    description:
      "Check if candidate X is a fixed point of an operator: op(X) ≅ X. " +
      "E.g., 'find a theory unchanged by opposite'.",
    input_schema: {
      type: "object" as const,
      properties: {
        forward_op: { type: "string" as const, description: "Operator name. " + operatorEnum },
        candidate: candidateSchema,
      },
      required: ["forward_op", "candidate"],
    },
  },

  // ── Pullback complement: find X such that pullback(base, X) ≅ target ──────
  {
    name: "evaluate_pullback_complement",
    description: "Check if candidate X satisfies pullback(base, X) ≅ target.",
    input_schema: {
      type: "object" as const,
      properties: {
        base: theoryParam,
        target: theoryParam,
        candidate: candidateSchema,
      },
      required: ["base", "target", "candidate"],
    },
  },

  // ── Simplification: find minimal X ≅ target ──────────────────────────────
  {
    name: "evaluate_simplification",
    description: "Check if candidate X is a valid simplification (minimal representation) of target.",
    input_schema: {
      type: "object" as const,
      properties: {
        target: theoryParam,
        candidate: candidateSchema,
      },
      required: ["target", "candidate"],
    },
  },

  // ── Model finding: generate a concrete instance ───────────────────────────
  {
    name: "evaluate_model",
    description:
      "Check if candidate is a valid concrete model/instance of a theory. " +
      "E.g., 'give me a concrete example of a Group' → the integers under addition.",
    input_schema: {
      type: "object" as const,
      properties: {
        theory: theoryParam,
        candidate: candidateSchema,
      },
      required: ["theory", "candidate"],
    },
  },

  // ── Subobject: find sub-theory satisfying property P ──────────────────────
  {
    name: "evaluate_subobject",
    description:
      "Check if candidate is a valid sub-theory of target satisfying a given property.",
    input_schema: {
      type: "object" as const,
      properties: {
        target: theoryParam,
        property: { type: "string" as const, description: "Property the sub-theory must satisfy" },
        candidate: candidateSchema,
      },
      required: ["target", "property", "candidate"],
    },
  },

  // ── Synthesis: find morphism composition ──────────────────────────────────
  {
    name: "evaluate_synthesis",
    description:
      "Check if candidate provides a valid morphism composition from source to target within a theory.",
    input_schema: {
      type: "object" as const,
      properties: {
        theory: theoryParam,
        candidate: candidateSchema,
      },
      required: ["theory", "candidate"],
    },
  },

  // ── Quotient: find minimal quotient ───────────────────────────────────────
  {
    name: "evaluate_quotient",
    description: "Check if candidate is a valid minimal quotient of base satisfying a property.",
    input_schema: {
      type: "object" as const,
      properties: {
        base: theoryParam,
        property: { type: "string" as const, description: "Property the quotient must satisfy" },
        candidate: candidateSchema,
      },
      required: ["base", "property", "candidate"],
    },
  },

  // ── Decomposition: decompose into independent components ──────────────────
  {
    name: "evaluate_decomposition",
    description: "Check if candidate provides a valid decomposition of target into independent components.",
    input_schema: {
      type: "object" as const,
      properties: {
        target: theoryParam,
        candidate: candidateSchema,
      },
      required: ["target", "candidate"],
    },
  },

  // ── Relaxation: find X closest to target satisfying property ──────────────
  {
    name: "evaluate_relaxation",
    description: "Check if candidate is a valid relaxation of target that satisfies a given property.",
    input_schema: {
      type: "object" as const,
      properties: {
        target: theoryParam,
        property: { type: "string" as const, description: "Property the relaxation must satisfy" },
        candidate: candidateSchema,
      },
      required: ["target", "property", "candidate"],
    },
  },

  // ── Catalyst: find C such that source⊗C → target⊗C ───────────────────────
  {
    name: "evaluate_catalyst",
    description:
      "Check if candidate C acts as a catalyst: source⊗C can be transformed into target⊗C. " +
      "The catalyst enables a transformation that isn't possible without it.",
    input_schema: {
      type: "object" as const,
      properties: {
        source: theoryParam,
        target: theoryParam,
        candidate: candidateSchema,
      },
      required: ["source", "target", "candidate"],
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

  constructor(casClient: CatlabClient, apiKey?: string) {
    this.client = new Anthropic({ apiKey: apiKey ?? process.env.ANTHROPIC_API_KEY });
    this.casClient = casClient;
  }

  /**
   * Process a user message through the LLM agent loop.
   * The agent may call CAS tools multiple times before responding.
   * Returns an array of events for the UI to render.
   */
  async processMessage(userMessage: string): Promise<ChatEvent[]> {
    const events: ChatEvent[] = [];

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
          // Thinking blocks are internal reasoning — don't expose to user
          continue;
        } else if (block.type === "text" && (block as any).text?.trim()) {
          textParts.push((block as any).text);
        } else if (block.type === "tool_use") {
          toolUses.push(block as Anthropic.ToolUseBlock);
        }
      }

      // Emit any text
      if (textParts.length > 0) {
        events.push({ type: "text", content: textParts.join("\n") });
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
        events.push({
          type: "status",
          content: `Calling ${toolUse.name}...`,
        });

        const result = await this.executeTool(toolUse.name, toolUse.input as Record<string, unknown>);

        // If we got a theory back, emit it
        if (result.theory) {
          events.push({
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

    events.push({ type: "done", content: "" });
    return events;
  }

  /**
   * Execute a single CAS tool call and return the result as text.
   */
  private async executeTool(
    name: string,
    input: Record<string, unknown>
  ): Promise<{ text: string; theory?: TheoryJson }> {
    try {
      switch (name) {
        case "list_theories": {
          const r = await api.listTheories(this.casClient);
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          return { text: `Available theories (${r.data.theories.length}):\n${r.data.theories.join(", ")}` };
        }

        case "get_summary": {
          const r = await api.getTheorySummary(this.casClient, input.theory as string);
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
          const r = await api.applyOperator(
            this.casClient,
            input.operator as string,
            input.theory as string
          );
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          const theory = r.data.theory;
          if (!theory) return { text: r.data.message ?? "Operator returned no theory." };
          return { text: JSON.stringify(theory, null, 2), theory };
        }

        case "compute_pushout": {
          const r = await api.computePushout(
            this.casClient,
            input.theory1 as string,
            input.theory2 as string,
            input.base as string
          );
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          const theory = r.data.theory;
          if (!theory) return { text: r.data.message ?? "Pushout returned no theory." };
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

        case "evaluate_inverse": {
          const r = await api.evaluateInverse(
            this.casClient,
            input.target as string,
            input.forward_op as string,
            input.candidate as TheoryJson
          );
          if (!r.ok) return { text: `Error: ${r.error.error}` };
          return { text: JSON.stringify(r.data.result, null, 2) };
        }

        // ── Evaluate commands that go through evaluate_generic or specific handlers ──

        case "evaluate_pushout_complement":
          return this.evalGeneric("evaluate_pushout_complement", {
            base: input.base,
            target: input.target,
            candidate: input.candidate,
          });

        case "evaluate_extension":
          return this.evalGeneric("evaluate_extension", {
            base: input.base,
            property: input.property,
            candidate: input.candidate,
          });

        case "evaluate_multi_objective":
          return this.evalGeneric("evaluate_multi_objective", {
            objectives: input.objectives,
            candidate: input.candidate,
          });

        case "evaluate_fixed_point":
          return this.evalGeneric("evaluate_fixed_point", {
            forward_op: input.forward_op,
            candidate: input.candidate,
          });

        case "evaluate_pullback_complement":
          return this.evalGeneric("evaluate_pullback_complement", {
            base: input.base,
            target: input.target,
            candidate: input.candidate,
          });

        case "evaluate_simplification":
          return this.evalGeneric("evaluate_simplification", {
            target: input.target,
            candidate: input.candidate,
          });

        case "evaluate_model":
          return this.evalGeneric("evaluate_model", {
            theory: input.theory,
            candidate: input.candidate,
          });

        case "evaluate_subobject":
          return this.evalGeneric("evaluate_subobject", {
            target: input.target,
            property: input.property,
            candidate: input.candidate,
          });

        case "evaluate_synthesis":
          return this.evalGeneric("evaluate_synthesis", {
            theory: input.theory,
            candidate: input.candidate,
          });

        case "evaluate_quotient":
          return this.evalGeneric("evaluate_quotient", {
            base: input.base,
            property: input.property,
            candidate: input.candidate,
          });

        case "evaluate_decomposition":
          return this.evalGeneric("evaluate_decomposition", {
            target: input.target,
            candidate: input.candidate,
          });

        case "evaluate_relaxation":
          return this.evalGeneric("evaluate_relaxation", {
            target: input.target,
            property: input.property,
            candidate: input.candidate,
          });

        case "evaluate_catalyst":
          return this.evalGeneric("evaluate_catalyst", {
            source: input.source,
            target: input.target,
            candidate: input.candidate,
          });

        default:
          return { text: `Unknown tool: ${name}` };
      }
    } catch (e) {
      return { text: `Tool execution error: ${(e as Error).message}` };
    }
  }

  /**
   * Send a command directly to the CAS and return the raw JSON result.
   */
  private async evalGeneric(
    command: string,
    payload: Record<string, unknown>
  ): Promise<{ text: string; theory?: TheoryJson }> {
    const res = await this.casClient.request(
      { command, ...payload } as any,
      30_000
    );
    if (res.status === "error") return { text: `CAS error: ${res.message}` };
    return { text: JSON.stringify(res, null, 2) };
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

  /** Reset conversation history */
  reset(): void {
    this.history = [];
  }

  /** Get conversation history length (for testing) */
  get historyLength(): number {
    return this.history.length;
  }
}
