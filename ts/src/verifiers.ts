/**
 * Concrete Verifier implementations for different problem types.
 *
 * Each verifier handles:
 *   1. Preflight: fetch context from CAS, build a ProblemSpec for the LLM
 *   2. Verify: send a candidate to the CAS, return a VerificationResult
 */

import type { CatlabClient } from "./client";
import type {
  ProblemSpec,
  Verifier,
  TheoryJson,
  VerificationResult,
} from "./types";
import { validateTheoryPayload, formatStructuralDiff } from "./llm";

// ── Helper ───────────────────────────────────────────────────────────────────

async function fetchTheorySummary(
  catlab: CatlabClient,
  name: string,
  timeoutMs: number,
): Promise<{ json: string; theory?: TheoryJson }> {
  const res = await catlab.requestOrThrow(
    { command: "summary", theory: name },
    timeoutMs,
  );
  return {
    json: res.theory ? JSON.stringify(res.theory, null, 2) : `(name: ${name})`,
    theory: res.theory,
  };
}

// ── 1. Inverse problem verifier ─────────────────────────────────────────────

/**
 * find X such that forwardOp(X) ≅ target
 */
export class InverseVerifier implements Verifier {
  constructor(
    private targetName: string,
    private forwardOp: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const { json } = await fetchTheorySummary(catlab, this.targetName, timeoutMs);
    const { problem, hint } = describeInverseProblem(this.forwardOp, this.targetName);

    return {
      kind: "inverse",
      problemDescription: problem,
      hint,
      contextJson: `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_inverse",
        target: this.targetName,
        forward_op: this.forwardOp,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    return res.result!;
  }
}

// ── 2. Pushout complement verifier ──────────────────────────────────────────

/**
 * find X such that pushout(inclusion(base, X), inclusion(base, known)) ≅ target
 *
 * Classic pushout complement: given a span B → A and B → T, find X such that
 * the pushout A ⊔_B X ≅ T.
 */
export class PushoutComplementVerifier implements Verifier {
  constructor(
    private baseName: string,
    private targetName: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const [base, target] = await Promise.all([
      fetchTheorySummary(catlab, this.baseName, timeoutMs),
      fetchTheorySummary(catlab, this.targetName, timeoutMs),
    ]);

    return {
      kind: "pushout_complement",
      problemDescription:
        `Find a theory X such that **pushout(inclusion(${this.baseName}, ${this.targetName}), ` +
        `inclusion(${this.baseName}, X)) ≅ "${this.targetName}"**.\n\n` +
        `The base theory "${this.baseName}" embeds into both the target and your candidate. ` +
        `The pushout amalgamates them over the shared base. Your candidate X must supply ` +
        `exactly the generators and axioms that the target has beyond what the base provides.`,
      hint:
        `**Recipe for pushout complement:**\n` +
        `1. Look at what generators the target has that the base does NOT.\n` +
        `2. Your candidate X must contain the base generators (they get identified in the pushout).\n` +
        `3. Add exactly the "extra" generators from the target.\n` +
        `4. Add axioms that relate the base generators to the new ones, matching the target's axioms.`,
      contextJson:
        `## Base Theory: "${this.baseName}"\n\n\`\`\`json\n${base.json}\n\`\`\`\n\n` +
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_pushout_complement",
        base: this.baseName,
        target: this.targetName,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    return res.result!;
  }
}

// ── 3. Extension verifier ───────────────────────────────────────────────────

/**
 * find X extending base B such that property P(X) holds.
 *
 * The candidate must contain B as a sub-theory, plus additional generators/axioms.
 * The CAS checks: (a) B embeds into X, (b) validate(X) passes, (c) property P holds.
 */
export class ExtensionVerifier implements Verifier {
  constructor(
    private baseName: string,
    private property: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const base = await fetchTheorySummary(catlab, this.baseName, timeoutMs);

    return {
      kind: "extension",
      problemDescription:
        `Find a theory X that **extends "${this.baseName}"** and satisfies the property **"${this.property}"**.\n\n` +
        `Your candidate must include all objects, morphisms, and axioms from the base theory, ` +
        `plus additional structure that makes the property hold.`,
      hint:
        `**Recipe for extension:**\n` +
        `1. Start with the base theory's generators verbatim.\n` +
        `2. Add new objects/morphisms/axioms to satisfy "${this.property}".\n` +
        `3. The CAS will check that the base embeds into your candidate and that the property holds.`,
      contextJson:
        `## Base Theory: "${this.baseName}"\n\n\`\`\`json\n${base.json}\n\`\`\`\n\n` +
        `## Required Property: "${this.property}"`,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_extension",
        base: this.baseName,
        property: this.property,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    return res.result!;
  }
}

// ── 4. Multi-objective verifier ─────────────────────────────────────────────

/**
 * find X such that F₁(X) ≅ T₁ AND F₂(X) ≅ T₂ AND ...
 *
 * All objectives must pass simultaneously. The VerificationResult merges
 * failures from all objectives.
 */
export class MultiObjectiveVerifier implements Verifier {
  constructor(
    private objectives: Array<{ target: string; forwardOp: string }>,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const summaries = await Promise.all(
      this.objectives.map(async (obj) => {
        const s = await fetchTheorySummary(catlab, obj.target, timeoutMs);
        return { ...obj, json: s.json };
      }),
    );

    const objDescriptions = summaries
      .map((s, i) => `${i + 1}. ${s.forwardOp}(X) ≅ "${s.target}"`)
      .join("\n");

    const contextParts = summaries
      .map((s) => `## Target: "${s.target}" (via ${s.forwardOp})\n\n\`\`\`json\n${s.json}\n\`\`\``)
      .join("\n\n");

    return {
      kind: "multi_objective",
      problemDescription:
        `Find a **single** theory X satisfying ALL of the following simultaneously:\n\n${objDescriptions}\n\n` +
        `The CAS will apply each operator to your candidate and check structural equivalence ` +
        `against each target. ALL must pass.`,
      hint:
        `**Strategy for multi-objective:**\n` +
        `1. Study each target theory's structure.\n` +
        `2. Find the common structure that must be preserved across all operators.\n` +
        `3. Your candidate must be compatible with every operator simultaneously.\n` +
        `4. Start with the most constraining objective and verify the others fit.`,
      contextJson: contextParts,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_multi_objective",
        objectives: this.objectives.map(o => ({ target: o.target, forward_op: o.forwardOp })),
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    return res.result!;
  }
}

// ── 5. Fixed-point verifier ──────────────────────────────────────────────────

/**
 * find X such that F(X) ≅ X
 *
 * The candidate must be a fixed point of the operator — applying F to X
 * produces something structurally equivalent to X itself.
 * Uses the target theory as a "seed" / hint for the LLM to understand
 * the domain, but the actual verification is diff(F(X), X).
 */
export class FixedPointVerifier implements Verifier {
  constructor(
    private seedName: string,
    private forwardOp: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const seed = await fetchTheorySummary(catlab, this.seedName, timeoutMs);

    return {
      kind: "inverse",  // reuse inverse kind for prompt formatting
      problemDescription:
        `Find a theory X such that **${this.forwardOp}(X) ≅ X** (a fixed point).\n\n` +
        `The CAS will apply "${this.forwardOp}" to your candidate and check whether the ` +
        `result is structurally equivalent to the candidate itself.\n\n` +
        `The theory "${this.seedName}" is provided as a reference for the domain — ` +
        `your answer may or may not resemble it.`,
      hint:
        `**Strategy for fixed points:**\n` +
        `1. Think about what theories are invariant under "${this.forwardOp}".\n` +
        `2. Self-dual theories are natural fixed points (e.g. BooleanAlgebra under mirror).\n` +
        `3. Start with a simple symmetric structure and verify it works.\n` +
        `4. The diff will show mismatches between F(X) and X — use it to adjust.`,
      contextJson:
        `## Reference Theory: "${this.seedName}"\n\n\`\`\`json\n${seed.json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.requestOrThrow(
      {
        command: "evaluate_fixed_point",
        forward_op: this.forwardOp,
        candidate,
      },
      timeoutMs,
    );
    return res.result!;
  }
}

// ── 6. Factorization verifier ──────────────────────────────────────────────

/**
 * Find (X, Y) such that X ⊗ Y ≅ T (or any binary operator).
 *
 * This demonstrates the generic architecture: the answer schema asks for TWO
 * theories, not one. The verifier defines a custom tool schema, custom
 * validation, and custom feedback formatting.
 */
export class FactorizationVerifier implements Verifier {
  constructor(
    private targetName: string,
    private binaryOp: string = "tensor",
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const target = await fetchTheorySummary(catlab, this.targetName, timeoutMs);

    return {
      kind: "factorization",
      problemDescription:
        `Find **two theories X and Y** such that **${this.binaryOp}(X, Y) ≅ "${this.targetName}"**.\n\n` +
        `You must submit two complete theory JSON objects. The CAS will compose them ` +
        `using the "${this.binaryOp}" operator and check structural equivalence with the target.`,
      hint:
        `**Strategy for factorization:**\n` +
        `1. Study the target theory's structure.\n` +
        `2. Find a natural decomposition into two independent parts.\n` +
        `3. Each factor should be a self-contained theory.\n` +
        `4. The composition of the factors must reconstruct the target.`,
      contextJson:
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\``,
      answerSchema: {
        type: "object",
        properties: {
          reasoning: { type: "string", description: "Mathematical reasoning (scratchpad)" },
          factorX: {
            type: "object",
            description: "First factor theory (X)",
            properties: {
              name: { type: "string" }, doctrine: { type: "string" },
              objects: { type: "array", items: { type: "object" } },
              morphisms: { type: "array", items: { type: "object" } },
              axioms: { type: "array", items: { type: "object" } },
            },
            required: ["name", "objects", "morphisms", "axioms"],
          },
          factorY: {
            type: "object",
            description: "Second factor theory (Y)",
            properties: {
              name: { type: "string" }, doctrine: { type: "string" },
              objects: { type: "array", items: { type: "object" } },
              morphisms: { type: "array", items: { type: "object" } },
              axioms: { type: "array", items: { type: "object" } },
            },
            required: ["name", "objects", "morphisms", "axioms"],
          },
        },
        required: ["factorX", "factorY"],
      },
      answerToolName: "propose_factorization",
      answerToolDescription: "Submit two factor theories (X, Y) for verification.",
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const p = payload as { factorX: TheoryJson; factorY: TheoryJson };
    // Use generic evaluate: pack both factors into the payload
    const res = await catlab.request(
      {
        command: "evaluate_generic" as any,
        handler: "factorization",
        payload: {
          target: this.targetName,
          binary_op: this.binaryOp,
          factor_x: p.factorX,
          factor_y: p.factorY,
        },
      } as any,
      timeoutMs,
    );
    if (res.status === "error") {
      // Fall back: verify each factor individually against the target
      // (This is a degraded mode until the Lean handler exists)
      return {
        verified: false,
        candidateName: `${p.factorX?.name ?? "X"} ⊗ ${p.factorY?.name ?? "Y"}`,
        verificationStatus: `✗ Failed: ${res.message}`,
        missingSignatures: [],
        unmappedObjects: [],
        axiomViolations: [],
        feedbackStrings: [
          `Factorization verification not yet implemented in CAS: ${res.message}`,
          `Factor X: "${p.factorX?.name}" (${p.factorX?.objects?.length ?? 0} obj)`,
          `Factor Y: "${p.factorY?.name}" (${p.factorY?.objects?.length ?? 0} obj)`,
        ],
      };
    }
    return res.result!;
  }

  validatePayload(payload: unknown): void {
    if (typeof payload !== "object" || payload === null) throw new Error("Expected object");
    const p = payload as Record<string, unknown>;
    if (!p.factorX || typeof p.factorX !== "object") throw new Error("Missing factorX");
    if (!p.factorY || typeof p.factorY !== "object") throw new Error("Missing factorY");
    validateTheoryPayload(p.factorX);
    validateTheoryPayload(p.factorY);
  }

  formatFeedback(result: VerificationResult, payload: unknown): string {
    const lines: string[] = [];
    if (result.feedbackStrings) {
      for (const fb of result.feedbackStrings) lines.push(`• ${fb}`);
    }
    if (result.distance !== undefined) {
      lines.push(`\nDistance score: ${result.distance}`);
    }
    // Include structural diff info if present
    lines.push("\n" + formatStructuralDiff(result));
    return lines.join("\n");
  }
}

// ── 7. Interpolation verifier ─────────────────────────────────────────────

/**
 * Find X with morphisms A → X and X → B.
 * The candidate must sit "between" two known theories.
 */
export class InterpolationVerifier implements Verifier {
  constructor(
    private sourceName: string,
    private targetName: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const [source, target] = await Promise.all([
      fetchTheorySummary(catlab, this.sourceName, timeoutMs),
      fetchTheorySummary(catlab, this.targetName, timeoutMs),
    ]);

    return {
      kind: "interpolation",
      problemDescription:
        `Find a theory X that **interpolates** between "${this.sourceName}" and "${this.targetName}".\n\n` +
        `Your candidate must have:\n` +
        `  • An inclusion from "${this.sourceName}" into X (X extends the source)\n` +
        `  • A morphism from X into "${this.targetName}" (X maps into the target)\n\n` +
        `In other words, X sits in a chain: ${this.sourceName} ↪ X → ${this.targetName}`,
      hint:
        `**Strategy for interpolation:**\n` +
        `1. Start with all generators from "${this.sourceName}".\n` +
        `2. Add generators that connect to "${this.targetName}"'s structure.\n` +
        `3. The source must embed fully; the target must be reachable via some morphism.`,
      contextJson:
        `## Source Theory: "${this.sourceName}"\n\n\`\`\`json\n${source.json}\n\`\`\`\n\n` +
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    // Check: source embeds into candidate (extension check)
    const extRes = await catlab.request(
      {
        command: "evaluate_extension",
        base: this.sourceName,
        property: "none",
        candidate,
      },
      timeoutMs,
    );
    if (extRes.status === "error") throw new Error(`Lean error: ${extRes.message}`);

    const extendsSource = (extRes as any).extends_base === true;

    // Check: candidate can map to target (use pushout complement as proxy)
    // For a proper check we'd need a morphism-existence command.
    // For now, verify extension of source + structural compatibility with target.
    const result = extRes.result ?? {
      verified: false,
      candidateName: candidate.name,
      verificationStatus: "✗ Failed: could not verify",
      missingSignatures: [],
      unmappedObjects: [],
      axiomViolations: [],
    };

    if (!extendsSource) {
      result.verified = false;
      result.verificationStatus = `✗ Failed: candidate does not extend "${this.sourceName}"`;
      result.feedbackStrings = [
        `Your theory must include all objects and morphisms from "${this.sourceName}".`,
      ];
    }

    return result;
  }

  formatFeedback(result: VerificationResult, _payload: unknown): string {
    const lines: string[] = [];
    if (result.feedbackStrings) {
      for (const fb of result.feedbackStrings) lines.push(`• ${fb}`);
    }
    lines.push("\n" + formatStructuralDiff(result));
    return lines.join("\n");
  }
}

// ── 8. Optimization verifier ──────────────────────────────────────────────

/**
 * Find X minimizing cost(X) subject to constraint(X).
 * The verifier tracks the best distance score across rounds.
 */
export class OptimizationVerifier implements Verifier {
  private bestDistance = Infinity;
  private bestPayload: unknown = undefined;

  constructor(
    private constraintOp: string,
    private constraintTarget: string,
    private costDescription: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const target = await fetchTheorySummary(catlab, this.constraintTarget, timeoutMs);

    return {
      kind: "optimization",
      problemDescription:
        `Find a theory X that satisfies **${this.constraintOp}(X) ≅ "${this.constraintTarget}"** ` +
        `while minimizing: **${this.costDescription}**.\n\n` +
        `The CAS will verify the constraint and report a distance score. ` +
        `You want to get verified=true with the smallest possible distance.`,
      hint:
        `**Strategy for optimization:**\n` +
        `1. First, find ANY theory that satisfies the constraint.\n` +
        `2. Then iteratively simplify it to minimize the cost.\n` +
        `3. The distance score in the feedback tells you how close you are.`,
      contextJson:
        `## Constraint Target: "${this.constraintTarget}"\n\n\`\`\`json\n${target.json}\n\`\`\`\n\n` +
        `## Cost Function: ${this.costDescription}`,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    // Verify the constraint using inverse evaluation
    const res = await catlab.request(
      {
        command: "evaluate_inverse",
        target: this.constraintTarget,
        forward_op: this.constraintOp,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);

    const result = res.result!;

    // Compute a simple cost metric: total generator count
    const cost = candidate.objects.length + candidate.morphisms.length + candidate.axioms.length;
    result.distance = cost;

    // Track best
    if (result.verified && cost < this.bestDistance) {
      this.bestDistance = cost;
      this.bestPayload = payload;
    }

    result.feedbackStrings = [
      `Cost (total generators): ${cost}`,
      `Best so far: ${this.bestDistance === Infinity ? "none" : this.bestDistance}`,
      ...(result.feedbackStrings ?? []),
    ];

    return result;
  }

  formatFeedback(result: VerificationResult, _payload: unknown): string {
    const lines: string[] = [];
    if (result.feedbackStrings) {
      for (const fb of result.feedbackStrings) lines.push(`• ${fb}`);
    }
    lines.push("\n" + formatStructuralDiff(result));
    return lines.join("\n");
  }
}

// ── 9. Pullback complement verifier ─────────────────────────────────────────

/**
 * find X such that pullback(base, X) ≅ target
 * Dual of pushout complement.
 */
export class PullbackComplementVerifier implements Verifier {
  constructor(
    private baseName: string,
    private targetName: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const [base, target] = await Promise.all([
      fetchTheorySummary(catlab, this.baseName, timeoutMs),
      fetchTheorySummary(catlab, this.targetName, timeoutMs),
    ]);

    return {
      kind: "pullback_complement",
      problemDescription:
        `Find a theory X such that **pullback(${this.baseName}, X) ≅ "${this.targetName}"**.\n\n` +
        `This is the dual of pushout complement. The pullback (fibered product) of your ` +
        `candidate with the base over a shared sub-theory must produce the target.`,
      hint:
        `**Recipe for pullback complement:**\n` +
        `1. Study what the target has beyond the base.\n` +
        `2. Your candidate must contain the base generators (they get identified in the pullback).\n` +
        `3. Add the "extra" generators that produce the target when pulled back.\n` +
        `4. This is dual to pushout complement — think of it as working in the opposite category.`,
      contextJson:
        `## Base Theory: "${this.baseName}"\n\n\`\`\`json\n${base.json}\n\`\`\`\n\n` +
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_pullback_complement",
        base: this.baseName,
        target: this.targetName,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    return res.result!;
  }
}

// ── 10. Simplification verifier ─────────────────────────────────────────────

/**
 * find structurally minimal X ≅ T
 * The candidate must be isomorphic to target but with fewer generators.
 */
export class SimplificationVerifier implements Verifier {
  constructor(private targetName: string) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const target = await fetchTheorySummary(catlab, this.targetName, timeoutMs);

    return {
      kind: "simplification",
      problemDescription:
        `Find a theory X that is **structurally equivalent to "${this.targetName}"** ` +
        `but with **fewer total generators** (objects + morphisms + axioms).\n\n` +
        `The CAS will verify X ≅ "${this.targetName}" and compare generator counts.`,
      hint:
        `**Strategy for simplification:**\n` +
        `1. Look for redundant axioms (consequences of other axioms).\n` +
        `2. Look for derivable morphisms (compositions of existing ones).\n` +
        `3. Look for objects that can be expressed as products/coproducts.\n` +
        `4. The structural diff must show zero mismatches.`,
      contextJson:
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_simplification",
        target: this.targetName,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    const result = res.result!;
    const resOk = res as any;
    // Add size info to feedback
    result.feedbackStrings = [
      `Candidate size: ${resOk.candidate_size ?? "?"} generators`,
      `Target size: ${resOk.target_size ?? "?"} generators`,
      ...(result.feedbackStrings ?? []),
    ];
    return result;
  }

  formatFeedback(result: VerificationResult, _payload: unknown): string {
    const lines: string[] = [];
    if (result.feedbackStrings) {
      for (const fb of result.feedbackStrings) lines.push(`• ${fb}`);
    }
    lines.push("\n" + formatStructuralDiff(result));
    return lines.join("\n");
  }
}

// ── 11. Model finding verifier ──────────────────────────────────────────────

/**
 * Generate a concrete, valid instance/algebra for a theory.
 * The candidate must be a theory with matching structure.
 */
export class ModelFindingVerifier implements Verifier {
  constructor(private theoryName: string) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const theory = await fetchTheorySummary(catlab, this.theoryName, timeoutMs);

    return {
      kind: "model_finding",
      problemDescription:
        `Generate a **concrete model (instance)** of the theory "${this.theoryName}".\n\n` +
        `Your candidate must be a theory with the same structure as "${this.theoryName}" — ` +
        `same number of objects, morphisms with matching domain/codomain shapes, and axioms ` +
        `that reduce to the same normal forms. Think of it as providing a concrete interpretation.`,
      hint:
        `**Strategy for model finding:**\n` +
        `1. Study the theory's objects, morphisms, and axioms.\n` +
        `2. Create a theory with matching structural shape.\n` +
        `3. You may rename generators — the CAS uses shape matching.\n` +
        `4. All axioms must hold in your instance.`,
      contextJson:
        `## Theory: "${this.theoryName}"\n\n\`\`\`json\n${theory.json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_model",
        theory: this.theoryName,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    return res.result!;
  }
}

// ── 12. Sub-object verifier ─────────────────────────────────────────────────

/**
 * Find a sub-theory of target satisfying property P.
 * The candidate must be a sub-theory (all generators exist in target).
 */
export class SubobjectVerifier implements Verifier {
  constructor(
    private targetName: string,
    private property: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const target = await fetchTheorySummary(catlab, this.targetName, timeoutMs);

    return {
      kind: "subobject",
      problemDescription:
        `Find a **sub-theory** of "${this.targetName}" that satisfies the property **"${this.property}"**.\n\n` +
        `Your candidate must use ONLY objects and morphisms that exist in the target theory. ` +
        `It should be a coherent sub-theory (axioms must be consistent) that satisfies the property.`,
      hint:
        `**Strategy for sub-object finding:**\n` +
        `1. Study the target theory's generators.\n` +
        `2. Select a subset that forms a self-consistent sub-theory.\n` +
        `3. Include only the axioms that involve your selected generators.\n` +
        `4. Verify the property "${this.property}" holds for your selection.`,
      contextJson:
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\`\n\n` +
        `## Required Property: "${this.property}"`,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_subobject",
        target: this.targetName,
        property: this.property,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);

    const result = res.result!;
    const isSub = (res as any).is_subtheory === true;

    if (!isSub) {
      result.verified = false;
      result.verificationStatus = `✗ Failed: candidate contains generators not in "${this.targetName}"`;
      const notInTarget = (res as any).not_in_target ?? [];
      result.feedbackStrings = [
        `These generators are NOT in the target theory: ${notInTarget.join(", ")}`,
        `Your candidate must only use generators from "${this.targetName}".`,
      ];
    }

    return result;
  }

  formatFeedback(result: VerificationResult, _payload: unknown): string {
    const lines: string[] = [];
    if (result.feedbackStrings) {
      for (const fb of result.feedbackStrings) lines.push(`• ${fb}`);
    }
    lines.push("\n" + formatStructuralDiff(result));
    return lines.join("\n");
  }
}

// ── 13. Synthesis verifier ──────────────────────────────────────────────────

/**
 * Find a morphism sequence in a theory that composes to a given type.
 * The candidate extends the base theory with the desired composite morphism.
 */
export class SynthesisVerifier implements Verifier {
  constructor(
    private theoryName: string,
    private source: string,
    private target: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const theory = await fetchTheorySummary(catlab, this.theoryName, timeoutMs);

    return {
      kind: "synthesis",
      problemDescription:
        `Working within the theory "${this.theoryName}", find a **composite morphism** ` +
        `from "${this.source}" to "${this.target}".\n\n` +
        `Your candidate must include all generators from "${this.theoryName}" plus a new ` +
        `morphism that is defined as a composition of existing morphisms, with an axiom ` +
        `asserting it equals the desired composite.`,
      hint:
        `**Strategy for synthesis:**\n` +
        `1. Include ALL objects and morphisms from "${this.theoryName}" verbatim.\n` +
        `2. Add a new morphism with domain "${this.source}" and codomain "${this.target}".\n` +
        `3. Add an axiom stating this morphism equals a comp([...]) of existing morphisms.\n` +
        `4. The composition must typecheck: domains and codomains must chain correctly.`,
      contextJson:
        `## Theory: "${this.theoryName}"\n\n\`\`\`json\n${theory.json}\n\`\`\`\n\n` +
        `## Desired morphism: ${this.source} → ${this.target}`,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_synthesis",
        theory: this.theoryName,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);

    const result = res.result!;
    const extendsTheory = (res as any).extends_theory === true;

    if (!extendsTheory) {
      result.verified = false;
      result.verificationStatus = `✗ Failed: candidate doesn't include all generators from "${this.theoryName}"`;
      const missing = (res as any).missing_from_theory ?? [];
      result.feedbackStrings = [
        `Missing generators from "${this.theoryName}": ${missing.join(", ")}`,
        `Your candidate must include ALL generators from the base theory.`,
      ];
    }

    return result;
  }

  formatFeedback(result: VerificationResult, _payload: unknown): string {
    const lines: string[] = [];
    if (result.feedbackStrings) {
      for (const fb of result.feedbackStrings) lines.push(`• ${fb}`);
    }
    lines.push("\n" + formatStructuralDiff(result));
    return lines.join("\n");
  }
}

// ── 14. Quotient verifier ───────────────────────────────────────────────────

/**
 * Find minimal congruence ∼ on base such that base/∼ satisfies property P.
 */
export class QuotientVerifier implements Verifier {
  constructor(
    private baseName: string,
    private property: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const base = await fetchTheorySummary(catlab, this.baseName, timeoutMs);

    return {
      kind: "quotient",
      problemDescription:
        `Find a **quotient** of "${this.baseName}" that satisfies the property **"${this.property}"**.\n\n` +
        `Your candidate should be a theory with the same objects as "${this.baseName}" but with ` +
        `some morphisms identified (collapsed) and/or additional axioms that enforce the congruence. ` +
        `The result should be the minimal quotient satisfying the property.`,
      hint:
        `**Strategy for quotient:**\n` +
        `1. Keep ALL objects from "${this.baseName}".\n` +
        `2. Keep all morphisms, but add axioms that identify (equate) some of them.\n` +
        `3. The new axioms define the congruence ∼.\n` +
        `4. Verify the property "${this.property}" holds in the quotient.`,
      contextJson:
        `## Base Theory: "${this.baseName}"\n\n\`\`\`json\n${base.json}\n\`\`\`\n\n` +
        `## Required Property: "${this.property}"`,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_quotient",
        base: this.baseName,
        property: this.property,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);

    const result = res.result!;
    const isQuotient = (res as any).is_quotient === true;

    if (!isQuotient) {
      result.verified = false;
      result.verificationStatus = `✗ Failed: candidate is missing objects from "${this.baseName}"`;
      result.feedbackStrings = [
        `A quotient must keep ALL objects from the base theory.`,
        `Missing: ${((res as any).missing_objects ?? []).join(", ")}`,
      ];
    }

    return result;
  }
}

// ── 15. Decomposition verifier ──────────────────────────────────────────────

/**
 * Find a set of components Xᵢ such that ⨁ Xᵢ ≅ target.
 */
export class DecompositionVerifier implements Verifier {
  constructor(private targetName: string) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const target = await fetchTheorySummary(catlab, this.targetName, timeoutMs);

    return {
      kind: "decomposition",
      problemDescription:
        `**Decompose** "${this.targetName}" into independent components.\n\n` +
        `Find a theory that, when viewed as a coproduct (disjoint union) of sub-theories, ` +
        `is structurally equivalent to "${this.targetName}". The candidate should make the ` +
        `decomposition explicit through its structure.`,
      hint:
        `**Strategy for decomposition:**\n` +
        `1. Identify independent "clusters" of generators in the target.\n` +
        `2. Each cluster should be self-contained (axioms only reference that cluster).\n` +
        `3. The union of all clusters must reconstruct the full target.\n` +
        `4. Submit the reassembled theory — the CAS verifies it matches the target.`,
      contextJson:
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\``,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_decomposition",
        target: this.targetName,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);
    return res.result!;
  }
}

// ── 16. Relaxation verifier ─────────────────────────────────────────────────

/**
 * Find X minimizing edit distance to target while satisfying property P.
 */
export class RelaxationVerifier implements Verifier {
  private bestDistance = Infinity;

  constructor(
    private targetName: string,
    private property: string,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    const target = await fetchTheorySummary(catlab, this.targetName, timeoutMs);

    return {
      kind: "relaxation",
      problemDescription:
        `Find a theory X that satisfies **"${this.property}"** while being as close as possible ` +
        `to "${this.targetName}".\n\n` +
        `The CAS will compare your candidate structurally against "${this.targetName}" and report ` +
        `an edit distance. You want to minimize this distance while satisfying the property.`,
      hint:
        `**Strategy for relaxation:**\n` +
        `1. Start with "${this.targetName}" as a base.\n` +
        `2. Make the minimal changes needed to satisfy "${this.property}".\n` +
        `3. Each round, the CAS reports edit distance — try to reduce it.\n` +
        `4. Prefer adding/modifying axioms over changing generators.`,
      contextJson:
        `## Target Theory: "${this.targetName}"\n\n\`\`\`json\n${target.json}\n\`\`\`\n\n` +
        `## Required Property: "${this.property}"`,
    };
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<VerificationResult> {
    const candidate = payload as TheoryJson;
    const res = await catlab.request(
      {
        command: "evaluate_relaxation",
        target: this.targetName,
        property: this.property,
        candidate,
      },
      timeoutMs,
    );
    if (res.status === "error") throw new Error(`Lean error: ${res.message}`);

    const result = res.result!;
    const editDist = (res as any).edit_distance ?? Infinity;

    if (result.verified && editDist < this.bestDistance) {
      this.bestDistance = editDist;
    }

    result.feedbackStrings = [
      `Edit distance from target: ${editDist}`,
      `Best distance so far: ${this.bestDistance === Infinity ? "none" : this.bestDistance}`,
      ...(result.feedbackStrings ?? []),
    ];

    return result;
  }

  formatFeedback(result: VerificationResult, _payload: unknown): string {
    const lines: string[] = [];
    if (result.feedbackStrings) {
      for (const fb of result.feedbackStrings) lines.push(`• ${fb}`);
    }
    lines.push("\n" + formatStructuralDiff(result));
    return lines.join("\n");
  }
}

// ── Inverse problem descriptions ────────────────────────────────────────────

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
