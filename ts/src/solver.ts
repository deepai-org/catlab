/**
 * InverseProblemSolver — the main LLM ↔ CAS feedback loop.
 *
 * Implements the three-step architecture:
 *   1. LLM proposes a candidate Theory JSON
 *   2. Lean CAS applies forwardOp and diffs against the target
 *   3. If verified: done. If not: format the diff and go to 1.
 *
 * The loop terminates on either success or maxRounds exhaustion.
 * All intermediate results are recorded in history for debugging.
 */

import type { CatlabClient } from "./client";
import type { LLMClient } from "./llm";
import type { TheoryJson, VerificationResult, SolverOptions, SolverResult } from "./types";

export class InverseProblemSolver {
  constructor(
    private catlab: CatlabClient,
    private llm: LLMClient,
  ) {}

  /**
   * Run the inverse problem loop for the given target theory.
   *
   * @param targetName  Name of the target theory in the CatLab registry
   *                    (e.g. "Monoid", "Ring", "Category")
   * @param options     Solver options: forwardOp, stylePrompt, maxRounds, etc.
   */
  async solve(targetName: string, options: SolverOptions): Promise<SolverResult> {
    const maxRounds = options.maxRounds ?? 5;
    const timeoutMs = options.leanTimeoutMs ?? 30_000;
    const history: SolverResult["history"] = [];

    // ── Fetch the target theory from the CAS to show the LLM its structure ──
    console.error(`[solver] Fetching target theory "${targetName}" from CAS...`);
    const summaryRes = await this.catlab.requestOrThrow(
      { command: "summary", theory: targetName },
      timeoutMs,
    );
    const targetJson = summaryRes.theory
      ? JSON.stringify(summaryRes.theory, null, 2)
      : `(no structure available — name: ${targetName})`;

    console.error(`[solver] Target theory loaded. Starting ${maxRounds}-round loop.`);
    console.error(`[solver] Forward operator: ${options.forwardOp}`);
    if (options.stylePrompt) console.error(`[solver] Style: ${options.stylePrompt}`);

    let candidate: TheoryJson | undefined;
    let lastResult: VerificationResult | undefined;

    for (let round = 1; round <= maxRounds; round++) {
      console.error(`\n${"─".repeat(60)}`);
      console.error(`[solver] Round ${round}/${maxRounds}`);

      // ── Step A: Generate candidate ──────────────────────────────────────
      console.error(`[solver] Calling Claude Opus 4.6 (adaptive thinking)...`);
      try {
        if (round === 1 || !candidate || !lastResult) {
          candidate = await this.llm.generateInitial(
            targetName,
            targetJson,
            options.forwardOp,
            options.stylePrompt,
          );
        } else {
          candidate = await this.llm.refineWithDiff(
            targetName,
            lastResult,
            candidate,
            options.forwardOp,
            round,
          );
        }
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        console.error(`[solver] LLM error on round ${round}: ${msg}`);
        // If the LLM fails to produce valid JSON, log and continue
        if (round < maxRounds) {
          console.error(`[solver] Retrying with a fresh prompt...`);
          candidate = undefined; // force re-generation from scratch next round
          continue;
        }
        break;
      }

      console.error(`[solver] Candidate: "${candidate.name}" ` +
        `(${candidate.objects.length} objs, ${candidate.morphisms.length} morphs, ${candidate.axioms.length} axioms)`);

      // ── Step B: Verify with the CAS ─────────────────────────────────────
      console.error(`[solver] Sending to Lean CAS for verification...`);
      const leanRes = await this.catlab.request(
        {
          command: "evaluate_inverse",
          target: targetName,
          forward_op: options.forwardOp,
          candidate,
        },
        timeoutMs,
      );

      if (leanRes.status === "error") {
        console.error(`[solver] Lean error: ${leanRes.message}`);
        // A Lean error (e.g. malformed JSON escaping through the NDJSON layer)
        // is different from a verification failure — it means we sent something
        // Lean couldn't process. Log and try next round.
        lastResult = undefined;
        continue;
      }

      const result = leanRes.result!;
      lastResult = result;
      history.push({ round, candidate, result });

      console.error(`[solver] Verification: ${result.verificationStatus}`);
      if (result.missingSignatures.length > 0)
        console.error(`  • ${result.missingSignatures.length} missing signature(s)`);
      if (result.unmappedObjects.length > 0)
        console.error(`  • ${result.unmappedObjects.length} unmapped object(s)`);
      if (result.axiomViolations.length > 0)
        console.error(`  • ${result.axiomViolations.length} axiom violation(s)`);

      // ── Step C: Victory check ────────────────────────────────────────────
      if (result.verified) {
        console.error(`\n✅ [solver] VERIFIED on round ${round}!`);
        console.error(`   Winner: "${candidate.name}"`);
        return {
          success: true,
          rounds: round,
          winner: candidate,
          finalResult: result,
          history,
        };
      }

      console.error(`[solver] Not verified. Formatting diff for round ${round + 1}...`);
    }

    console.error(`\n❌ [solver] Max rounds (${maxRounds}) reached without verification.`);
    return {
      success: false,
      rounds: maxRounds,
      finalResult: lastResult,
      history,
    };
  }
}
