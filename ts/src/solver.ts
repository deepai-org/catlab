/**
 * InverseProblemSolver — LLM ↔ CAS feedback loop as an explicit state machine.
 *
 * States:
 *   GENERATING  — waiting for the LLM to produce a candidate Theory JSON
 *   VERIFYING   — waiting for the Lean CAS to evaluate the candidate
 *   SUCCESS     — terminal: Lean confirmed verified = true
 *   EXHAUSTED   — terminal: maxRounds completed without verification
 *
 * Round discipline:
 *   A "round" is one complete GENERATING → VERIFYING cycle.
 *   Retries within a phase (rate limits, network blips, transient Lean errors)
 *   do NOT advance the round counter. The counter only increments when Lean
 *   returns a real VerificationResult (whether it passes or not).
 *
 * Error classification:
 *   FATAL       — do not retry; fail the entire run (auth errors, wrong config)
 *   RETRYABLE   — retry with exponential backoff (rate limits, network, timeouts)
 *   PARSE_ERROR — retry fresh generation (LLM produced non-JSON output)
 */

import Anthropic from "@anthropic-ai/sdk";
import type { CatlabClient } from "./client";
import type { LLMClient } from "./llm";
import type {
  TheoryJson,
  VerificationResult,
  SolverOptions,
  SolverResult,
  HistoryEntry,
} from "./types";

// ── State type ────────────────────────────────────────────────────────────────

type Phase = "GENERATING" | "VERIFYING" | "SUCCESS" | "EXHAUSTED";

// ── Error classification ──────────────────────────────────────────────────────

type ErrorKind = "FATAL" | "RETRYABLE" | "PARSE_ERROR";

function classifyLLMError(err: unknown): ErrorKind {
  if (err instanceof Anthropic.AuthenticationError) return "FATAL";
  if (err instanceof Anthropic.PermissionDeniedError) return "FATAL";
  if (err instanceof Anthropic.RateLimitError)        return "RETRYABLE";
  if (err instanceof Anthropic.APIConnectionError)    return "RETRYABLE";
  if (err instanceof Anthropic.InternalServerError)   return "RETRYABLE";
  // JSON parse failures from extractTheoryJson are plain Errors
  if (err instanceof Error && err.message.startsWith("LLM did not output")) {
    return "PARSE_ERROR";
  }
  return "RETRYABLE"; // unknown errors: give it another shot
}

function classifyLeanError(err: unknown): ErrorKind {
  if (err instanceof Error) {
    // "Theory '...' not found" is a config error, not a transient one
    if (err.message.includes("not found")) return "FATAL";
    // Timeouts and process errors are retryable
    if (err.message.includes("timed out"))  return "RETRYABLE";
    if (err.message.includes("exited"))     return "RETRYABLE";
  }
  return "RETRYABLE";
}

// ── Backoff ───────────────────────────────────────────────────────────────────

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/** Exponential backoff: attempt 0 = 1s, 1 = 2s, 2 = 4s, capped at 30s. */
function backoffMs(attempt: number): number {
  return Math.min(1_000 * 2 ** attempt, 30_000);
}

// ── Helpers ───────────────────────────────────────────────────────────────────

function tag(phase: Phase, round: number, maxRounds: number): string {
  return `[solver:${phase}:round ${round}/${maxRounds}]`;
}

// ── InverseProblemSolver ──────────────────────────────────────────────────────

export class InverseProblemSolver {
  constructor(
    private catlab: CatlabClient,
    private llm: LLMClient,
  ) {}

  async solve(targetName: string, options: SolverOptions): Promise<SolverResult> {
    const maxRounds     = options.maxRounds     ?? 5;
    const maxLLMRetries = options.maxLLMRetries ?? 3;
    const maxLeanRetries= options.maxLeanRetries ?? 2;
    const timeoutMs     = options.leanTimeoutMs  ?? 30_000;

    const history: HistoryEntry[] = [];

    // ── Preflight: fetch target theory structure ──────────────────────────
    console.error(`[solver:INIT] Fetching "${targetName}" from CAS...`);
    const summaryRes = await this.catlab.requestOrThrow(
      { command: "summary", theory: targetName },
      timeoutMs,
    );
    const targetJson = summaryRes.theory
      ? JSON.stringify(summaryRes.theory, null, 2)
      : `(name: ${targetName})`;
    console.error(
      `[solver:INIT] Target loaded. ` +
      `maxRounds=${maxRounds} llmRetries=${maxLLMRetries} leanRetries=${maxLeanRetries}`,
    );
    console.error(`[solver:INIT] forward_op=${options.forwardOp}${
      options.stylePrompt ? `  style="${options.stylePrompt}"` : ""
    }`);

    // ── State machine variables ───────────────────────────────────────────
    let phase: Phase = "GENERATING";
    let round = 0;
    let candidate: TheoryJson | undefined;
    let lastResult: VerificationResult | undefined;

    // ── Main loop ─────────────────────────────────────────────────────────
    while (phase !== "SUCCESS" && phase !== "EXHAUSTED") {

      // ════════════════════════════════════════════════════════════════════
      //  GENERATING phase
      //  Retry loop: retries stay in GENERATING, never advance the round.
      // ════════════════════════════════════════════════════════════════════
      if (phase === "GENERATING") {
        const isRefine = (candidate !== undefined && lastResult !== undefined);
        console.error(
          `\n${"─".repeat(60)}\n` +
          `${tag("GENERATING", round + 1, maxRounds)} ` +
          (isRefine ? "refining with diff" : "initial proposal"),
        );

        let llmAttempt = 0;
        let generatedCandidate: TheoryJson | undefined;

        while (llmAttempt <= maxLLMRetries) {
          try {
            if (!isRefine || generatedCandidate === undefined && llmAttempt > 0) {
              // Fresh generation: round 1, or after a PARSE_ERROR clears the candidate
              generatedCandidate = await this.llm.generateInitial(
                targetName, targetJson, options.forwardOp, options.stylePrompt,
              );
            } else {
              generatedCandidate = await this.llm.refineWithDiff(
                targetName, lastResult!, candidate!, options.forwardOp, round + 1,
              );
            }
            break; // success → exit retry loop

          } catch (err) {
            const kind = classifyLLMError(err);
            const msg  = err instanceof Error ? err.message.split("\n")[0] : String(err);

            if (kind === "FATAL") {
              console.error(
                `${tag("GENERATING", round + 1, maxRounds)} FATAL LLM error: ${msg}`,
              );
              throw err; // propagate immediately — nothing to retry
            }

            llmAttempt++;
            if (llmAttempt > maxLLMRetries) {
              console.error(
                `${tag("GENERATING", round + 1, maxRounds)} ` +
                `LLM retries exhausted (${maxLLMRetries}). Last error: ${msg}`,
              );
              // Treat as EXHAUSTED — we can't make progress without a candidate
              phase = "EXHAUSTED";
              break;
            }

            if (kind === "PARSE_ERROR") {
              // LLM produced non-JSON: retry fresh (not refine) — it may have
              // confused itself trying to fix the diff.
              // Log the full message (not just line 1) so we can see the preview.
              const fullMsg = err instanceof Error ? err.message : String(err);
              console.error(
                `${tag("GENERATING", round + 1, maxRounds)} ` +
                `PARSE_ERROR (attempt ${llmAttempt}/${maxLLMRetries}) — retrying fresh\n  ${fullMsg}`,
              );
              candidate = undefined; // force fresh generation on next attempt
              lastResult = undefined;
            } else {
              // RETRYABLE: rate limit or network — back off and retry same prompt
              const delay = backoffMs(llmAttempt - 1);
              console.error(
                `${tag("GENERATING", round + 1, maxRounds)} ` +
                `${kind} (attempt ${llmAttempt}/${maxLLMRetries}) — backing off ${delay}ms: ${msg}`,
              );
              await sleep(delay);
            }
          }
        }

        if (phase === "EXHAUSTED") break;

        // We have a valid candidate — transition to VERIFYING
        candidate = generatedCandidate!;
        console.error(
          `${tag("GENERATING", round + 1, maxRounds)} ` +
          `candidate "${candidate.name}" ` +
          `(${candidate.objects.length} obj / ${candidate.morphisms.length} mor / ${candidate.axioms.length} ax)`,
        );
        phase = "VERIFYING";
      }

      // ════════════════════════════════════════════════════════════════════
      //  VERIFYING phase
      //  Retry loop: retries stay in VERIFYING, never advance the round.
      //  The round counter increments only when Lean returns a real result.
      // ════════════════════════════════════════════════════════════════════
      if (phase === "VERIFYING") {
        let leanAttempt = 0;
        let verifyResult: VerificationResult | undefined;

        while (leanAttempt <= maxLeanRetries) {
          try {
            const leanRes = await this.catlab.request(
              {
                command: "evaluate_inverse",
                target: targetName,
                forward_op: options.forwardOp,
                candidate: candidate!,
              },
              timeoutMs,
            );

            if (leanRes.status === "error") {
              // Lean returned a well-formed error response (e.g. bad theory structure)
              // This is a *soft* error — the theory was malformed, not a crash.
              // Treat it like a PARSE_ERROR: retry with fresh LLM generation.
              console.error(
                `${tag("VERIFYING", round + 1, maxRounds)} ` +
                `Lean soft error: ${leanRes.message}`,
              );
              // Force fresh generation on next round
              candidate  = undefined;
              lastResult = undefined;
              phase = "GENERATING";
              break;
            }

            verifyResult = leanRes.result!;
            break; // success → exit retry loop

          } catch (err) {
            const kind = classifyLeanError(err);
            const msg  = err instanceof Error ? err.message.split("\n")[0] : String(err);

            if (kind === "FATAL") {
              console.error(
                `${tag("VERIFYING", round + 1, maxRounds)} FATAL Lean error: ${msg}`,
              );
              throw err;
            }

            leanAttempt++;
            if (leanAttempt > maxLeanRetries) {
              console.error(
                `${tag("VERIFYING", round + 1, maxRounds)} ` +
                `Lean retries exhausted (${maxLeanRetries}). Last error: ${msg}`,
              );
              // Skip this candidate — go back to GENERATING for a fresh one
              candidate  = undefined;
              lastResult = undefined;
              phase = "GENERATING";
              break;
            }

            const delay = backoffMs(leanAttempt - 1);
            console.error(
              `${tag("VERIFYING", round + 1, maxRounds)} ` +
              `${kind} (attempt ${leanAttempt}/${maxLeanRetries}) — backing off ${delay}ms`,
            );
            await sleep(delay);
          }
        }

        // If Lean retries sent us back to GENERATING, continue without incrementing round
        if (phase === "GENERATING") continue;

        // A real VerificationResult arrived — this counts as a completed round
        round++;
        lastResult = verifyResult!;
        history.push({ round, candidate: candidate!, result: lastResult });

        console.error(
          `${tag("VERIFYING", round, maxRounds)} ${lastResult.verificationStatus}`,
        );
        if (lastResult.missingSignatures.length > 0)
          console.error(`  • ${lastResult.missingSignatures.length} missing signature(s)`);
        if (lastResult.unmappedObjects.length > 0)
          console.error(`  • ${lastResult.unmappedObjects.length} unmapped object(s)`);
        if (lastResult.axiomViolations.length > 0)
          console.error(`  • ${lastResult.axiomViolations.length} axiom violation(s)`);

        if (lastResult.verified) {
          console.error(`\n✅ ${tag("SUCCESS", round, maxRounds)} "${candidate!.name}"`);
          phase = "SUCCESS";
        } else if (round >= maxRounds) {
          console.error(`\n❌ [solver:EXHAUSTED] max rounds reached`);
          phase = "EXHAUSTED";
        } else {
          // More rounds remain — go back to GENERATING with the diff
          phase = "GENERATING";
        }
      }
    }

    // ── Return result ─────────────────────────────────────────────────────
    const success = phase === "SUCCESS";
    if (!success) {
      console.error(
        `[solver:EXHAUSTED] Completed ${round} verification round(s) without success.`,
      );
      if (history.length > 0) {
        const last = history[history.length - 1];
        console.error(`  Best attempt: "${last.candidate.name}"`);
        console.error(`  Final status: ${last.result.verificationStatus}`);
      }
    }

    // ── Post-solve reflection ──────────────────────────────────────────────
    let reflection: string | undefined;
    if (success || history.length > 0) {
      try {
        console.error(`\n[solver:REFLECT] Asking LLM for prompt improvement suggestions...`);
        reflection = await this.llm.reflectOnSolve(
          targetName, options.forwardOp, round, history,
        );
        console.error(`[solver:REFLECT] Suggestions:\n${reflection}\n`);
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        console.error(`[solver:REFLECT] Reflection failed (non-fatal): ${msg}`);
      }
    }

    return {
      success,
      rounds: round,
      winner:      success ? candidate : undefined,
      finalResult: lastResult,
      history,
      reflection,
    };
  }
}
