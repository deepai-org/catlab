/**
 * GenericSolver — LLM ↔ CAS feedback loop as an explicit state machine.
 *
 * The solver is fully verifier-agnostic. It treats the LLM's output as an
 * opaque JSON payload. The verifier defines the answer schema, the verification
 * logic, the feedback formatting, and the payload validation.
 *
 * States:
 *   GENERATING  — waiting for the LLM to produce a candidate payload
 *   VERIFYING   — waiting for the CAS to evaluate the payload
 *   SUCCESS     — terminal: CAS confirmed verified = true
 *   EXHAUSTED   — terminal: maxRounds completed without verification
 */

import Anthropic from "@anthropic-ai/sdk";
import type { CatlabClient } from "./client";
import type { LLMClient } from "./llm";
import { formatStructuralDiff, validateTheoryPayload } from "./llm";
import type {
  ProblemSpec,
  VerificationResult,
  Verifier,
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
  if (err instanceof Error && err.message.startsWith("LLM did not output")) {
    return "PARSE_ERROR";
  }
  return "RETRYABLE";
}

function classifyLeanError(err: unknown): ErrorKind {
  if (err instanceof Error) {
    if (err.message.includes("not found")) return "FATAL";
    if (err.message.includes("timed out"))  return "RETRYABLE";
    if (err.message.includes("exited"))     return "RETRYABLE";
  }
  return "RETRYABLE";
}

// ── Backoff ───────────────────────────────────────────────────────────────────

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function backoffMs(attempt: number): number {
  return Math.min(1_000 * 2 ** attempt, 30_000);
}

// ── Helpers ───────────────────────────────────────────────────────────────────

function tag(phase: Phase, round: number, maxRounds: number): string {
  return `[solver:${phase}:round ${round}/${maxRounds}]`;
}

/** Summarize a payload for logging (works for TheoryJson or any object with a name). */
function summarizePayload(payload: unknown): string {
  if (typeof payload !== "object" || payload === null) return "(unknown)";
  const p = payload as Record<string, unknown>;
  const name = typeof p.name === "string" ? p.name : "?";
  const parts: string[] = [`"${name}"`];
  if (Array.isArray(p.objects)) parts.push(`${p.objects.length} obj`);
  if (Array.isArray(p.morphisms)) parts.push(`${p.morphisms.length} mor`);
  if (Array.isArray(p.axioms)) parts.push(`${p.axioms.length} ax`);
  return parts.join(" / ");
}

// ── GenericSolver ─────────────────────────────────────────────────────────────

export class GenericSolver {
  constructor(
    private catlab: CatlabClient,
    private llm: LLMClient,
    private verifier: Verifier,
  ) {}

  async solve(options: SolverOptions): Promise<SolverResult> {
    const maxRounds     = options.maxRounds     ?? 5;
    const maxLLMRetries = options.maxLLMRetries ?? 3;
    const maxLeanRetries= options.maxLeanRetries ?? 2;
    const timeoutMs     = options.leanTimeoutMs  ?? 30_000;

    const history: HistoryEntry[] = [];

    // ── Preflight: get problem spec from verifier ───────────────────────
    console.error(`[solver:INIT] Running verifier preflight...`);
    const spec = await this.verifier.preflight(this.catlab, timeoutMs);
    if (options.stylePrompt) {
      spec.stylePrompt = options.stylePrompt;
    }
    console.error(
      `[solver:INIT] Problem type: ${spec.kind}  ` +
      `maxRounds=${maxRounds} llmRetries=${maxLLMRetries} leanRetries=${maxLeanRetries}`,
    );

    // Resolve feedback formatter and payload validator from verifier
    const formatFeedback = this.verifier.formatFeedback?.bind(this.verifier)
      ?? ((result: VerificationResult, _payload: unknown) => formatStructuralDiff(result));
    const validatePayload = this.verifier.validatePayload?.bind(this.verifier)
      ?? validateTheoryPayload;

    // ── State machine variables ───────────────────────────────────────────
    let phase: Phase = "GENERATING";
    let round = 0;
    let payload: unknown | undefined;
    let lastResult: VerificationResult | undefined;

    // ── Main loop ─────────────────────────────────────────────────────────
    while (phase !== "SUCCESS" && phase !== "EXHAUSTED") {

      // ════════════════════════════════════════════════════════════════════
      //  GENERATING phase
      // ════════════════════════════════════════════════════════════════════
      if (phase === "GENERATING") {
        const isRefine = (payload !== undefined && lastResult !== undefined);
        console.error(
          `\n${"─".repeat(60)}\n` +
          `${tag("GENERATING", round + 1, maxRounds)} ` +
          (isRefine ? "refining with feedback" : "initial proposal"),
        );

        let llmAttempt = 0;
        let generatedPayload: unknown | undefined;

        while (llmAttempt <= maxLLMRetries) {
          try {
            if (!isRefine || generatedPayload === undefined && llmAttempt > 0) {
              generatedPayload = await this.llm.generateInitial(spec);
            } else {
              const feedbackText = formatFeedback(lastResult!, payload);
              generatedPayload = await this.llm.refineWithFeedback(
                spec, feedbackText, payload!, round + 1,
              );
            }
            // Validate the payload shape
            validatePayload(generatedPayload);
            break;

          } catch (err) {
            const kind = classifyLLMError(err);
            const msg  = err instanceof Error ? err.message.split("\n")[0] : String(err);

            if (kind === "FATAL") {
              console.error(
                `${tag("GENERATING", round + 1, maxRounds)} FATAL LLM error: ${msg}`,
              );
              throw err;
            }

            llmAttempt++;
            if (llmAttempt > maxLLMRetries) {
              console.error(
                `${tag("GENERATING", round + 1, maxRounds)} ` +
                `LLM retries exhausted (${maxLLMRetries}). Last error: ${msg}`,
              );
              phase = "EXHAUSTED";
              break;
            }

            if (kind === "PARSE_ERROR") {
              const fullMsg = err instanceof Error ? err.message : String(err);
              console.error(
                `${tag("GENERATING", round + 1, maxRounds)} ` +
                `PARSE_ERROR (attempt ${llmAttempt}/${maxLLMRetries}) — retrying fresh\n  ${fullMsg}`,
              );
              payload = undefined;
              lastResult = undefined;
            } else {
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

        payload = generatedPayload!;
        console.error(
          `${tag("GENERATING", round + 1, maxRounds)} ` +
          `candidate ${summarizePayload(payload)}`,
        );
        // Print the full candidate JSON so we can inspect what the LLM proposed
        console.error(`\n── candidate JSON ──\n${JSON.stringify(payload, null, 2)}\n── end candidate ──`);
        phase = "VERIFYING";
      }

      // ════════════════════════════════════════════════════════════════════
      //  VERIFYING phase
      // ════════════════════════════════════════════════════════════════════
      if (phase === "VERIFYING") {
        let leanAttempt = 0;
        let verifyResult: VerificationResult | undefined;

        while (leanAttempt <= maxLeanRetries) {
          try {
            verifyResult = await this.verifier.verify(
              this.catlab, payload!, timeoutMs,
            );
            break;

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
              payload    = undefined;
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

        if (phase === "GENERATING") continue;

        round++;
        lastResult = verifyResult!;
        history.push({ round, payload: payload!, result: lastResult });

        console.error(
          `${tag("VERIFYING", round, maxRounds)} ${lastResult.verificationStatus}`,
        );
        if (lastResult.distance !== undefined)
          console.error(`  • distance: ${lastResult.distance}`);
        if (lastResult.missingSignatures.length > 0)
          console.error(`  • ${lastResult.missingSignatures.length} missing signature(s)`);
        if (lastResult.unmappedObjects.length > 0)
          console.error(`  • ${lastResult.unmappedObjects.length} unmapped object(s)`);
        if (lastResult.axiomViolations.length > 0)
          console.error(`  • ${lastResult.axiomViolations.length} axiom violation(s)`);
        if (lastResult.feedbackStrings && lastResult.feedbackStrings.length > 0)
          console.error(`  • ${lastResult.feedbackStrings.length} feedback message(s)`);

        // Print the full feedback that will be sent to the LLM
        if (!lastResult.verified) {
          const feedbackText = formatFeedback(lastResult, payload);
          console.error(`\n── feedback to LLM ──\n${feedbackText}\n── end feedback ──`);
        }

        if (lastResult.verified) {
          const name = (payload as Record<string, unknown>)?.name ?? "solution";
          console.error(`\n✅ ${tag("SUCCESS", round, maxRounds)} "${name}"`);
          phase = "SUCCESS";
        } else if (round >= maxRounds) {
          console.error(`\n❌ [solver:EXHAUSTED] max rounds reached`);
          phase = "EXHAUSTED";
        } else {
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
        console.error(`  Best attempt: ${summarizePayload(last.payload)}`);
        console.error(`  Final status: ${last.result.verificationStatus}`);
      }
    }

    // ── Post-solve reflection (opt-in via options) ────────────────────────
    let reflection: string | undefined;
    if (options.reflect && (success || history.length > 0)) {
      try {
        console.error(`\n[solver:REFLECT] Asking LLM for prompt improvement suggestions...`);
        reflection = await this.llm.reflectOnSolve(spec, round, history);
        console.error(`[solver:REFLECT] Suggestions:\n${reflection}\n`);
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        console.error(`[solver:REFLECT] Reflection failed (non-fatal): ${msg}`);
      }
    }

    return {
      success,
      rounds: round,
      winner:      success ? payload : undefined,
      finalResult: lastResult,
      history,
      reflection,
    };
  }
}

