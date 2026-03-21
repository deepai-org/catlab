/**
 * Two-Tier Verification Pipeline
 *
 * Wraps any existing Verifier with an optional Lean/Mathlib deep verification pass.
 *
 * Tier 1 (Fast Path): Existing CAS structural checks (ms)
 *   - Dangling references, duplicate names, shape mismatches
 *   - If this fails, exit immediately with structural feedback
 *
 * Tier 2 (Deep Path): Lean/Mathlib elaboration (seconds)
 *   - Type-checks morphism domains/codomains against Mathlib
 *   - Attempts to prove axioms via aesop_cat
 *   - Returns semantic errors or unverified-axiom warnings
 *
 * The LLM never waits for Lean compilation on a structurally broken theory.
 */

import type { CatlabClient } from "./client";
import type {
  ProblemSpec,
  Verifier,
  VerificationResult,
  TheoryJson,
} from "./types";
import {
  elaborate,
  formatElaborationFeedback,
  type ElaborationOptions,
  type ElaborationResult,
} from "./lean-elaborator";

export interface DeepVerifierOptions {
  /** Enable deep (Lean/Mathlib) verification. Default: false */
  deepVerification: boolean;
  /** Project root for Lean compilation */
  projectRoot: string;
  /** Lean compilation timeout in ms. Default: 60000 */
  leanTimeoutMs?: number;
  /** Keep generated .lean files for debugging. Default: false */
  keepLeanFiles?: boolean;
}

/**
 * Extended VerificationResult with deep verification data.
 */
export interface DeepVerificationResult extends VerificationResult {
  /** Deep verification result (only present when deep path runs) */
  elaboration?: ElaborationResult;
  /** Whether the deep path was skipped (fast path failed or deep disabled) */
  deepSkipped: boolean;
  /** Overall verification tier that produced the result */
  tier: "fast" | "deep";
}

/**
 * Wraps an existing Verifier with two-tier verification.
 */
export class DeepVerifier implements Verifier {
  constructor(
    private inner: Verifier,
    private opts: DeepVerifierOptions,
  ) {}

  async preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec> {
    return this.inner.preflight(catlab, timeoutMs);
  }

  async verify(
    catlab: CatlabClient,
    payload: unknown,
    timeoutMs: number,
  ): Promise<DeepVerificationResult> {
    // ── Tier 1: Fast path (existing CAS) ─────────────────────────────────
    const fastResult = await this.inner.verify(catlab, payload, timeoutMs);

    if (!fastResult.verified) {
      // Fast path failed — don't waste time on Lean compilation
      return {
        ...fastResult,
        deepSkipped: true,
        tier: "fast",
      };
    }

    // ── Routing: skip deep path for higher categories (Phase 2: Rzk) ─────
    const theory = payload as TheoryJson;
    if (!this.opts.deepVerification) {
      return {
        ...fastResult,
        deepSkipped: true,
        tier: "fast",
      };
    }

    // ── Tier 2: Deep path (Lean/Mathlib) ─────────────────────────────────
    const elabOpts: ElaborationOptions = {
      projectRoot: this.opts.projectRoot,
      timeoutMs: this.opts.leanTimeoutMs ?? 60000,
      keepFile: this.opts.keepLeanFiles ?? false,
    };

    const elaboration = await elaborate(theory, elabOpts);

    // Merge results: fast path passed, now augment with deep findings
    const deepResult: DeepVerificationResult = {
      ...fastResult,
      elaboration,
      deepSkipped: false,
      tier: "deep",
    };

    if (elaboration.status === "semantic_error") {
      // Deep path found type errors — override the fast path's success
      deepResult.verified = false;
      deepResult.verificationStatus = "✗ Deep verification failed: " +
        elaboration.errors
          .filter(e => e.severity === "fatal")
          .map(e => e.message)
          .join("; ");
    } else if (elaboration.status === "unverified_axiom") {
      // Well-typed but unproven axioms — keep verified=true but annotate
      deepResult.verificationStatus = "⚠ Verified with unproven axioms";
    } else if (elaboration.status === "success") {
      deepResult.verificationStatus = "✓ Fully verified by Lean/Mathlib";
    }

    return deepResult;
  }

  formatFeedback?(result: VerificationResult, payload: unknown): string {
    const deep = result as DeepVerificationResult;

    // Start with the inner verifier's feedback
    const baseFeedback = this.inner.formatFeedback
      ? this.inner.formatFeedback(result, payload)
      : defaultFeedback(result);

    // Append deep verification feedback if available
    if (deep.elaboration && !deep.deepSkipped) {
      return baseFeedback + "\n\n── Deep Verification ──\n" +
        formatElaborationFeedback(deep.elaboration);
    }

    return baseFeedback;
  }

  validatePayload?(payload: unknown): void {
    if (this.inner.validatePayload) {
      this.inner.validatePayload(payload);
    }
  }
}

function defaultFeedback(result: VerificationResult): string {
  if (result.verified) return "✓ Structural verification passed.";
  const parts: string[] = ["✗ Structural verification failed."];
  if (result.missingSignatures.length > 0) {
    parts.push(`Missing morphisms: ${result.missingSignatures.map(s => s.sourceName).join(", ")}`);
  }
  if (result.unmappedObjects.length > 0) {
    parts.push(`Unmapped objects: ${result.unmappedObjects.join(", ")}`);
  }
  if (result.axiomViolations.length > 0) {
    parts.push(`Axiom violations: ${result.axiomViolations.map(v => v.sourceAxiom).join(", ")}`);
  }
  return parts.join("\n");
}
