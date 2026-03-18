/**
 * Wire types matching the Lean NDJSON contract in Catlab/Repl/Protocol.lean.
 * These are 1:1 with what the Lean server sends and receives.
 */

// ── Expr JSON (tagged-union, single-key objects) ──────────────────────────────
// "unit" | "terminal" | "initial"  → Expr constants
// "X"                              → Expr.atom (bare string shorthand)
// { "atom": "X" }                  → Expr.atom
// { "comp": [e1, e2] }            → Expr.comp e1 e2
// etc.
export type ExprJson =
  | string
  | { atom: string }
  | { comp: [ExprJson, ExprJson] }
  | { tensor: [ExprJson, ExprJson] }
  | { prod: [ExprJson, ExprJson] }
  | { hom: [ExprJson, ExprJson] }
  | { coprod: [ExprJson, ExprJson] }
  | { id: ExprJson };

// ── Theory JSON ───────────────────────────────────────────────────────────────

export interface ObjectJson {
  name: string;
  description?: string;
}

export interface MorphismJson {
  name: string;
  domain: ExprJson;
  codomain: ExprJson;
  description?: string;
}

export interface AxiomJson {
  name: string;
  lhs: ExprJson;
  rhs: ExprJson;
  description?: string;
}

export interface TheoryJson {
  name: string;
  /** Doctrine string, e.g. "MonoidalCategory", "Category", "LawvereTheory" */
  doctrine: string;
  objects: ObjectJson[];
  morphisms: MorphismJson[];
  axioms: AxiomJson[];
}

// ── VerificationResult ──────────────────────────────────────────────────────────
// Generic feedback from the CAS. Specific fields (missingSignatures, etc.) are
// present for structural-equivalence problems but optional in general.

export interface MissingSignature {
  /** Position-normalized domain, e.g. "§0" or "(§0,§0)" */
  domainShape: string;
  /** Position-normalized codomain */
  codomainShape: string;
  /** Original name in the target theory (for human-readable feedback) */
  sourceName: string;
}

export interface AxiomViolation {
  sourceAxiom: string;
  /** "✓ Success" | "✗ Failed: ..." | "⏱ Timeout at depth N" */
  status: string;
  lhsReduced: string;
  rhsReduced: string;
  depthUsed: number;
}

export interface VerificationResult {
  verified: boolean;
  candidateName: string;
  /** "✓ Success" | "✗ Failed: ..." | "⏱ Timeout at depth N" */
  verificationStatus: string;
  /** Structural-equivalence specific fields (optional for generic problems) */
  missingSignatures: MissingSignature[];
  unmappedObjects: string[];
  axiomViolations: AxiomViolation[];
  /** Generic feedback strings from the CAS (for non-structural problems) */
  feedbackStrings?: string[];
  /** Numeric distance/score (0 = perfect match, higher = worse). Used as gradient signal. */
  distance?: number;
}

// ── NDJSON Request types ──────────────────────────────────────────────────────

export type CatlabCommand =
  | { command: "list_theories" }
  | { command: "summary"; theory: string }
  | { command: "validate"; theory: string }
  | { command: "apply_operator"; operator: string; theory: string }
  | { command: "compute_pushout"; theory1: string; theory2: string; base: string }
  | {
      command: "evaluate_inverse";
      target: string;
      forward_op: string;
      candidate: TheoryJson;
    }
  | {
      command: "solve_inverse";
      target: string;
      forward_op: string;
      candidates: TheoryJson[];
    }
  | {
      command: "evaluate_pushout_complement";
      base: string;
      target: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_extension";
      base: string;
      property: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_multi_objective";
      objectives: Array<{ target: string; forward_op: string }>;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_fixed_point";
      forward_op: string;
      candidate: TheoryJson;
    }
  | {
      /** Generic evaluate: verifier packs the full payload, Lean handler unpacks it */
      command: "evaluate_generic";
      handler: string;
      payload: unknown;
    }
  | {
      command: "evaluate_pullback_complement";
      base: string;
      target: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_simplification";
      target: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_model";
      theory: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_subobject";
      target: string;
      property: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_synthesis";
      theory: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_quotient";
      base: string;
      property: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_decomposition";
      target: string;
      candidate: TheoryJson;
    }
  | {
      command: "evaluate_relaxation";
      target: string;
      property: string;
      candidate: TheoryJson;
    };

export type CatlabRequest = CatlabCommand & { id: string };

// ── NDJSON Response types ─────────────────────────────────────────────────────

export interface CatlabResponseOk {
  id: string;
  status: "ok";
  // Fields present depending on command
  result?: VerificationResult;
  /** For multi-objective: per-objective sub-results */
  subResults?: VerificationResult[];
  theory?: TheoryJson;
  theories?: string[];
  summary?: string;
  verified?: boolean;
  winner?: TheoryJson;
  valid?: boolean;
  errors?: string[];
  count?: number;
  message?: string;
  // Extra fields from new problem types
  candidate_size?: number;
  target_size?: number;
  is_subtheory?: boolean;
  not_in_target?: string[];
  extends_theory?: boolean;
  extends_base?: boolean;
  missing_from_theory?: string[];
  new_morphisms?: number;
}

export interface CatlabResponseError {
  id: string;
  status: "error";
  message: string;
}

export type CatlabResponse = CatlabResponseOk | CatlabResponseError;

// ── Problem specification (consumed by solver + LLM) ─────────────────────────

/** Describes any search problem — consumed by both the solver loop and LLM. */
export interface ProblemSpec {
  /** Human-readable problem type */
  kind: string;
  /** Full problem statement shown to LLM */
  problemDescription: string;
  /** Actionable hint / recipe for the LLM */
  hint: string;
  /** Context JSON (target theory, base theory, etc.) */
  contextJson: string;
  /** Optional style prompt */
  stylePrompt?: string;
  /**
   * Anthropic tool input_schema for the LLM's answer.
   * If undefined, defaults to the standard TheoryJson schema.
   * This lets verifiers ask for { theoryA, theoryB }, a functor mapping, etc.
   */
  answerSchema?: Record<string, unknown>;
  /**
   * Name and description for the tool the LLM calls to submit its answer.
   * Defaults to "propose_theory" / "Submit a candidate Theory".
   */
  answerToolName?: string;
  answerToolDescription?: string;
}

// ── Verifier interface ───────────���───────────────────────────────────────────

import type { CatlabClient } from "./client";

/**
 * Pluggable verification backend. The solver loop is verifier-agnostic.
 *
 * The verifier owns three things:
 *   1. The answer schema (what shape JSON the LLM must produce)
 *   2. The verification logic (send payload to CAS, interpret result)
 *   3. The feedback formatting (turn VerificationResult into LLM-readable text)
 */
export interface Verifier {
  /** Fetch preflight data from CAS, return a ProblemSpec for the LLM. */
  preflight(catlab: CatlabClient, timeoutMs: number): Promise<ProblemSpec>;

  /** Send the LLM's answer payload to the CAS, return verification result. */
  verify(catlab: CatlabClient, payload: unknown, timeoutMs: number): Promise<VerificationResult>;

  /**
   * Format a VerificationResult into LLM-readable feedback text.
   * If not implemented, the solver uses a default structural-diff formatter.
   */
  formatFeedback?(result: VerificationResult, payload: unknown): string;

  /**
   * Validate the LLM's raw output before sending to CAS.
   * If not implemented, the solver uses default TheoryJson validation.
   * Throw if invalid.
   */
  validatePayload?(payload: unknown): void;
}

// ── Solver types ──────────────────────────────────────────────────────────────

export interface SolverOptions {
  /** Style hint for the LLM (e.g. "prefer cobordisms", "use chain complexes") */
  stylePrompt?: string;
  /** Max verification rounds before giving up. Default: 5. */
  maxRounds?: number;
  /** Max retries per round for LLM API errors. Default: 3 */
  maxLLMRetries?: number;
  /** Max retries per round for transient Lean errors. Default: 2 */
  maxLeanRetries?: number;
  /** Timeout per Lean request in ms. Default: 30000 */
  leanTimeoutMs?: number;
  /** Run post-solve reflection step. Default: false */
  reflect?: boolean;
}

/** One entry per *verification attempt* (not per retry). */
export interface HistoryEntry {
  round: number;
  /** The raw payload the LLM submitted (TheoryJson for most problems, opaque for others) */
  payload: unknown;
  result: VerificationResult;
}

export interface SolverResult {
  success: boolean;
  /** Number of verification rounds completed (not counting retries) */
  rounds: number;
  /** The winning payload (TheoryJson for most problems) */
  winner?: unknown;
  finalResult?: VerificationResult;
  /** One entry per successful Lean verification attempt, pass or fail */
  history: HistoryEntry[];
  /** Post-solve LLM reflection on prompt quality (if available) */
  reflection?: string;
}
