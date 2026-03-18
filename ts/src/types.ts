/**
 * Wire types matching the Lean NDJSON contract in Catlab/Repl/Protocol.lean.
 * These are 1:1 with what the Lean server sends and receives.
 */

// ── Expr JSON (tagged-union, single-key objects) ──────────────────────────────
// "unit" | "terminal" | "initial"  → Expr constants
// "X"                              → Expr.atom (bare string shorthand)
// { "atom": "X" }                  → Expr.atom
// { "comp": [e1, e2] }             → Expr.comp e1 e2
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

// ── VerificationResult (from Core/InverseProblem.lean) ────────────────────────

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
  missingSignatures: MissingSignature[];
  /** Generator names the LLM hallucinated that don't correspond to any target object */
  unmappedObjects: string[];
  axiomViolations: AxiomViolation[];
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
    };

export type CatlabRequest = CatlabCommand & { id: string };

// ── NDJSON Response types ─────────────────────────────────────────────────────

export interface CatlabResponseOk {
  id: string;
  status: "ok";
  // Fields present depending on command
  result?: VerificationResult;
  theory?: TheoryJson;
  theories?: string[];
  summary?: string;
  verified?: boolean;
  winner?: TheoryJson;
  valid?: boolean;
  errors?: string[];
  count?: number;
  message?: string;
}

export interface CatlabResponseError {
  id: string;
  status: "error";
  message: string;
}

export type CatlabResponse = CatlabResponseOk | CatlabResponseError;

// ── Solver types ──────────────────────────────────────────────────────────────

export interface SolverOptions {
  /** Which CAS operator inverts the candidate to check against target */
  forwardOp: "decategorify_iso" | "decategorify_K0" | "decategorify_chi" | "mirror" | "opposite" | "identity";
  /** Style hint for the LLM (e.g. "prefer cobordisms", "use chain complexes") */
  stylePrompt?: string;
  /** Max verification rounds before giving up. Default: 5.
   *  A "round" is one successful LLM generation + one successful Lean verification.
   *  Transient retries (rate limits, network blips) do not count as rounds. */
  maxRounds?: number;
  /** Max retries per round for LLM API errors (rate limits, network, bad JSON). Default: 3 */
  maxLLMRetries?: number;
  /** Max retries per round for transient Lean errors (timeout, soft error). Default: 2 */
  maxLeanRetries?: number;
  /** Timeout per Lean request in ms. Default: 30000 */
  leanTimeoutMs?: number;
}

/** One entry per *verification attempt* (not per retry). */
export interface HistoryEntry {
  round: number;
  candidate: TheoryJson;
  result: VerificationResult;
}

export interface SolverResult {
  success: boolean;
  /** Number of verification rounds completed (not counting retries) */
  rounds: number;
  winner?: TheoryJson;
  finalResult?: VerificationResult;
  /** One entry per successful Lean verification attempt, pass or fail */
  history: HistoryEntry[];
  /** Post-solve LLM reflection on prompt quality (if available) */
  reflection?: string;
}
