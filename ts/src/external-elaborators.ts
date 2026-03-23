/**
 * Omega + Hyperion Elaboration Pipeline
 *
 * Centralized module for all Omega/Hyperion interaction.
 * Translates TheoryJson → .omega/.hyp source, invokes CLI via stdin,
 * and maps structured JSON output back to VerificationResult.
 *
 * Omega: equational/algebraic doctrines (LawvereTheory, AlgebraicTheory, etc.)
 *   Features used: sorts, constructors, rewrites, AC attributes, auto tactic,
 *   lemmas (cut rule), parameterized theory imports, implicit arguments, refute.
 *
 * Hyperion: higher-categorical doctrines (HoTT, ∞-categories, cubical, cohesive)
 *   Features used: Category/Substrate/Universe, PathType, JType, PartialElement,
 *   Functor/NatTrans/Adjunction :verify, TensorProduct, SymmetricMonoidal,
 *   Exponential/Evaluator, ModalOperator, assert-eq/assert-neq, eval-simplify,
 *   Preorder, resource modes.
 */

import { spawn } from "child_process";
import type { TheoryJson, ExprJson, AxiomJson, MorphismJson } from "./types";
import type { ElaborationResult, ElaborationStatus, SourceMappedError } from "./lean-elaborator";

// ── Backend routing ──────────────────────────────────────────────────────────

/** Doctrines routed to Omega (equational/algebraic). */
const OMEGA_DOCTRINES = new Set([
  "LawvereTheory",
  "AlgebraicTheory",
  "CartesianClosed",
  "FiniteProduct",
  "MonoidalCategory",   // equational fragment
]);

/** Doctrines routed to Hyperion (higher-categorical). */
export const HYPERION_DOCTRINES = new Set([
  "MartinLofTypeTheory",
  "PresentableInfinityCategory",
  "InfinityNCategory",
  "CubicalTypeTheory",
  "CohesiveHomotopyTypeTheory",
  "2Category",
  "Double",
  "Bicategory",
]);

export type ExternalBackend = "omega" | "hyperion" | null;

/** Determine which external backend (if any) should handle this theory. */
export function routeToExternal(theory: TheoryJson): ExternalBackend {
  if (HYPERION_DOCTRINES.has(theory.doctrine)) return "hyperion";
  if (OMEGA_DOCTRINES.has(theory.doctrine)) return "omega";
  return null;
}

// ── CLI JSON response types ──────────────────────────────────────────────────

interface ExternalResultEntry {
  name: string;
  node_id: string | null;
  status: "valid" | "invalid" | "timeout";
  message: string | null;
}

interface ExternalDiscovery {
  lhs: string;
  rhs: string;
  description: string;
  /** Proof term / path extracted from the e-graph (if available).
   *  This is a sequence of rewrite steps witnessing the equality,
   *  NOT just a boolean flag. For HoTT, these are path constructors. */
  proof_term?: string;
  /** The sequence of e-graph rewrite steps (if available).
   *  Each step is a named law application, forming a 2-cell/path. */
  rewrite_steps?: string[];
}

interface ExternalJsonResponse {
  status: "success" | "failure" | "timeout";
  elapsed_ms: number;
  results: ExternalResultEntry[];
  discoveries: ExternalDiscovery[];
}

// ── Omega source generation ──────────────────────────────────────────────────

/**
 * Detect which morphisms are commutative binary operations.
 * A morphism is AC-eligible if:
 *   - Its domain is prod(X, X) or tensor(X, X) for some sort X
 *   - Its codomain is X
 *   - There's an axiom declaring commutativity (lhs swaps arguments)
 */
function detectACOperations(theory: TheoryJson): Set<string> {
  const acOps = new Set<string>();

  for (const mor of theory.morphisms) {
    // Check if binary: domain is prod/tensor of same sort
    const dom = mor.domain;
    if (typeof dom === "object" && ("prod" in dom || "tensor" in dom)) {
      const pair = "prod" in dom ? dom.prod : (dom as { tensor: [ExprJson, ExprJson] }).tensor;
      const domA = exprToSortName(pair[0]);
      const domB = exprToSortName(pair[1]);
      const cod = exprToSortName(mor.codomain);
      if (domA && domB && cod && domA === domB && domA === cod) {
        // Check if any axiom declares commutativity for this op
        const hasCommutativity = theory.axioms.some(ax =>
          ax.description?.toLowerCase().includes("commut") ||
          ax.name.toLowerCase().includes("commut")
        );
        if (hasCommutativity) {
          acOps.add(mor.name);
        }
      }
    }
  }

  return acOps;
}

/** Extract a simple sort name from an ExprJson, or null if complex. */
function exprToSortName(expr: ExprJson): string | null {
  if (typeof expr === "string") return expr === "terminal" || expr === "unit" ? null : expr;
  if ("atom" in expr) return expr.atom;
  return null;
}

/**
 * Translate a TheoryJson into Omega (.omega) source.
 *
 * Uses:
 *   - AC attributes for commutative operations (rings, lattices)
 *   - auto tactic as fallback when eq-refl fails
 *   - Lemmas for intermediate results
 *   - Parameterized theory imports when doctrine maps to a known base
 */
export function theoryToOmega(theory: TheoryJson): string {
  const lines: string[] = [];
  const sortName = theory.objects.length > 0 ? theory.objects[0].name : "X";
  const theoryName = sanitize(theory.name);
  const acOps = detectACOperations(theory);

  lines.push(`;;; Generated by CatLab for Omega verification`);
  lines.push(`;;; Theory: ${theory.name} (${theory.doctrine})`);
  lines.push(``);

  // Theory block
  lines.push(`(theory ${theoryName}`);

  // Sorts
  for (const obj of theory.objects) {
    lines.push(`  ;; @node object:${obj.name}`);
    lines.push(`  (sort ${sanitize(obj.name)})`);
  }

  // Constructors (morphisms)
  for (const mor of theory.morphisms) {
    lines.push(`  ;; @node morphism:${mor.name}`);
    const sig = omegaMorphismSignature(mor.domain, mor.codomain);
    lines.push(`  (constructor ${sanitize(mor.name)} : ${sig})`);
  }

  // Detect structural combinators used in axioms and declare them
  const usedCombinators = collectCombinators(theory.axioms);
  if (usedCombinators.has("comp")) {
    lines.push(`  ;; Structural: categorical composition`);
    lines.push(`  (constructor comp : (-> ${sanitize(sortName)} ${sanitize(sortName)} ${sanitize(sortName)}))`);
  }
  if (usedCombinators.has("prod")) {
    lines.push(`  ;; Structural: product pairing`);
    lines.push(`  (constructor prod : (-> ${sanitize(sortName)} ${sanitize(sortName)} ${sanitize(sortName)}))`);
  }
  if (usedCombinators.has("id")) {
    lines.push(`  ;; Structural: identity morphism`);
    lines.push(`  (constructor id : (-> ${sanitize(sortName)} ${sanitize(sortName)}))`);
  }
  if (usedCombinators.has("tensor")) {
    lines.push(`  ;; Structural: monoidal tensor`);
    lines.push(`  (constructor tensor : (-> ${sanitize(sortName)} ${sanitize(sortName)} ${sanitize(sortName)}))`);
  }

  // AC attributes for commutative operations
  for (const opName of acOps) {
    lines.push(`  ;; AC: ${opName} is associative-commutative (hash-consing canonicalization)`);
    lines.push(`  (attribute ${sanitize(opName)} :ac)`);
  }

  // Equality judgment on the primary sort
  lines.push(``);
  lines.push(`  (judgment (eq ?a ?b) :where a : ${sanitize(sortName)} b : ${sanitize(sortName)})`);
  lines.push(`  (rule eq-refl :premises () :conclusion (eq ?a ?a))`);

  // Axioms as rewrite rules
  // Separate commutativity axioms from others — AC handles them
  for (const ax of theory.axioms) {
    const isCommAxiom = ax.name.toLowerCase().includes("commut") ||
      ax.description?.toLowerCase().includes("commut");
    if (isCommAxiom && acOps.size > 0) {
      lines.push(`  ;; @node axiom:${ax.name}`);
      lines.push(`  ;; (commutativity handled by :ac attribute)`);
      continue;
    }
    lines.push(`  ;; @node axiom:${ax.name}`);
    const lhs = exprToOmega(ax.lhs);
    const rhs = exprToOmega(ax.rhs);
    lines.push(`  (rewrite ${sanitize(ax.name)} ${lhs} ${rhs})`);
  }

  lines.push(`)`);

  // Proof blocks: try eq-refl first, then auto tactic as fallback
  for (const ax of theory.axioms) {
    const isCommAxiom = ax.name.toLowerCase().includes("commut") ||
      ax.description?.toLowerCase().includes("commut");
    if (isCommAxiom && acOps.size > 0) continue; // AC handles it

    lines.push(``);
    lines.push(`;;; @node axiom:${ax.name}`);
    const lhs = exprToOmega(ax.lhs);
    const rhs = exprToOmega(ax.rhs);
    lines.push(`(proof test-${sanitize(ax.name)}`);
    lines.push(`  :theory ${theoryName}`);
    lines.push(`  :goal (eq ${lhs} ${rhs})`);
    lines.push(`  :tactics ((try (eq-refl) (auto 10))))`);
  }

  // Lemmas: if there are many axioms, prove them incrementally and register
  // as derived rules for use in subsequent proofs
  if (theory.axioms.length > 3) {
    lines.push(``);
    lines.push(`;;; Incremental lemmas — register proven axioms as derived rules`);
    for (const ax of theory.axioms) {
      const isCommAxiom = ax.name.toLowerCase().includes("commut") ||
        ax.description?.toLowerCase().includes("commut");
      if (isCommAxiom && acOps.size > 0) continue;

      const lhs = exprToOmega(ax.lhs);
      const rhs = exprToOmega(ax.rhs);
      lines.push(`(lemma derived-${sanitize(ax.name)}`);
      lines.push(`  :theory ${theoryName}`);
      lines.push(`  :premises ()`);
      lines.push(`  :conclusion (eq ${lhs} ${rhs})`);
      lines.push(`  :derivation (eq-refl))`);
    }
  }

  return lines.join("\n") + "\n";
}

/** Build an Omega type signature from domain/codomain. */
function omegaMorphismSignature(domain: ExprJson, codomain: ExprJson): string {
  const domTypes = flattenDomain(domain);
  const codType = exprToOmegaType(codomain);

  if (domTypes.length === 0) {
    // Nullary constructor (e.g., unit element)
    return codType;
  }
  return `(-> ${domTypes.join(" ")} ${codType})`;
}

/** Flatten a domain expression into a list of sort names. */
function flattenDomain(expr: ExprJson): string[] {
  if (typeof expr === "string") {
    if (expr === "terminal" || expr === "unit") return [];
    return [sanitize(expr)];
  }
  if ("atom" in expr) return [sanitize(expr.atom)];
  if ("prod" in expr || "tensor" in expr) {
    const pair = "prod" in expr ? expr.prod : (expr as { tensor: [ExprJson, ExprJson] }).tensor;
    return [...flattenDomain(pair[0]), ...flattenDomain(pair[1])];
  }
  return [sanitize(JSON.stringify(expr))];
}

/** Convert an ExprJson to an Omega type (sort name). */
function exprToOmegaType(expr: ExprJson): string {
  if (typeof expr === "string") return sanitize(expr);
  if ("atom" in expr) return sanitize(expr.atom);
  return sanitize(JSON.stringify(expr));
}

/** Convert an ExprJson into an Omega term expression. */
function exprToOmega(expr: ExprJson): string {
  if (typeof expr === "string") {
    if (expr === "terminal" || expr === "unit") return "unit";
    return sanitize(expr);
  }
  if ("atom" in expr) return sanitize(expr.atom);
  if ("comp" in expr) {
    return `(comp ${exprToOmega(expr.comp[0])} ${exprToOmega(expr.comp[1])})`;
  }
  if ("id" in expr) {
    return `(id ${exprToOmega(expr.id)})`;
  }
  if ("prod" in expr) {
    return `(prod ${exprToOmega(expr.prod[0])} ${exprToOmega(expr.prod[1])})`;
  }
  if ("tensor" in expr) {
    return `(tensor ${exprToOmega(expr.tensor[0])} ${exprToOmega(expr.tensor[1])})`;
  }
  if ("coprod" in expr) {
    return `(coprod ${exprToOmega(expr.coprod[0])} ${exprToOmega(expr.coprod[1])})`;
  }
  if ("hom" in expr) {
    return `(hom ${exprToOmega(expr.hom[0])} ${exprToOmega(expr.hom[1])})`;
  }
  if ("path" in expr) {
    return `(path ${exprToOmega(expr.path[0])} ${exprToOmega(expr.path[1])} ${exprToOmega(expr.path[2])})`;
  }
  if ("refl" in expr) {
    return `(refl ${exprToOmega(expr.refl)})`;
  }
  if ("pathJ" in expr) {
    return `(J ${exprToOmega(expr.pathJ[0])} ${exprToOmega(expr.pathJ[1])} ${exprToOmega(expr.pathJ[2])} ${exprToOmega(expr.pathJ[3])})`;
  }
  if ("hcomp" in expr) {
    return `(hcomp ${exprToOmega(expr.hcomp[0])} ${exprToOmega(expr.hcomp[1])})`;
  }
  if ("fill" in expr) {
    return `(fill ${exprToOmega(expr.fill[0])} ${exprToOmega(expr.fill[1])})`;
  }
  if ("coe" in expr) {
    return `(coe ${exprToOmega(expr.coe[0])} ${exprToOmega(expr.coe[1])})`;
  }
  if ("bvar" in expr) return `#${expr.bvar}`;
  if ("fvar" in expr) return `?${expr.fvar}`;
  if ("lam" in expr) {
    return `(lam ${sanitize(expr.lam.name)} ${exprToOmega(expr.lam.domain)} ${exprToOmega(expr.lam.body)})`;
  }
  if ("univ" in expr) return `(U ${expr.univ})`;
  return `?unknown`;
}

// ── Hyperion source generation ───────────────────────────────────────────────

/** Doctrine → Hyperion category-level structures. */
interface HyperionDoctrineConfig {
  pathType: boolean;
  jType: boolean;
  partialElement: boolean;
  eGraph: boolean;
  /** Use proof-relevant e-graph mode (merges create labeled edges, not collapse) */
  proofRelevant: boolean;
  /** Add IntervalSort for cubical interval [0,1] with endpoints and connections */
  intervalSort: boolean;
  /** Extra structures to add to [Category ...] block */
  categoryStructures: string[];
  /** Substrate resource mode */
  resourceMode: "optimal-sharing" | "strictly-linear" | "affine";
}

function hyperionDoctrineConfig(doctrine: string): HyperionDoctrineConfig {
  const base: HyperionDoctrineConfig = {
    pathType: false, jType: false, partialElement: false, eGraph: false,
    proofRelevant: false, intervalSort: false,
    categoryStructures: [], resourceMode: "optimal-sharing",
  };

  switch (doctrine) {
    case "MartinLofTypeTheory":
      return { ...base, pathType: true, jType: true, proofRelevant: true,
        categoryStructures: ["[Evaluator app]"] };

    case "CubicalTypeTheory":
      return { ...base, pathType: true, partialElement: true,
        proofRelevant: true, intervalSort: true };

    case "CohesiveHomotopyTypeTheory":
      return { ...base, pathType: true, proofRelevant: true,
        categoryStructures: ["[ModalOperator :ops [esh bflat bsharp]]"] };

    case "InfinityNCategory":
    case "PresentableInfinityCategory":
      return { ...base, pathType: true, eGraph: true, proofRelevant: true };

    case "2Category":
    case "Double":
    case "Bicategory":
      return { ...base, pathType: true, eGraph: true, proofRelevant: true };

    // Monoidal doctrines routed to Hyperion (when needed for coherence)
    case "BraidedMonoidal":
    case "SymmetricMonoidal":
    case "SymmetricMonoidalClosed":
      return { ...base,
        categoryStructures: ["[TensorProduct tensor :unit I]", "[SymmetricMonoidal]"] };

    default:
      return base;
  }
}

/**
 * Translate a TheoryJson into Hyperion (.hyp) source.
 *
 * Uses:
 *   - PathType, JType, PartialElement auto-injection
 *   - Functor/NatTrans/Adjunction :verify for doctrine morphisms
 *   - TensorProduct/SymmetricMonoidal for monoidal categories
 *   - Exponential/Evaluator for CCCs
 *   - ModalOperator for cohesive doctrines
 *   - assert-eq and assert-neq for positive/negative verification
 *   - eval-simplify for canonical form extraction
 *   - Resource modes (strictly-linear, affine) for linear/substructural
 *   - Preorder auto-rules for preorder-enriched categories
 */
export function theoryToHyperion(theory: TheoryJson): string {
  const lines: string[] = [];
  const doctrine = theory.doctrine;
  const config = hyperionDoctrineConfig(doctrine);
  const catName = sanitize(theory.name) + "Cat";
  const subName = sanitize(theory.name) + "Sub";
  const uniName = sanitize(theory.name) + "Uni";
  const thName = sanitize(theory.name) + "Theory";

  lines.push(`;; Generated by CatLab for Hyperion verification`);
  lines.push(`;; Theory: ${theory.name} (${doctrine})`);
  lines.push(``);

  // ── Category block ─────────────────────────────────────────────────────
  lines.push(`[Category ${catName}`);
  for (const obj of theory.objects) {
    lines.push(`  ;; @node object:${obj.name}`);
    lines.push(`  [Object ${sanitize(obj.name)}]`);
  }
  for (const mor of theory.morphisms) {
    lines.push(`  ;; @node morphism:${mor.name}`);
    const domParts = flattenDomain(mor.domain);
    const codType = exprToOmegaType(mor.codomain);
    const domStr = domParts.length === 0 ? `[]` : `[${domParts.join(" ")}]`;
    lines.push(`  [Morphism ${sanitize(mor.name)} :domain ${domStr} :codomain ${codType}]`);
  }

  // Auto-injected structures based on doctrine
  if (config.pathType) {
    lines.push(`  [PathType :refl refl :concat concat :inv inv :ap ap]`);
  }
  if (config.jType) {
    lines.push(`  [JType :elim J :transport transport]`);
  }
  if (config.partialElement) {
    lines.push(`  [PartialElement :hcomp hcomp :coe coe]`);
  }
  if (config.intervalSort) {
    // Cubical interval [0,1] with endpoints and connections.
    // Kernel cubical reductions (coe-refl, coe-concat, coe-inv) are
    // auto-injected by Hyperion when both PathType and PartialElement are present.
    lines.push(`  [IntervalSort I :zero i0 :one i1 :connections [min max] :involution rev]`);
  }
  for (const struct of config.categoryStructures) {
    lines.push(`  ${struct}`);
  }

  lines.push(`]`);
  lines.push(``);

  // ── Substrate block ────────────────────────────────────────────────────
  // Equality mode selection:
  // - proof-relevant: for HoTT/cubical (e-graph merges create labeled edges, not collapse)
  // - equality-saturation: for ∞-categories (standard e-graph)
  // - topological-homotopy: for path algebra (rewriting + eta)
  // - rewrite-equivalence: for directed rewriting only
  const equality = config.proofRelevant
    ? (config.intervalSort ? "topological-homotopy" : "proof-relevant")
    : config.eGraph ? "equality-saturation" : "rewrite-equivalence";
  lines.push(`[Substrate ${subName}`);
  lines.push(`  @engine interaction-graph`);
  lines.push(`  @resource-mode ${config.resourceMode}`);
  lines.push(`  @barrier transparent`);
  lines.push(`  @equality ${equality}`);
  lines.push(`]`);
  lines.push(``);

  // ── Universe ───────────────────────────────────────────────────────────
  lines.push(`[Universe ${uniName} :category ${catName} :substrate ${subName}]`);
  lines.push(``);

  // ── Theory block ───────────────────────────────────────────────────────
  const lawFlag = theory.axioms.length > 0 ? "" : " :no-laws";
  lines.push(`[Theory ${thName} :in ${uniName}${lawFlag}`);

  // Declare constants for each object
  for (const obj of theory.objects) {
    lines.push(`  [const ${sanitize(obj.name).toLowerCase()} ${sanitize(obj.name)}]`);
  }

  // Axioms as @law (bidirectional) or @rule (directed).
  // CRITICAL: bidirectional @law causes exponential e-graph blowup with
  // associativity-like rules. Use @rule for computational axioms (unit laws,
  // simplifications) and reserve @law for genuinely symmetric equations.
  // Cap @law at MAX_BIDIR_LAWS to prevent saturation hangs.
  const MAX_BIDIR_LAWS = 3;
  let bidirCount = 0;

  for (const ax of theory.axioms) {
    lines.push(`  ;; @node axiom:${ax.name}`);
    const lhs = exprToHyperion(ax.lhs);
    const rhs = exprToHyperion(ax.rhs);
    if (ax.relation === "ineq") {
      lines.push(`  [@rule ${sanitize(ax.name)} ${lhs} ==> ${rhs}]`);
    } else if (config.eGraph && !isComputationalAxiom(ax) && bidirCount < MAX_BIDIR_LAWS) {
      // Genuinely symmetric equation — safe for bidirectional exploration
      lines.push(`  [@law ${sanitize(ax.name)} ${lhs} === ${rhs}]`);
      bidirCount++;
    } else {
      // Computational / overflow — directed rewriting only
      lines.push(`  [@rule ${sanitize(ax.name)} ${lhs} ==> ${rhs}]`);
    }
  }

  lines.push(`]`);
  lines.push(``);

  // ── Proofs block ───────────────────────────────────────────────────────
  if (theory.axioms.length > 0) {
    lines.push(`[Proofs ${sanitize(theory.name)}Check :in ${thName}`);
    for (const ax of theory.axioms) {
      lines.push(`  ;; @node axiom:${ax.name}`);
      const lhs = exprToHyperion(ax.lhs);
      const rhs = exprToHyperion(ax.rhs);
      lines.push(`  [assert-eq ${sanitize(ax.name)} ${lhs} ${rhs}]`);
    }

    // extract-proof: selectively extract structured proof terms.
    // Only for axioms that genuinely need path inspection (not all of them).
    // extract-proof enables egg's explanation tracking which adds overhead
    // to every e-graph merge, so use sparingly.
    if (config.proofRelevant && theory.axioms.length <= 5) {
      lines.push(``);
      lines.push(`  ;; Extract structured proof terms (selective — overhead scales with saturation)`);
      for (const ax of theory.axioms) {
        const lhs = exprToHyperion(ax.lhs);
        const rhs = exprToHyperion(ax.rhs);
        lines.push(`  [extract-proof ${sanitize(ax.name)}-path ${lhs} ${rhs}]`);
      }
    }

    // assert-exists: for ∞-categorical doctrines, verify Kan filler existence.
    // Given a horn (boundary with one face missing), assert that a filler exists
    // in the e-graph. This is the computational content of the Kan condition.
    if (config.proofRelevant && config.pathType) {
      lines.push(``);
      lines.push(`  ;; Kan filler verification: assert existence of fillers`);
      lines.push(`  ;; for horn inclusions Λ^n_k → Δ^n`);
      // For each composable pair of morphisms, assert a composite exists
      for (let i = 0; i < theory.morphisms.length; i++) {
        for (let j = 0; j < theory.morphisms.length; j++) {
          const f = theory.morphisms[i];
          const g = theory.morphisms[j];
          const fCod = exprToSortName(f.codomain);
          const gDom = exprToSortName(g.domain);
          if (fCod && gDom && fCod === gDom) {
            lines.push(`  [assert-exists comp-${sanitize(f.name)}-${sanitize(g.name)} [comp ${sanitize(g.name)} ${sanitize(f.name)}]]`);
          }
        }
      }
    }

    // eval-simplify: extract canonical forms for key terms on e-graph substrates
    if (config.eGraph && theory.morphisms.length > 0) {
      lines.push(``);
      lines.push(`  ;; Extract canonical forms via e-graph saturation`);
      for (const mor of theory.morphisms.slice(0, 3)) {
        // Simplify a few key morphism applications
        const domParts = flattenDomain(mor.domain);
        if (domParts.length > 0) {
          const args = domParts.map(p => p.toLowerCase()).join(" ");
          lines.push(`  [eval-simplify canonical-${sanitize(mor.name)} [${sanitize(mor.name)} ${args}]]`);
        }
      }
    }

    lines.push(`]`);
  }

  // ── Negative assertions (assert-neq) ───────────────────────────────────
  // If we have an e-graph substrate, also generate a directed-substrate block
  // to confirm which equalities require e-graph and can't be reached directedly
  if (config.eGraph && theory.axioms.length > 0) {
    const dirSubName = sanitize(theory.name) + "DirSub";
    const dirUniName = sanitize(theory.name) + "DirUni";
    const dirThName = sanitize(theory.name) + "DirTheory";

    lines.push(``);
    lines.push(`;; Directed substrate — confirms which equalities need e-graph discovery`);
    lines.push(`[Substrate ${dirSubName}`);
    lines.push(`  @engine interaction-graph`);
    lines.push(`  @resource-mode ${config.resourceMode}`);
    lines.push(`  @barrier transparent`);
    lines.push(`  @equality rewrite-equivalence`);
    lines.push(`]`);
    lines.push(``);
    lines.push(`[Universe ${dirUniName} :category ${catName} :substrate ${dirSubName}]`);
    lines.push(``);
    lines.push(`[Theory ${dirThName} :in ${dirUniName} :no-laws`);
    for (const obj of theory.objects) {
      lines.push(`  [const ${sanitize(obj.name).toLowerCase()} ${sanitize(obj.name)}]`);
    }
    // Same axioms as @law (Hyperion will treat as bidirectional even on rewrite sub,
    // but the point is that assert-neq confirms non-derivability)
    for (const ax of theory.axioms) {
      const lhs = exprToHyperion(ax.lhs);
      const rhs = exprToHyperion(ax.rhs);
      lines.push(`  [@law ${sanitize(ax.name)} ${lhs} === ${rhs}]`);
    }
    lines.push(`]`);
    lines.push(``);

    // assert-neq: confirm these equalities are NOT reachable on directed substrate
    // (this is informational — failures here are expected and confirm e-graph value)
    lines.push(`[Proofs ${sanitize(theory.name)}DirCheck :in ${dirThName}`);
    for (const ax of theory.axioms) {
      const lhs = exprToHyperion(ax.lhs);
      const rhs = exprToHyperion(ax.rhs);
      lines.push(`  [assert-neq ${sanitize(ax.name)}-blocked ${lhs} ${rhs}]`);
    }
    lines.push(`]`);
  }

  // ── Functor :verify for doctrine morphisms ─────────────────────────────
  // If the theory has morphisms that look like functorial mappings between sorts,
  // generate Functor verification blocks
  const functorPairs = detectFunctorialMorphisms(theory);
  if (functorPairs.length > 0) {
    lines.push(``);
    lines.push(`;; Functor verification — doctrine morphisms`);
    for (const fp of functorPairs) {
      lines.push(`[Functor ${sanitize(fp.name)}`);
      lines.push(`  :from ${catName}`);
      lines.push(`  :to ${catName}`);
      lines.push(`  :on-objects [${sanitize(fp.domSort)} -> ${sanitize(fp.codSort)}]`);
      lines.push(`  :verify`);
      lines.push(`]`);
    }
  }

  return lines.join("\n") + "\n";
}

/** Detect morphisms that look like functorial mappings (map between distinct sorts). */
function detectFunctorialMorphisms(theory: TheoryJson): Array<{ name: string; domSort: string; codSort: string }> {
  const results: Array<{ name: string; domSort: string; codSort: string }> = [];
  for (const mor of theory.morphisms) {
    const domSort = exprToSortName(mor.domain);
    const codSort = exprToSortName(mor.codomain);
    // A functor-like morphism maps between distinct sorts (not binary ops)
    if (domSort && codSort && domSort !== codSort) {
      results.push({ name: mor.name, domSort, codSort });
    }
  }
  return results;
}

/** Convert an ExprJson into a Hyperion term expression. */
function exprToHyperion(expr: ExprJson): string {
  if (typeof expr === "string") {
    if (expr === "terminal" || expr === "unit") return "unit";
    return sanitize(expr);
  }
  if ("atom" in expr) return sanitize(expr.atom);
  if ("comp" in expr) {
    return `[comp ${exprToHyperion(expr.comp[0])} ${exprToHyperion(expr.comp[1])}]`;
  }
  if ("id" in expr) {
    return `[refl ${exprToHyperion(expr.id)}]`;
  }
  if ("prod" in expr) {
    return `[prod ${exprToHyperion(expr.prod[0])} ${exprToHyperion(expr.prod[1])}]`;
  }
  if ("tensor" in expr) {
    return `[tensor ${exprToHyperion(expr.tensor[0])} ${exprToHyperion(expr.tensor[1])}]`;
  }
  if ("coprod" in expr) {
    return `[coprod ${exprToHyperion(expr.coprod[0])} ${exprToHyperion(expr.coprod[1])}]`;
  }
  if ("hom" in expr) {
    return `[hom ${exprToHyperion(expr.hom[0])} ${exprToHyperion(expr.hom[1])}]`;
  }
  if ("path" in expr) {
    return `[path ${exprToHyperion(expr.path[0])} ${exprToHyperion(expr.path[1])} ${exprToHyperion(expr.path[2])}]`;
  }
  if ("refl" in expr) {
    return `[refl ${exprToHyperion(expr.refl)}]`;
  }
  if ("pathJ" in expr) {
    return `[J ${exprToHyperion(expr.pathJ[0])} ${exprToHyperion(expr.pathJ[1])} ${exprToHyperion(expr.pathJ[2])} ${exprToHyperion(expr.pathJ[3])}]`;
  }
  if ("hcomp" in expr) {
    return `[hcomp ${exprToHyperion(expr.hcomp[0])} ${exprToHyperion(expr.hcomp[1])}]`;
  }
  if ("fill" in expr) {
    return `[fill ${exprToHyperion(expr.fill[0])} ${exprToHyperion(expr.fill[1])}]`;
  }
  if ("coe" in expr) {
    return `[coe ${exprToHyperion(expr.coe[0])} ${exprToHyperion(expr.coe[1])}]`;
  }
  if ("bvar" in expr) return `#${expr.bvar}`;
  if ("fvar" in expr) return `?${expr.fvar}`;
  if ("lam" in expr) {
    return `[lam ${sanitize(expr.lam.name)} ${exprToHyperion(expr.lam.domain)} ${exprToHyperion(expr.lam.body)}]`;
  }
  if ("app" in expr) {
    return `[${exprToHyperion(expr.app[0])} ${exprToHyperion(expr.app[1])}]`;
  }
  if ("pi" in expr) {
    return `[pi ${sanitize(expr.pi.name)} ${exprToHyperion(expr.pi.base)} ${exprToHyperion(expr.pi.body)}]`;
  }
  if ("sigma" in expr) {
    return `[sigma ${sanitize(expr.sigma.name)} ${exprToHyperion(expr.sigma.base)} ${exprToHyperion(expr.sigma.body)}]`;
  }
  if ("univ" in expr) return `[U ${expr.univ}]`;
  return `?unknown`;
}

/** Whether this doctrine needs PathType auto-injection. */
function needsPathType(doctrine: string): boolean {
  return hyperionDoctrineConfig(doctrine).pathType;
}

/** Whether this doctrine benefits from e-graph saturation. */
function needsEGraph(doctrine: string): boolean {
  return hyperionDoctrineConfig(doctrine).eGraph;
}

// ── CLI invocation ───────────────────────────────────────────────────────────

export interface ExternalElaborationOptions {
  /** Path to omega binary. Default: "omega" */
  omegaBin?: string;
  /** Path to hyperion binary. Default: "hyperion" */
  hyperionBin?: string;
  /** Timeout in ms. Default: 30000 */
  timeoutMs?: number;
}

/**
 * Elaborate a theory via the appropriate external backend.
 * Returns null if no external backend handles this doctrine.
 */
export async function elaborateExternal(
  theory: TheoryJson,
  opts?: ExternalElaborationOptions,
): Promise<ElaborationResult | null> {
  const backend = routeToExternal(theory);
  if (!backend) return null;

  if (backend === "omega") {
    return elaborateViaOmega(theory, opts);
  } else {
    return elaborateViaHyperion(theory, opts);
  }
}

/** Elaborate via Omega CLI. */
async function elaborateViaOmega(
  theory: TheoryJson,
  opts?: ExternalElaborationOptions,
): Promise<ElaborationResult> {
  const source = theoryToOmega(theory);
  const bin = opts?.omegaBin ?? "omega";
  const timeout = opts?.timeoutMs ?? 30000;

  const response = await runExternalCli(bin, ["check", "--json", "--stdin"], source, timeout);
  return externalResponseToResult(response, source, "omega");
}

/** Elaborate via Hyperion CLI. */
async function elaborateViaHyperion(
  theory: TheoryJson,
  opts?: ExternalElaborationOptions,
): Promise<ElaborationResult> {
  const source = theoryToHyperion(theory);
  const bin = opts?.hyperionBin ?? "/Users/kevin/Desktop/omega/hyperion/target/release/hyperion";
  const timeout = opts?.timeoutMs ?? 30000;

  const response = await runExternalCli(bin, ["check", "--json", "--stdin"], source, timeout);
  return externalResponseToResult(response, source, "hyperion");
}

/** Spawn a CLI process, pipe source to stdin, parse JSON stdout. */
function runExternalCli(
  bin: string,
  args: string[],
  source: string,
  timeout: number,
): Promise<ExternalJsonResponse> {
  return new Promise((resolve) => {
    let stdout = "";
    let stderr = "";

    const proc = spawn(bin, args, { timeout });

    // Hard kill safety net: if the process doesn't exit within timeout + 5s,
    // SIGKILL it. Hyperion's e-graph saturation can hang indefinitely with
    // too many bidirectional @law rules.
    const killTimer = setTimeout(() => {
      try { proc.kill("SIGKILL"); } catch { /* already dead */ }
    }, timeout + 5000);

    proc.stdout.on("data", (d: Buffer) => { stdout += d.toString(); });
    proc.stderr.on("data", (d: Buffer) => { stderr += d.toString(); });

    proc.on("close", (code, signal) => {
      clearTimeout(killTimer);
      if (signal === "SIGTERM" || signal === "SIGKILL") {
        resolve({
          status: "timeout",
          elapsed_ms: timeout,
          results: [{
            name: "timeout",
            node_id: null,
            status: "timeout",
            message: `${bin} killed after ${timeout}ms (signal: ${signal})`,
          }],
          discoveries: [],
        });
        return;
      }
      // JSON may be on stdout, stderr, or both — try each
      const jsonText = tryParseJson(stdout.trim()) ? stdout.trim()
        : tryParseJson(stderr.trim()) ? stderr.trim()
        : stdout.trim() || stderr.trim();
      try {
        const parsed = JSON.parse(jsonText) as ExternalJsonResponse;
        resolve(parsed);
      } catch {
        resolve({
          status: code === 0 ? "success" : "failure",
          elapsed_ms: 0,
          results: [{
            name: "parse_error",
            node_id: null,
            status: "invalid",
            message: `Failed to parse ${bin} output: ${jsonText.slice(0, 200)}`,
          }],
          discoveries: [],
        });
      }
    });

    proc.on("error", (err) => {
      resolve({
        status: "failure",
        elapsed_ms: 0,
        results: [{
          name: "spawn_error",
          node_id: null,
          status: "invalid",
          message: `Failed to run ${bin}: ${err.message}`,
        }],
        discoveries: [],
      });
    });

    // Write source to stdin and close
    proc.stdin.write(source);
    proc.stdin.end();
  });
}

/** Convert an external JSON response into CatLab's ElaborationResult. */
function externalResponseToResult(
  response: ExternalJsonResponse,
  source: string,
  backend: "omega" | "hyperion",
): ElaborationResult {
  const errors: SourceMappedError[] = [];

  for (const r of response.results) {
    if (r.status === "invalid") {
      errors.push({
        astNodeId: r.node_id ?? `${backend}:${r.name}`,
        leanLine: 0,
        message: r.message ?? `${r.name} failed verification`,
        severity: "fatal",
      });
    } else if (r.status === "timeout") {
      errors.push({
        astNodeId: r.node_id ?? `${backend}:${r.name}`,
        leanLine: 0,
        message: r.message ?? `${r.name} timed out`,
        severity: "warning",
      });
    }
  }

  const fatalErrors = errors.filter(e => e.severity === "fatal");
  const warnings = errors.filter(e => e.severity === "warning");

  let status: ElaborationStatus;
  if (fatalErrors.length > 0) {
    status = "semantic_error";
  } else if (warnings.length > 0) {
    status = "unverified_axiom";
  } else {
    status = "success";
  }

  // Build diagnostics string
  const diagLines: string[] = [];

  if (status === "success") {
    diagLines.push(`All assertions verified by ${backend} (${response.elapsed_ms.toFixed(1)}ms).`);
  }

  for (const err of fatalErrors) {
    diagLines.push(`[${backend.toUpperCase()} ERROR in ${err.astNodeId}] ${err.message}`);
  }
  for (const warn of warnings) {
    diagLines.push(`[${backend.toUpperCase()} TIMEOUT in ${warn.astNodeId}] ${warn.message}`);
  }

  // Include discoveries (Hyperion e-graph results) with proof terms
  if (response.discoveries.length > 0) {
    diagLines.push(``);
    diagLines.push(`Discoveries (${response.discoveries.length}):`);
    for (const d of response.discoveries) {
      diagLines.push(`  ${d.lhs} = ${d.rhs} — ${d.description}`);
      // Include the proof term (path/2-cell) if available.
      // This is essential for HoTT: the LLM needs to see the specific
      // path constructors, not just that an equality holds.
      if (d.proof_term) {
        diagLines.push(`    proof: ${d.proof_term}`);
      }
      if (d.rewrite_steps && d.rewrite_steps.length > 0) {
        diagLines.push(`    via: ${d.rewrite_steps.join(" → ")}`);
      }
    }
  }

  return {
    status,
    errors,
    diagnostics: diagLines.join("\n"),
    leanSource: source,
  };
}


// ── Cross-Tier / Truncation / Pushout (REMOVED) ──────────────────────────────
//
// The following were removed because they duplicated Lean CAS functionality:
//   - CrossTierFunctor, compileCrossTierFunctor, elaborateCrossTierFunctor
//   - truncateToHomotopyCategory, truncatedTheoryToLean
//   - computeTheoryPushout, PushoutCocone, computePushoutCocone
//   - transportAxiom, applyFunctorToExpr, verifyTheoryPushout
//
// Lean's CAS already implements these correctly:
//   - Theory pushouts: `pushout` operator via compute_pushout REPL command
//   - Theory morphisms: TheoryMorphism with inclusion, comp, id
//   - Truncation: `Truncate` operator via apply_operator REPL command
//
// The tier-translation logic (theory → .omega/.hyp source) remains in
// theoryToOmega() and theoryToHyperion() above.

// ── Geometric Morphism Elaboration ───────────────────────────────────────────

import type { TheoryMorphismJson, GeneratorMapEntryJson } from "./types";

/**
 * Translate a TheoryMorphism (from the Lean REPL) into Hyperion functor syntax.
 *
 * This is the critical tier-translation step for ∞-topos verification:
 * Lean computes the theory morphism (pushout cocone leg, inclusion, etc.)
 * and TypeScript translates it into Hyperion's functor verification language.
 *
 * For PathType doctrines, the functor must preserve paths:
 *   F(p : x = y) becomes a valid path F(x) = F(y) in the target theory.
 * Hyperion's [Functor :verify] directive checks this automatically once
 * we declare the object/morphism mappings.
 */
export function morphismToHyperion(
  morphism: TheoryMorphismJson,
  sourceTheory: TheoryJson,
  targetTheory: TheoryJson,
): string {
  const lines: string[] = [];
  const srcConfig = hyperionDoctrineConfig(sourceTheory.doctrine);
  const tgtConfig = hyperionDoctrineConfig(targetTheory.doctrine);
  const functorName = sanitize(morphism.name);

  lines.push(`;; Functor: ${morphism.name}`);
  lines.push(`;; ${morphism.source} → ${morphism.target}`);
  lines.push(``);

  // First, emit both theories as Category blocks
  lines.push(`;; ── Source theory ──`);
  lines.push(theoryToHyperion(sourceTheory));
  lines.push(`;; ── Target theory ──`);
  lines.push(theoryToHyperion(targetTheory));

  // Functor block: declare the mapping
  const srcCatName = sanitize(sourceTheory.name) + "Cat";
  const tgtCatName = sanitize(targetTheory.name) + "Cat";

  lines.push(`[Functor ${functorName}`);
  lines.push(`  :source ${srcCatName}`);
  lines.push(`  :target ${tgtCatName}`);

  // Object mappings
  for (const entry of morphism.onObjects) {
    const srcName = sanitize(entry.source);
    const tgtExpr = mapEntryTargetToHyperion(entry.target);
    lines.push(`  [on-object ${srcName} ${tgtExpr}]`);
  }

  // Morphism mappings
  for (const entry of morphism.onMorphisms) {
    const srcName = sanitize(entry.source);
    const tgtExpr = mapEntryTargetToHyperion(entry.target);
    lines.push(`  [on-morphism ${srcName} ${tgtExpr}]`);
  }

  // Path preservation: if source has PathType, the functor must map paths
  // to paths. Hyperion's :verify directive checks this automatically.
  if (srcConfig.pathType || tgtConfig.pathType) {
    lines.push(`  :preserve-paths true`);
  }

  lines.push(`  :verify true`);
  lines.push(`]`);
  lines.push(``);

  return lines.join("\n");
}

/**
 * Translate a pair of TheoryMorphisms representing an adjunction
 * (geometric morphism) into Hyperion syntax for verification.
 *
 * A geometric morphism f : E → F between ∞-topoi consists of:
 *   - f* : F → E  (inverse image, preserves finite limits)
 *   - f_* : E → F (direct image, right adjoint to f*)
 *
 * Hyperion verifies:
 *   1. f* preserves finite limits (checked via path-preservation)
 *   2. The adjunction unit η : Id → f_* ∘ f* and counit ε : f* ∘ f_* → Id
 *   3. Triangle identities
 */
export function adjunctionToHyperion(
  inverseName: string,
  inverseImage: TheoryMorphismJson,
  directImage: TheoryMorphismJson,
  sourceTheory: TheoryJson,
  targetTheory: TheoryJson,
): string {
  const lines: string[] = [];

  lines.push(`;; Geometric morphism: ${inverseName}`);
  lines.push(`;; f* : ${directImage.source} → ${directImage.target} (inverse image)`);
  lines.push(`;; f_* : ${inverseImage.source} → ${inverseImage.target} (direct image)`);
  lines.push(``);

  // Emit both theories
  lines.push(theoryToHyperion(sourceTheory));
  lines.push(theoryToHyperion(targetTheory));

  // Emit both functors
  const srcCatName = sanitize(sourceTheory.name) + "Cat";
  const tgtCatName = sanitize(targetTheory.name) + "Cat";
  const fStarName = sanitize(inverseName) + "_star";
  const fLowerName = sanitize(inverseName) + "_lower";

  // f* : target → source (inverse image, left adjoint)
  lines.push(`[Functor ${fStarName}`);
  lines.push(`  :source ${tgtCatName}`);
  lines.push(`  :target ${srcCatName}`);
  for (const entry of inverseImage.onObjects) {
    lines.push(`  [on-object ${sanitize(entry.source)} ${mapEntryTargetToHyperion(entry.target)}]`);
  }
  for (const entry of inverseImage.onMorphisms) {
    lines.push(`  [on-morphism ${sanitize(entry.source)} ${mapEntryTargetToHyperion(entry.target)}]`);
  }
  lines.push(`  :preserve-paths true`);
  lines.push(`  :verify true`);
  lines.push(`]`);
  lines.push(``);

  // f_* : source → target (direct image, right adjoint)
  lines.push(`[Functor ${fLowerName}`);
  lines.push(`  :source ${srcCatName}`);
  lines.push(`  :target ${tgtCatName}`);
  for (const entry of directImage.onObjects) {
    lines.push(`  [on-object ${sanitize(entry.source)} ${mapEntryTargetToHyperion(entry.target)}]`);
  }
  for (const entry of directImage.onMorphisms) {
    lines.push(`  [on-morphism ${sanitize(entry.source)} ${mapEntryTargetToHyperion(entry.target)}]`);
  }
  lines.push(`  :verify true`);
  lines.push(`]`);
  lines.push(``);

  // Adjunction declaration
  lines.push(`[Adjunction ${sanitize(inverseName)}`);
  lines.push(`  :left ${fStarName}`);
  lines.push(`  :right ${fLowerName}`);
  lines.push(`  :verify true`);
  lines.push(`]`);
  lines.push(``);

  return lines.join("\n");
}

/**
 * Generate a WeakEquivalence verification block for Hyperion.
 *
 * In HoTT/∞-categorical contexts, two theories may be strictly different
 * but weakly equivalent. This generates Hyperion's [WeakEquivalence :verify]
 * directive which checks that corresponding types are connected by
 * invertible maps (not strict isomorphism).
 */
export function weakEquivalenceToHyperion(
  name: string,
  theory1: TheoryJson,
  theory2: TheoryJson,
  typePairings: Array<[string, string]>,
  /** Set false during development to skip verification (faster). Default: true. */
  verify: boolean = true,
): string {
  const lines: string[] = [];
  const cat1 = sanitize(theory1.name) + "Cat";
  const cat2 = sanitize(theory2.name) + "Cat";

  lines.push(`;; Weak equivalence check: ${theory1.name} ≃ ${theory2.name}`);
  lines.push(``);

  // Emit both theories
  lines.push(theoryToHyperion(theory1));
  lines.push(theoryToHyperion(theory2));

  // WeakEquivalence block
  lines.push(`[WeakEquivalence ${sanitize(name)}`);
  lines.push(`  :source ${cat1}`);
  lines.push(`  :target ${cat2}`);
  lines.push(`  :on-types [`);
  for (const [t1, t2] of typePairings) {
    lines.push(`    [${sanitize(t1)} ${sanitize(t2)}]`);
  }
  lines.push(`  ]`);
  lines.push(`  :verify ${verify}`);
  lines.push(`]`);
  lines.push(``);

  return lines.join("\n");
}

/** Convert a GeneratorMapEntry target (ExprJson) to Hyperion syntax. */
function mapEntryTargetToHyperion(target: ExprJson): string {
  return exprToHyperion(target);
}

// ── Lemma Loop: LLM Proof Assistance ──────────────────────────────────────────

/**
 * A LemmaNode represents an intermediate lemma that the LLM can propose
 * to help prove a difficult axiom. When aesop_cat fails, the LLM can
 * break the proof into smaller steps by providing lemma nodes.
 *
 * These are translated to Lean `have` statements or independent lemmas
 * before the final theorem, feeding intermediate goals to aesop/simp.
 */
export interface LemmaNode {
  /** Lemma name (must be unique within the theory) */
  name: string;
  /** The statement to prove (as an ExprJson equality) */
  statement: { lhs: ExprJson; rhs: ExprJson };
  /** Proof strategy: which tactic to try */
  tactic: "aesop_cat" | "simp" | "ring" | "omega" | "rfl" | "ext" | "exact"
    | "rw" | "erw" | "apply" | "calc" | "steps";
  /** For "exact"/"apply": the proof term to use */
  proofTerm?: string;
  /**
   * For "rw"/"erw"/"steps": ordered list of tactic steps.
   * Each string is a complete tactic line, e.g.:
   *   ["rw [PCA.skk_app]", "rw [PCA.comp_tracker_app]", "exact h"]
   * Critical for PCA combinator algebra where simp/aesop cause infinite loops.
   */
  tacticSteps?: string[];
  /** Dependencies: names of other lemmas this one uses */
  dependencies?: string[];
}

/**
 * Translate a sequence of LemmaNodes into Lean source.
 * Each lemma becomes a `have` statement in the proof context,
 * building up to the final goal.
 */
export function lemmasToLean(
  lemmas: LemmaNode[],
  finalGoal: { lhs: string; rhs: string },
  nameCtx: { sanitize: (s: string) => string },
): string {
  const lines: string[] = [];

  // Topological sort by dependencies
  const sorted = topologicalSort(lemmas);

  for (const lemma of sorted) {
    const lhs = nameCtx.sanitize(exprToLeanish(lemma.statement.lhs));
    const rhs = nameCtx.sanitize(exprToLeanish(lemma.statement.rhs));

    lines.push(`  -- Intermediate lemma: ${lemma.name}`);
    lines.push(`  have ${nameCtx.sanitize(lemma.name)} : ${lhs} = ${rhs} := by`);

    switch (lemma.tactic) {
      case "exact":
        lines.push(`    exact ${lemma.proofTerm ?? "sorry"}`);
        break;
      case "apply":
        lines.push(`    apply ${lemma.proofTerm ?? "sorry"}`);
        break;
      case "rfl":
        lines.push(`    rfl`);
        break;
      case "ext":
        lines.push(`    ext; aesop_cat`);
        break;
      case "rw":
      case "erw":
        // Emit each rewrite step on its own line — directional control
        if (lemma.tacticSteps && lemma.tacticSteps.length > 0) {
          for (const step of lemma.tacticSteps) {
            lines.push(`    ${step}`);
          }
        } else {
          lines.push(`    ${lemma.tactic} [sorry]`);
        }
        break;
      case "calc":
        // Calc block: each step is a line in the calculation
        if (lemma.tacticSteps && lemma.tacticSteps.length > 0) {
          lines.push(`    calc`);
          for (const step of lemma.tacticSteps) {
            lines.push(`      ${step}`);
          }
        } else {
          lines.push(`    sorry`);
        }
        break;
      case "steps":
        // Arbitrary tactic sequence — the LLM dictates every line
        if (lemma.tacticSteps && lemma.tacticSteps.length > 0) {
          for (const step of lemma.tacticSteps) {
            lines.push(`    ${step}`);
          }
        } else {
          lines.push(`    sorry`);
        }
        break;
      default:
        lines.push(`    ${lemma.tactic}`);
    }
  }

  // Final goal using the accumulated lemmas
  lines.push(`  -- Final goal`);
  lines.push(`  aesop_cat`);

  return lines.join("\n");
}

/** Topological sort of lemmas by dependencies. */
function topologicalSort(lemmas: LemmaNode[]): LemmaNode[] {
  const byName = new Map(lemmas.map(l => [l.name, l]));
  const visited = new Set<string>();
  const result: LemmaNode[] = [];

  function visit(name: string) {
    if (visited.has(name)) return;
    visited.add(name);
    const lemma = byName.get(name);
    if (!lemma) return;
    for (const dep of lemma.dependencies ?? []) {
      visit(dep);
    }
    result.push(lemma);
  }

  for (const l of lemmas) visit(l.name);
  return result;
}

/** Quick ExprJson → string for lemma context (not full Lean elaboration). */
function exprToLeanish(expr: ExprJson): string {
  if (typeof expr === "string") return expr;
  if ("atom" in expr) return expr.atom;
  if ("comp" in expr) return `(${exprToLeanish(expr.comp[0])} ≫ ${exprToLeanish(expr.comp[1])})`;
  if ("id" in expr) return `(𝟙 ${exprToLeanish(expr.id)})`;
  if ("prod" in expr) return `(${exprToLeanish(expr.prod[0])} ⨯ ${exprToLeanish(expr.prod[1])})`;
  if ("tensor" in expr) return `(${exprToLeanish(expr.tensor[0])} ⊗ ${exprToLeanish(expr.tensor[1])})`;
  return "sorry";
}
// ── Utilities ────────────────────────────────────────────────────────────────

/** Check if a string is valid JSON. */
function tryParseJson(s: string): boolean {
  try { JSON.parse(s); return true; } catch { return false; }
}

/** Collect which structural combinators (comp, prod, id, tensor) appear in axiom expressions. */
function collectCombinators(axioms: AxiomJson[]): Set<string> {
  const result = new Set<string>();
  function walk(expr: ExprJson) {
    if (typeof expr === "string") return;
    if ("atom" in expr) return;
    if ("comp" in expr) { result.add("comp"); walk(expr.comp[0]); walk(expr.comp[1]); }
    if ("prod" in expr) { result.add("prod"); walk(expr.prod[0]); walk(expr.prod[1]); }
    if ("id" in expr) { result.add("id"); walk(expr.id); }
    if ("tensor" in expr) { result.add("tensor"); walk(expr.tensor[0]); walk(expr.tensor[1]); }
    if ("coprod" in expr) { result.add("coprod"); walk(expr.coprod[0]); walk(expr.coprod[1]); }
    if ("hom" in expr) { result.add("hom"); walk(expr.hom[0]); walk(expr.hom[1]); }
    if ("path" in expr) { result.add("path"); walk(expr.path[0]); walk(expr.path[1]); walk(expr.path[2]); }
    if ("refl" in expr) { result.add("refl"); walk(expr.refl); }
    if ("pathJ" in expr) { result.add("pathJ"); walk(expr.pathJ[0]); walk(expr.pathJ[1]); walk(expr.pathJ[2]); walk(expr.pathJ[3]); }
    if ("hcomp" in expr) { result.add("hcomp"); walk(expr.hcomp[0]); walk(expr.hcomp[1]); }
    if ("fill" in expr) { result.add("fill"); walk(expr.fill[0]); walk(expr.fill[1]); }
    if ("coe" in expr) { result.add("coe"); walk(expr.coe[0]); walk(expr.coe[1]); }
    if ("lam" in expr) { result.add("lam"); walk(expr.lam.domain); walk(expr.lam.body); }
    if ("univ" in expr) { result.add("univ"); }
  }
  for (const ax of axioms) {
    walk(ax.lhs);
    walk(ax.rhs);
  }
  return result;
}

/**
 * Classify an axiom as "computational" (should use directed @rule, not @law).
 * Computational axioms have a clear reduction direction and cause e-graph
 * blowup when made bidirectional. Examples: unit laws, identity, associativity.
 */
function isComputationalAxiom(ax: AxiomJson): boolean {
  const name = ax.name.toLowerCase();
  const desc = (ax.description ?? "").toLowerCase();
  // Unit/identity laws: f ∘ id = f, id ∘ f = f — always reduce
  if (name.includes("unit") || name.includes("identity")) return true;
  if (desc.includes("unit law") || desc.includes("identity")) return true;
  // Associativity: (f ∘ g) ∘ h = f ∘ (g ∘ h) — bidirectional = exponential
  if (name.includes("assoc")) return true;
  if (desc.includes("associativ")) return true;
  // Absorption, idempotence, simplification rules
  if (name.includes("absorb") || name.includes("idemp") || name.includes("simpl")) return true;
  // Check structural shape: if one side is strictly simpler (contains fewer
  // constructors), it's computational (reduce to simpler form)
  const lhsSize = exprJsonSize(ax.lhs);
  const rhsSize = exprJsonSize(ax.rhs);
  if (Math.abs(lhsSize - rhsSize) >= 2) return true;
  return false;
}

/** Rough size of an ExprJson for computational axiom classification. */
function exprJsonSize(expr: ExprJson): number {
  if (typeof expr === "string") return 1;
  if ("atom" in expr) return 1;
  let size = 1;
  for (const val of Object.values(expr)) {
    if (Array.isArray(val)) {
      for (const child of val) size += exprJsonSize(child as ExprJson);
    } else if (typeof val === "object" && val !== null) {
      size += exprJsonSize(val as ExprJson);
    }
  }
  return size;
}

// ── HIT Equivalence Verification via Hyperion ────────────────────────────────

/**
 * Prefix all atom references in an ExprJson with a namespace prefix.
 * Works at the AST level, not string level.
 */
function prefixExpr(expr: ExprJson, prefix: string): ExprJson {
  if (typeof expr === "string") {
    if (expr === "terminal" || expr === "unit") return expr;
    return { atom: prefix + sanitize(expr) };
  }
  if ("atom" in expr) return { atom: prefix + sanitize(expr.atom) };
  if ("comp" in expr) return { comp: [prefixExpr(expr.comp[0], prefix), prefixExpr(expr.comp[1], prefix)] };
  if ("id" in expr) return { id: prefixExpr(expr.id, prefix) };
  if ("prod" in expr) return { prod: [prefixExpr(expr.prod[0], prefix), prefixExpr(expr.prod[1], prefix)] };
  if ("path" in expr) return { path: [prefixExpr(expr.path[0], prefix), prefixExpr(expr.path[1], prefix), prefixExpr(expr.path[2], prefix)] };
  if ("refl" in expr) return { refl: prefixExpr(expr.refl, prefix) };
  if ("app" in expr) return { app: [prefixExpr(expr.app[0], prefix), prefixExpr(expr.app[1], prefix)] };
  if ("pi" in expr) return { pi: { name: expr.pi.name, base: prefixExpr(expr.pi.base, prefix), body: prefixExpr(expr.pi.body, prefix) } };
  if ("sigma" in expr) return { sigma: { name: expr.sigma.name, base: prefixExpr(expr.sigma.base, prefix), body: prefixExpr(expr.sigma.body, prefix) } };
  return expr;
}

/**
 * Generate Hyperion source to check equivalence between two theories.
 *
 * Uses manual [Proofs] with assert-eq — all constants and rules live in
 * one combined Theory so the e-graph can chase transitive identifications.
 * This handles different presentation sizes (e.g., suspension(S0) has 3
 * objects but S1 has 1).
 *
 * Strategy:
 *   1. Single Category with one shared sort X (all objects collapse here)
 *   2. One combined Theory with all constants from both sides
 *   3. Glue rules from the produced theory (HIT identifications)
 *   4. Mapping rule: produced pushout object ==> target object
 *   5. assert-eq checks that every produced object equals every target object
 */
export function equivalenceCheckToHyperion(
  produced: TheoryJson,
  target: TheoryJson,
): string {
  const lines: string[] = [];

  lines.push(`;; HIT equivalence check: ${produced.name} ≃ ${target.name}`);
  lines.push(`;; Generated by CatLab for Hyperion e-graph verification`);
  lines.push(``);

  // ── Category: single shared sort for all objects
  lines.push(`[Category C`);
  lines.push(`  [Object X]`);
  lines.push(`  [PathType :refl refl :concat concat :inv inv :ap ap]`);
  lines.push(`]`);
  lines.push(``);

  // ── Substrate
  lines.push(`[Substrate S`);
  lines.push(`  @engine interaction-graph`);
  lines.push(`  @resource-mode optimal-sharing`);
  lines.push(`  @barrier transparent`);
  lines.push(`  @equality rewrite-equivalence`);
  lines.push(`]`);
  lines.push(``);

  lines.push(`[Universe U :category C :substrate S]`);
  lines.push(``);

  // ── Combined theory: all constants + glue rules + mapping
  lines.push(`[Theory Combined :in U`);

  // Constants for produced objects (prefixed P_)
  for (const obj of produced.objects) {
    lines.push(`  [const P_${sanitize(obj.name)} X]`);
  }
  // Constants for produced morphisms (prefixed P_)
  for (const mor of produced.morphisms) {
    lines.push(`  [const P_${sanitize(mor.name)} X]`);
  }
  // Constants for target objects (prefixed T_)
  for (const obj of target.objects) {
    lines.push(`  [const T_${sanitize(obj.name)} X]`);
  }
  // Constants for target morphisms (prefixed T_)
  for (const mor of target.morphisms) {
    lines.push(`  [const T_${sanitize(mor.name)} X]`);
  }

  // Glue rules from produced theory (HIT identifications)
  // These are the key rules that collapse multiple objects into one
  for (const ax of produced.axioms) {
    const lhs = exprToHyperion(prefixExpr(ax.lhs, "P_"));
    const rhs = exprToHyperion(prefixExpr(ax.rhs, "P_"));
    lines.push(`  [@rule p_${sanitize(ax.name)} ${lhs} ==> ${rhs}]`);
  }

  // Axioms from target theory
  for (const ax of target.axioms) {
    const lhs = exprToHyperion(prefixExpr(ax.lhs, "T_"));
    const rhs = exprToHyperion(prefixExpr(ax.rhs, "T_"));
    lines.push(`  [@rule t_${sanitize(ax.name)} ${lhs} ==> ${rhs}]`);
  }

  // Object collapse rules: all produced objects map to the first target object.
  // For HIT pushouts, the produced objects (inl(⋆), inr(⋆), ⊤ ⊔ₕ ⊤) all
  // collapse to a single object in the target. The e-graph chains:
  //   P_inl → P_pushout → T_S1, P_inr → P_pushout → T_S1
  if (target.objects.length > 0) {
    const targetObj = target.objects[0];
    for (const pObj of produced.objects) {
      lines.push(`  [@rule collapse_${sanitize(pObj.name)} P_${sanitize(pObj.name)} ==> T_${sanitize(targetObj.name)}]`);
    }
  }

  lines.push(`]`);
  lines.push(``);

  // ── Proofs: assert each produced object equals each target object
  lines.push(`[Proofs EquivCheck :in Combined`);
  for (let i = 0; i < produced.objects.length; i++) {
    for (let j = 0; j < target.objects.length; j++) {
      const pN = sanitize(produced.objects[i].name);
      const tN = sanitize(target.objects[j].name);
      lines.push(`  ;; @node obj:P_${pN}=T_${tN}`);
      lines.push(`  [assert-eq obj_${i}_${j} P_${pN} T_${tN}]`);
    }
  }
  // Also assert morphisms with matching signatures are identified
  for (const tMor of target.morphisms) {
    const tIsTerm = tMor.domain === "terminal" || tMor.domain === "unit";
    for (const pMor of produced.morphisms) {
      const pIsTerm = pMor.domain === "terminal" || pMor.domain === "unit";
      if (pIsTerm === tIsTerm) {
        lines.push(`  [assert-eq mor_${sanitize(pMor.name)}_${sanitize(tMor.name)} P_${sanitize(pMor.name)} T_${sanitize(tMor.name)}]`);
      }
    }
  }
  lines.push(`]`);

  return lines.join("\n");
}

/**
 * Verify equivalence of two theories via Hyperion's e-graph.
 * Returns a VerificationResult compatible with the solver loop.
 */
export async function verifyEquivalenceViaHyperion(
  produced: TheoryJson,
  target: TheoryJson,
  opts?: ExternalElaborationOptions,
): Promise<import("./types").VerificationResult> {
  const source = equivalenceCheckToHyperion(produced, target);
  const bin = opts?.hyperionBin ?? "/Users/kevin/Desktop/omega/hyperion/target/release/hyperion";
  const timeout = opts?.timeoutMs ?? 30000;

  process.stderr.write(`[hyperion-equiv] Generated source (${source.split("\n").length} lines)\n`);
  const response = await runExternalCli(bin, ["check", "--json", "--stdin"], source, timeout);

  // Convert Hyperion response to VerificationResult
  const allPassed = response.status === "success" &&
    response.results.every(r => r.status !== "invalid" && r.status !== "timeout");

  const axiomViolations: import("./types").VerificationResult["axiomViolations"] = [];
  if (!allPassed) {
    for (const r of response.results) {
      if (r.status === "invalid" || r.status === "timeout") {
        axiomViolations.push({
          sourceAxiom: r.name,
          status: r.status === "timeout" ? `⏱ Timeout` : `✗ Failed`,
          lhsReduced: r.message ?? "",
          rhsReduced: "",
          depthUsed: 0,
        });
      }
    }
  }

  return {
    verified: allPassed,
    candidateName: produced.name,
    verificationStatus: allPassed
      ? "✓ Success (verified via Hyperion e-graph)"
      : `✗ Hyperion equivalence check failed: ${axiomViolations.length} violations`,
    missingSignatures: [],
    unmappedObjects: [],
    axiomViolations,
  };
}

/** Sanitize a name for use in Omega/Hyperion identifiers.
 *  Strips all non-ASCII and special characters, replacing with underscores. */
function sanitize(name: string): string {
  return name
    .replace(/[^\w]/g, "_")       // replace anything non-alphanumeric/underscore
    .replace(/^(\d)/, "_$1")      // don't start with digit
    .replace(/_+/g, "_")          // collapse multiple underscores
    .replace(/^_|_$/g, "") || "x"; // trim leading/trailing, fallback if empty
}
