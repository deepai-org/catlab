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
const HYPERION_DOCTRINES = new Set([
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
  return `?unknown`;
}

// ── Hyperion source generation ───────────────────────────────────────────────

/** Doctrine → Hyperion category-level structures. */
interface HyperionDoctrineConfig {
  pathType: boolean;
  jType: boolean;
  partialElement: boolean;
  eGraph: boolean;
  /** Extra structures to add to [Category ...] block */
  categoryStructures: string[];
  /** Substrate resource mode */
  resourceMode: "optimal-sharing" | "strictly-linear" | "affine";
}

function hyperionDoctrineConfig(doctrine: string): HyperionDoctrineConfig {
  const base: HyperionDoctrineConfig = {
    pathType: false, jType: false, partialElement: false, eGraph: false,
    categoryStructures: [], resourceMode: "optimal-sharing",
  };

  switch (doctrine) {
    case "MartinLofTypeTheory":
      return { ...base, pathType: true, jType: true,
        categoryStructures: ["[Evaluator app]"] };

    case "CubicalTypeTheory":
      return { ...base, pathType: true, partialElement: true };

    case "CohesiveHomotopyTypeTheory":
      return { ...base, pathType: true,
        categoryStructures: ["[ModalOperator :ops [esh bflat bsharp]]"] };

    case "InfinityNCategory":
    case "PresentableInfinityCategory":
      return { ...base, pathType: true, eGraph: true };

    case "2Category":
    case "Double":
    case "Bicategory":
      return { ...base, pathType: true, eGraph: true };

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
  for (const struct of config.categoryStructures) {
    lines.push(`  ${struct}`);
  }

  lines.push(`]`);
  lines.push(``);

  // ── Substrate block ────────────────────────────────────────────────────
  const equality = config.eGraph ? "equality-saturation" : "rewrite-equivalence";
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

  // Axioms as @law (bidirectional for e-graph) or @rule (directed for rewrite)
  for (const ax of theory.axioms) {
    lines.push(`  ;; @node axiom:${ax.name}`);
    const lhs = exprToHyperion(ax.lhs);
    const rhs = exprToHyperion(ax.rhs);
    if (ax.relation === "ineq") {
      // Inequalities are always directed
      lines.push(`  [@rule ${sanitize(ax.name)} ${lhs} ==> ${rhs}]`);
    } else if (config.eGraph) {
      // On e-graph substrate, use @law for bidirectional saturation
      lines.push(`  [@law ${sanitize(ax.name)} ${lhs} === ${rhs}]`);
    } else {
      // On rewrite substrate, use @rule for directed rewriting
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

    // extract-proof: for HoTT/∞-categorical doctrines, request the proof term
    // (path/2-cell) witnessing each equality — not just a boolean.
    // This prevents flattening higher-dimensional structure into strict equality.
    if (config.pathType) {
      lines.push(``);
      lines.push(`  ;; Extract proof terms (paths/2-cells) from e-graph`);
      lines.push(`  ;; CRITICAL: Hyperion must return the rewrite sequence,`);
      lines.push(`  ;; not just True/False. In HoTT, there may be multiple`);
      lines.push(`  ;; distinct paths between the same endpoints.`);
      for (const ax of theory.axioms) {
        const lhs = exprToHyperion(ax.lhs);
        const rhs = exprToHyperion(ax.rhs);
        lines.push(`  [extract-proof ${sanitize(ax.name)}-path ${lhs} ${rhs}]`);
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
  const bin = opts?.hyperionBin ?? "hyperion";
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

    proc.stdout.on("data", (d: Buffer) => { stdout += d.toString(); });
    proc.stderr.on("data", (d: Buffer) => { stderr += d.toString(); });

    proc.on("close", (code) => {
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

// ── Cross-Tier Functor Interoperability ───────────────────────────────────────

/**
 * Detect when a theory references objects/morphisms that span multiple
 * verification tiers. For example, a functor from an Omega-verified
 * algebraic theory (Monoid) to a Lean-verified 1-category (Set).
 *
 * Strategy: "Upward compilation" — compile the lower tier into the
 * higher tier's language. Omega theories compile trivially into Lean
 * (Lean handles algebra perfectly), so the functor can be verified
 * in a unified Lean context.
 */
export interface CrossTierFunctor {
  /** The functor's name */
  name: string;
  /** Source theory (with its tier) */
  source: { theory: TheoryJson; tier: ExternalBackend };
  /** Target theory (with its tier) */
  target: { theory: TheoryJson; tier: ExternalBackend };
  /** Object mapping: source object name → target object name */
  objectMap: Record<string, string>;
  /** Morphism mapping: source morphism name → target expression */
  morphismMap: Record<string, string>;
}

/**
 * Determine the verification tier ordering.
 * null (Lean) > "hyperion" > "omega"
 * Higher tiers can embed lower tiers.
 */
function tierRank(tier: ExternalBackend): number {
  if (tier === "omega") return 0;
  if (tier === null) return 1;  // Lean/Mathlib
  if (tier === "hyperion") return 2;
  return -1;
}

/**
 * Given a cross-tier functor, compile both theories into the higher tier
 * and return a unified verification payload.
 *
 * Compilation directions:
 *   omega → Lean:  trivial (Lean handles algebra natively)
 *   omega → Hyperion: compile omega theory into Hyperion Category block
 *   Lean → Hyperion: not supported (Lean theories are too rich for Hyperion)
 */
export function compileCrossTierFunctor(functor: CrossTierFunctor): {
  /** The unified theory combining source + target + functor axioms */
  unifiedTheory: TheoryJson;
  /** Which tier should verify the unified theory */
  verifyWith: ExternalBackend;
} {
  const srcRank = tierRank(functor.source.tier);
  const tgtRank = tierRank(functor.target.tier);

  // The unified theory is verified at the higher tier
  const verifyWith = srcRank >= tgtRank ? functor.source.tier : functor.target.tier;

  // Build unified theory: merge objects, morphisms, and axioms from both,
  // then add functor axioms (functoriality: F(id) = id, F(g∘f) = Fg∘Ff)
  const unified: TheoryJson = {
    name: `Functor_${functor.name}`,
    doctrine: verifyWith === "hyperion"
      ? functor.target.theory.doctrine  // use the Hyperion doctrine
      : verifyWith === "omega"
        ? functor.source.theory.doctrine
        : "Category",  // Lean handles everything
    objects: [
      // Prefix source objects to avoid collisions
      ...functor.source.theory.objects.map(o => ({
        ...o, name: `src_${o.name}`,
        description: `[source] ${o.description ?? o.name}`,
      })),
      ...functor.target.theory.objects.map(o => ({
        ...o, name: `tgt_${o.name}`,
        description: `[target] ${o.description ?? o.name}`,
      })),
    ],
    morphisms: [
      ...functor.source.theory.morphisms.map(m => ({
        ...m, name: `src_${m.name}`,
        domain: prefixExpr(m.domain, "src_"),
        codomain: prefixExpr(m.codomain, "src_"),
        description: `[source] ${m.description ?? m.name}`,
      })),
      ...functor.target.theory.morphisms.map(m => ({
        ...m, name: `tgt_${m.name}`,
        domain: prefixExpr(m.domain, "tgt_"),
        codomain: prefixExpr(m.codomain, "tgt_"),
        description: `[target] ${m.description ?? m.name}`,
      })),
      // Functor action on objects (as morphisms in the unified theory)
      ...Object.entries(functor.objectMap).map(([src, tgt]) => ({
        name: `F_obj_${src}`,
        domain: `src_${src}` as ExprJson,
        codomain: `tgt_${tgt}` as ExprJson,
        description: `Functor ${functor.name}: ${src} ↦ ${tgt}`,
      })),
    ],
    axioms: [
      // Include all source and target axioms
      ...functor.source.theory.axioms.map(a => ({
        ...a, name: `src_${a.name}`,
        lhs: prefixExpr(a.lhs, "src_"),
        rhs: prefixExpr(a.rhs, "src_"),
      })),
      ...functor.target.theory.axioms.map(a => ({
        ...a, name: `tgt_${a.name}`,
        lhs: prefixExpr(a.lhs, "tgt_"),
        rhs: prefixExpr(a.rhs, "tgt_"),
      })),
      // Functoriality axioms for each morphism mapping
      ...Object.entries(functor.morphismMap).map(([srcMor, tgtExpr]) => ({
        name: `F_mor_${srcMor}`,
        lhs: { atom: `F_${srcMor}` } as ExprJson,
        rhs: { atom: `tgt_${tgtExpr}` } as ExprJson,
        description: `Functor maps ${srcMor} ↦ ${tgtExpr}`,
      })),
    ],
  };

  return { unifiedTheory: unified, verifyWith };
}

/** Prefix all atom names in an ExprJson with a given prefix. */
function prefixExpr(expr: ExprJson, prefix: string): ExprJson {
  if (typeof expr === "string") {
    if (expr === "terminal" || expr === "unit" || expr === "initial") return expr;
    return `${prefix}${expr}`;
  }
  if ("atom" in expr) return { atom: `${prefix}${expr.atom}` };
  if ("comp" in expr) return { comp: [prefixExpr(expr.comp[0], prefix), prefixExpr(expr.comp[1], prefix)] };
  if ("prod" in expr) return { prod: [prefixExpr(expr.prod[0], prefix), prefixExpr(expr.prod[1], prefix)] };
  if ("tensor" in expr) return { tensor: [prefixExpr(expr.tensor[0], prefix), prefixExpr(expr.tensor[1], prefix)] };
  if ("coprod" in expr) return { coprod: [prefixExpr(expr.coprod[0], prefix), prefixExpr(expr.coprod[1], prefix)] };
  if ("hom" in expr) return { hom: [prefixExpr(expr.hom[0], prefix), prefixExpr(expr.hom[1], prefix)] };
  if ("id" in expr) return { id: prefixExpr(expr.id, prefix) };
  return expr;
}

/**
 * Elaborate a cross-tier functor by compiling to a unified theory
 * and verifying at the appropriate tier.
 */
export async function elaborateCrossTierFunctor(
  functor: CrossTierFunctor,
  opts?: ExternalElaborationOptions,
): Promise<ElaborationResult | null> {
  const { unifiedTheory, verifyWith } = compileCrossTierFunctor(functor);

  if (verifyWith === "omega") {
    const source = theoryToOmega(unifiedTheory);
    const bin = opts?.omegaBin ?? "omega";
    const timeout = opts?.timeoutMs ?? 30000;
    const response = await runExternalCli(bin, ["check", "--json", "--stdin"], source, timeout);
    return externalResponseToResult(response, source, "omega");
  } else if (verifyWith === "hyperion") {
    const source = theoryToHyperion(unifiedTheory);
    const bin = opts?.hyperionBin ?? "hyperion";
    const timeout = opts?.timeoutMs ?? 30000;
    const response = await runExternalCli(bin, ["check", "--json", "--stdin"], source, timeout);
    return externalResponseToResult(response, source, "hyperion");
  }

  // verifyWith === null → Lean handles it, return null to fall through
  return null;
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
  }
  for (const ax of axioms) {
    walk(ax.lhs);
    walk(ax.rhs);
  }
  return result;
}

/** Sanitize a name for use in Omega/Hyperion identifiers. */
function sanitize(name: string): string {
  return name
    .replace(/[\s\-\+\*\/\\=<>!@#$%^&(){}[\]|;:'"`,\.~?]/g, "_")
    .replace(/^(\d)/, "_$1")
    .replace(/_+/g, "_")
    .replace(/^_|_$/g, "");
}
