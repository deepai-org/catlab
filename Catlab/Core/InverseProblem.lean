/-
  CatLab -- Inverse Problem Framework

  The unified "solve for X" architecture for all inverse CAS problems:
    - Categorification:       find C such that decategorify(C) ≅ target
    - Morita context:         find M such that moritaCheck(T₁, T₂, M) holds
    - Internalization:        find f : T_syntax → T_semantics
    - Pushout complement:     find X such that pushout(f, X) ≅ target
    - Doctrine satisfaction:  find f : Syn(D) → T

  Architecture:
    Proposer (LLM or search)
      → produces candidates : List Theory
    CAS Verifier
      → applies forwardOp : Theory → Option Theory to each candidate
      → diffs produced against target via computeStructuralDiff
      → returns VerificationResult (structured diff for LLM feedback)
    Proposer (next round)
      → reads missingSignatures, axiomViolations, and refines

  Two traps addressed here:

  Trap 1 — Verification is NOT O(N).
    Checking produced ≅ target is Graph Isomorphism in general.
    Checking if an axiom holds in a presentation reduces to the Word Problem
    (undecidable in general). We use bounded rewriting with explicit Timeout.

  Trap 2 — Name-based diff breaks under LLM renaming.
    If target needs "State" and the LLM proposes "System", a name diff
    wastes an API call on a trivial rename. We diff by structural signatures:
    position-normalized Expr shapes that are invariant under generator renaming.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
-- import Catlab.Core.KnuthBendix  -- DISABLED: KB completion has perf issues (see TODO above)
import Batteries.Data.HashMap

namespace CatLab

-- ============================================================
-- VerificationStatus: 3-way result replacing Bool
-- ============================================================

/-- The result of a bounded verification attempt.
    Replaces a simple `Bool` to distinguish "proved false" from
    "gave up after N steps" (the word problem is undecidable in general). -/
inductive VerificationStatus where
  | Success
  | Failed (reason : String)
  /-- The rewriter did not converge within `depth` steps.
      The candidate may still be correct — it just needs simpler generators
      or intermediate lemmas to make the proof tractable. -/
  | Timeout (depth : Nat)
  deriving Repr, Inhabited, BEq

instance : ToString VerificationStatus where
  toString
    | .Success      => "✓ Success"
    | .Failed r     => s!"✗ Failed: {r}"
    | .Timeout d    => s!"⏱ Timeout at depth {d}"

-- ============================================================
-- MorphismSignature: structural (name-independent) description
-- ============================================================

/-- A structural signature for a required morphism, invariant under renaming.
    Domain and codomain are normalized by object position (§0, §1, ...) so
    "A → B ⊗ A" and "State → Config ⊗ State" have the same signature: §0 → §1 ⊗ §0.
    This ensures the diff survives LLM renaming of generators. -/
structure MorphismSignature where
  /-- Position-normalized domain Expr: atoms replaced by §{index} -/
  domainShape   : Expr
  /-- Position-normalized codomain Expr: atoms replaced by §{index} -/
  codomainShape : Expr
  /-- Original name in the target theory, for human-readable feedback -/
  sourceName    : Name
  tags          : List (String × String) := []
  deriving Repr, Inhabited

instance : ToString MorphismSignature where
  toString s :=
    s!"Missing morphism '{s.sourceName}': {s.domainShape.toName} → {s.codomainShape.toName}"

-- ============================================================
-- AxiomViolation: bounded rewriting result for one axiom
-- ============================================================

/-- Result of checking whether a target axiom holds in the produced theory.
    Uses bounded rewriting (closed axioms only; quantified axioms require
    a unification engine and are reported as Timeout). -/
structure AxiomViolation where
  sourceAxiom : Generator2
  /-- LHS after up to `depthUsed` rewriting steps in the produced theory -/
  lhsReduced : Expr
  /-- RHS after up to `depthUsed` rewriting steps in the produced theory -/
  rhsReduced : Expr
  depthUsed  : Nat
  status     : VerificationStatus
  /-- Names of axioms fired during LHS normalization (last N steps).
      On timeout, this shows the LLM which rules are cycling. -/
  lhsTrace   : List Name := []
  /-- Names of axioms fired during RHS normalization (last N steps). -/
  rhsTrace   : List Name := []
  deriving Repr, Inhabited

instance : ToString AxiomViolation where
  toString v :=
    s!"Axiom '{v.sourceAxiom.id.name}': {v.status} " ++
    s!"(LHS→{v.lhsReduced.toName}, RHS→{v.rhsReduced.toName} after {v.depthUsed} steps)"

-- ============================================================
-- VerificationResult: the full structured diff
-- ============================================================

/-- The complete result of verifying one candidate against a target.
    Designed to be the primary input to the LLM's next proposal round.
    All diffs are structural (name-independent) to survive generator renaming. -/
structure VerificationResult where
  candidate         : Theory
  status            : VerificationStatus
  /-- The output of forwardOp(candidate); none if forwardOp failed to compile -/
  produced          : Option Theory
  verified          : Bool
  /-- Morphisms the target requires that no structurally-equivalent morphism
      in the produced theory satisfies. Keyed by shape, not by name. -/
  missingSignatures : List MorphismSignature
  /-- Objects in produced not structurally matched by any target object.
      These are generators the LLM hallucinated that serve no purpose. -/
  unmappedObjects   : List Name
  /-- Axioms from target that are absent or unverifiable in produced. -/
  axiomViolations   : List AxiomViolation
  deriving Repr, Inhabited

-- ============================================================
-- Structural normalization helpers
-- ============================================================

/-- Build a position index from a list of Generator0s: name → index.
    Used to normalize Exprs by position rather than by name. -/
private def buildObjIndexFromList (objs : List Generator0) : Std.HashMap Name Nat :=
  objs.foldl (fun (acc : Std.HashMap Name Nat × Nat) o =>
    (acc.1.insert o.id.name acc.2, acc.2 + 1)) ({}, 0) |>.1

/-- Build a position index: object name → its index in the theory's object list. -/
private def buildObjIndex (t : Theory) : Std.HashMap Name Nat :=
  buildObjIndexFromList t.objects

/-- Normalize an Expr by replacing object atoms with positional placeholders §0, §1, …
    Two Exprs with the same tree shape but different atom names become equal after
    normalization, provided their object positions correspond.
    Non-object atoms (morphism names, unknown atoms) are left unchanged. -/
private def normalizeShape (objIdx : Std.HashMap Name Nat) (e : Expr) : Expr :=
  e.mapNames fun n =>
    match objIdx[n]? with
    | some i => .root s!"§{i}"
    | none   => n

-- ============================================================
-- Bounded rewriting
-- ============================================================

/-- Size of an expression (number of AST nodes). Used for orienting rewrite
    rules so they always reduce toward smaller normal forms. -/
private def exprSize : Expr → Nat
  | .atom _      => 1
  | .unit        => 1
  | .terminal    => 1
  | .initial     => 1
  | .var _       => 1
  | .comp f g    => 1 + exprSize f + exprSize g
  | .id e        => 1 + exprSize e
  | .prod a b    => 1 + exprSize a + exprSize b
  | .tensor a b  => 1 + exprSize a + exprSize b
  | .hom a b     => 1 + exprSize a + exprSize b
  | .coprod a b  => 1 + exprSize a + exprSize b
  | .sigma _ b f => 1 + exprSize b + exprSize f
  | .pi _ b f    => 1 + exprSize b + exprSize f
  | .fiber m p   => 1 + exprSize m + exprSize p
  | .proj _ s    => 1 + exprSize s
  | .inj _ t     => 1 + exprSize t
  | .app f x     => 1 + exprSize f + exprSize x
  | .limit d     => 1 + exprSize d
  | .colimit d   => 1 + exprSize d
  | .natComponent n x => 1 + exprSize n + exprSize x

/-- Orient axioms so the larger side is always on the left (the rewrite target).
    This prevents expansion loops when operators like `opposite` swap LHS↔RHS,
    turning reductive rules into expansive ones. Equal-size axioms are left as-is. -/
private def orientAxioms (axioms : List Generator2) : List Generator2 :=
  axioms.map fun ax =>
    if exprSize ax.rightPath > exprSize ax.leftPath then
      { ax with leftPath := ax.rightPath, rightPath := ax.leftPath }
    else ax

/-- Try to fire one closed axiom at the root of `e`, left-to-right only.
    Quantified axioms are skipped (word problem).
    We do NOT fire right-to-left: symmetric firing creates ping-pong cycles
    (lhs→rhs on the left, rhs→lhs on the right) where both sides swap each
    step and never converge, causing false violations.
    Returns (result, axiomName) so the caller can build a rewrite trace. -/
private def fireAxiomRoot (ax : Generator2) (e : Expr) : Option (Expr × Name) :=
  if !ax.quantifiers.isEmpty then none   -- skip: word problem
  else if e == ax.leftPath then some (ax.rightPath, ax.id.name)
  else none

/-- One rewriting step: try all axioms at root, then recurse into the first
    subterm that fires (leftmost-outermost strategy).
    Returns `none` if the expression is already in normal form under these axioms.
    When a step fires, returns (result, axiomName) for the rewrite trace. -/
private partial def rewriteStep (axioms : List Generator2) (e : Expr) : Option (Expr × Name) :=
  -- Try root first
  match axioms.findSome? (fireAxiomRoot · e) with
  | some hit => some hit
  | none    =>
    -- Recurse into subterms (leftmost-outermost)
    match e with
    | .comp f g =>
      match rewriteStep axioms f with
      | some (f', n) => some (.comp f' g, n)
      | none    => (rewriteStep axioms g).map fun (g', n) => (.comp f g', n)
    | .id obj   => (rewriteStep axioms obj).map fun (o', n) => (.id o', n)
    | .prod a b =>
      match rewriteStep axioms a with
      | some (a', n) => some (.prod a' b, n)
      | none    => (rewriteStep axioms b).map fun (b', n) => (.prod a b', n)
    | .tensor a b =>
      match rewriteStep axioms a with
      | some (a', n) => some (.tensor a' b, n)
      | none    => (rewriteStep axioms b).map fun (b', n) => (.tensor a b', n)
    | .hom a b =>
      match rewriteStep axioms a with
      | some (a', n) => some (.hom a' b, n)
      | none    => (rewriteStep axioms b).map fun (b', n) => (.hom a b', n)
    | _ => none   -- atoms, unit, terminal, initial, var: already normal

/-- Reduce `e` using `axioms` as rewrite rules, up to `maxDepth` steps.
    Returns (normalForm, stepsUsed, rewriteTrace). If stepsUsed = maxDepth,
    the expression may not be fully normalized — report as Timeout, not failure.
    The rewrite trace records axiom names in firing order (last N steps kept). -/
def boundedNormalize (axioms : List Generator2) (e : Expr) (maxDepth : Nat)
    : Expr × Nat × List Name :=
  -- Keep only last `traceLimit` steps to avoid unbounded memory
  let traceLimit := min maxDepth 10
  let rec go (e : Expr) (depth : Nat) (trace : List Name) : Expr × Nat × List Name :=
    if depth >= maxDepth then (e, depth, trace)
    else match rewriteStep axioms e with
      | none    => (e, depth, trace)    -- normal form reached
      | some (e', axName) =>
        let trace' := if trace.length < traceLimit then trace ++ [axName]
                      else trace.tail! ++ [axName]  -- sliding window
        go e' (depth + 1) trace'
  go e 0 []

/-- Generate both orientations of each axiom (for equational closure).
    Filters to closed axioms only. Deduplicates symmetric axioms. -/
private def bothOrientations (axioms : List Generator2) : List Generator2 :=
  axioms.foldl (fun acc ax =>
    if !ax.quantifiers.isEmpty then acc   -- skip quantified
    else if ax.leftPath == ax.rightPath then acc  -- trivial
    else
      let fwd := ax
      let bwd := { ax with leftPath := ax.rightPath, rightPath := ax.leftPath }
      acc ++ [fwd, bwd]
  ) []

/-- Bounded equational closure: try to show lhs = rhs by exploring
    rewrite paths from BOTH expressions using both axiom orientations,
    checking for intersection. Uses a visited set to prevent cycles.
    Returns `true` if the expressions are provably equal. -/
def boundedEquationalCheck (axioms : List Generator2) (lhs rhs : Expr)
    (maxDepth : Nat := 50) : Bool :=
  let biAxioms := bothOrientations axioms
  -- BFS from lhs, collecting all reachable normal forms
  let rec expandFrom (frontier : List Expr) (visited : List Expr)
      (depth : Nat) : List Expr :=
    if depth >= maxDepth then visited
    else
      let next := frontier.foldl (fun acc e =>
        biAxioms.foldl (fun acc2 ax =>
          match rewriteStep [ax] e with
          | some (e', _) =>
            if visited.any (· == e') || acc2.any (· == e') then acc2
            else e' :: acc2
          | none => acc2
        ) acc
      ) []
      if next.isEmpty then visited
      else expandFrom next (visited ++ next) (depth + 1)
  -- Check if any form reachable from lhs equals any form reachable from rhs
  let fromLhs := lhs :: expandFrom [lhs] [lhs] 0
  fromLhs.any (· == rhs) ||
    -- Also expand from rhs and check intersection
    let fromRhs := rhs :: expandFrom [rhs] [rhs] 0
    fromLhs.any fun l => fromRhs.any fun r => l == r

-- ============================================================
-- Permutation helpers
-- ============================================================

/-- Insert `x` at every position in `xs`, returning all resulting lists. -/
private def insertEverywhere {α} (x : α) : List α → List (List α)
  | []      => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (y :: ·)

/-- All permutations of a list. O(n!) — only used for n ≤ 4. -/
private def allPermutations {α} : List α → List (List α)
  | []      => [[]]
  | x :: xs => (allPermutations xs).flatMap (insertEverywhere x)

-- ============================================================
-- Order-independent object mapping (V2 fix)
-- ============================================================

/-- Find the best mapping from target objects → produced objects.
    The naive zip-based position mapping breaks silently when the LLM reorders
    objects: [State, Config] paired with [Environment, System] crosses all types.

    Fix: for produced.objects.length ≤ 4 (covers ~all foundational theories),
    try all N! permutations of produced.objects and return the one that minimizes
    missing morphism signatures. For larger theories, fall back to position-based
    mapping (prompt engineering should handle ordering there).

    Returns (producedObjIndex, targetName → producedName map). -/
private def findBestObjMapping (produced target : Theory)
    : Std.HashMap Name Nat × Std.HashMap Name Name :=
  let targetObjIdx := buildObjIndex target
  let normTarget   := normalizeShape targetObjIdx

  -- Score a candidate permutation of produced.objects by counting missing signatures
  let scorePerm (perm : List Generator0) : Nat :=
    let permIdx  := buildObjIndexFromList perm
    let normProd := normalizeShape permIdx
    (target.morphisms.filter fun tm =>
      let tmDom := normTarget tm.domain
      let tmCod := normTarget tm.codomain
      !produced.morphisms.any fun pm =>
        normProd pm.domain == tmDom && normProd pm.codomain == tmCod).length

  let chosenPerm : List Generator0 :=
    if produced.objects.length <= 4 then
      -- Permutation search: find the object ordering with fewest missing signatures
      (allPermutations produced.objects).foldl (fun best perm =>
        if scorePerm perm < scorePerm best then perm else best)
        produced.objects
    else
      -- Large theory: trust ordering (use prompt engineering as V1 mitigation)
      produced.objects

  let prodObjIdx := buildObjIndexFromList chosenPerm
  let nameMap    := (chosenPerm.zip target.objects).foldl
    (fun acc (po, to_) => acc.insert to_.id.name po.id.name) {}
  (prodObjIdx, nameMap)

-- ============================================================
-- computeStructuralDiff: the core diff function
-- ============================================================

/-- Compute a structural (name-independent) diff of `produced` against `target`.
    This is the primary feedback signal for the LLM's next proposal round.

    Parameters:
      candidate  — the LLM's original proposal
      produced   — forwardOp(candidate) (what we got)
      target     — what we want
      maxDepth   — bound for the rewriting engine (default 200)

    Returns a VerificationResult with:
      - missingSignatures: morphisms the target needs that produced lacks (by shape)
      - unmappedObjects: objects in produced that don't correspond to any target object
      - axiomViolations: target axioms absent or unverifiable in produced -/
def computeStructuralDiff
    (candidate : Theory)
    (produced  : Theory)
    (target    : Theory)
    (maxDepth  : Nat := 200)
    : VerificationResult :=

  -- Find the best object mapping (order-independent for ≤ 4 objects)
  let (prodObjIdx, objNameMap) := findBestObjMapping produced target
  let targetObjIdx := buildObjIndex target

  let normProd   := normalizeShape prodObjIdx
  let normTarget := normalizeShape targetObjIdx

  -- ── Missing morphism signatures ───────────────────────────────────────────
  -- Uses the best-permutation object index, so a reordered LLM proposal like
  -- [Environment, System] matching target [State, Config] won't falsely fail.
  let missingSignatures : List MorphismSignature :=
    target.morphisms.filterMap fun tm =>
      let tmDom := normTarget tm.domain
      let tmCod := normTarget tm.codomain
      let hasMatch := produced.morphisms.any fun pm =>
        normProd pm.domain == tmDom && normProd pm.codomain == tmCod
      if hasMatch then none
      else some {
        domainShape   := tm.domain
        codomainShape := tm.codomain
        sourceName    := tm.id.name }

  -- ── Unmapped objects ──────────────────────────────────────────────────────
  -- Objects in produced beyond target's count are "hallucinated" generators.
  -- We report the surplus by count (exact identity is less important than
  -- knowing you have too many).
  let unmappedObjects : List Name :=
    if produced.objects.length > target.objects.length then
      produced.objects.drop target.objects.length |>.map (·.id.name)
    else []

  -- ── Axiom violations ─────────────────────────────────────────────────────
  -- Strategy: normalize both LHS and RHS of each target axiom using produced's
  -- axioms as rewrite rules, after mapping target atoms to produced atoms by
  -- position. If they converge to the same normal form → axiom holds.
  -- If not, report the (partially reduced) forms with status.
  --
  -- Position mapping: §i in target ↔ §i in produced. This assumes the forward
  -- operator preserves object order (true for decategorify, pushout, etc.).
  -- When object counts differ, we report Timeout (mapping is ambiguous).
  let axiomViolations : List AxiomViolation :=
    if produced.objects.length != target.objects.length then
      -- Object count mismatch: can't reliably translate axioms
      target.axioms.map fun ax =>
        { sourceAxiom := ax, lhsReduced := ax.leftPath, rhsReduced := ax.rightPath,
          depthUsed := 0,
          status := .Timeout 0  -- "ambiguous translation, not a proof of failure"
        }
    else
      -- Same object count: translate target axioms into produced's naming using
      -- the best-permutation object map (order-independent for ≤ 4 objects).
      -- Also build a morphism name map by matching structural signatures
      -- (position-normalized domain/codomain shapes).
      let morNameMap : Std.HashMap Name Name :=
        target.morphisms.foldl (fun acc tm =>
          let tmDom := normTarget tm.domain
          let tmCod := normTarget tm.codomain
          match produced.morphisms.find? fun pm =>
            normProd pm.domain == tmDom && normProd pm.codomain == tmCod with
          | some pm => acc.insert tm.id.name pm.id.name
          | none    => acc
        ) {}
      let fullNameMap : Std.HashMap Name Name :=
        morNameMap.fold (fun acc k v => acc.insert k v) objNameMap
      let translate (e : Expr) : Expr :=
        e.mapNames fun n =>
          match fullNameMap[n]? with
          | some n' => n'
          | none    => n
      -- NOTE: KB completion (KnuthBendix.completeTheory) is implemented but
      -- currently DISABLED due to performance issues — critical pair computation
      -- diverges on our theory sizes, pegging CPU at 100% indefinitely. The
      -- unify/criticalPairsFrom functions need proper depth limits or a different
      -- overlap strategy before KB can be safely enabled. See KnuthBendix.lean.
      --
      -- TODO: Fix KB completion performance, then re-enable here as:
      --   let kbRules := KnuthBendix.completeTheory produced.axioms
      --   ... normalize with kbRules as first pass ...
      let oriented := orientAxioms produced.axioms
      target.axioms.filterMap fun ax =>
        let lhsTrans := translate ax.leftPath
        let rhsTrans := translate ax.rightPath
        -- Fast path: axiom is directly present in produced (most common case,
        -- and the only tractable case for quantified axioms where rewriting
        -- is skipped). This handles produced == target correctly.
        let directlyPresent := produced.axioms.any fun pax =>
          (pax.leftPath == lhsTrans && pax.rightPath == rhsTrans) ||
          (pax.leftPath == rhsTrans && pax.rightPath == lhsTrans)
        if directlyPresent then none   -- trivially satisfied as a stated axiom
        else
          -- Bounded L→R rewriting (size-oriented axioms)
          let (lhsNorm, lhsD, lhsTrace) := boundedNormalize oriented lhsTrans maxDepth
          let (rhsNorm, rhsD, rhsTrace) := boundedNormalize oriented rhsTrans maxDepth
          if lhsNorm == rhsNorm then none
          else
            -- NOTE: boundedEquationalCheck (bidirectional BFS) is DISABLED —
            -- it diverges on theories with same-shaped morphisms, generating
            -- exponential frontiers. TODO: fix with proper visited HashSet.
            let depth := max lhsD rhsD
              let status : VerificationStatus :=
                if depth >= maxDepth then .Timeout maxDepth
                else .Failed s!"LHS→{lhsNorm.toName}, RHS→{rhsNorm.toName}"
              some { sourceAxiom := ax, lhsReduced := lhsNorm, rhsReduced := rhsNorm,
                     depthUsed := depth, status,
                     lhsTrace := lhsTrace, rhsTrace := rhsTrace }

  -- ── Overall status ────────────────────────────────────────────────────────
  let hasTimeout := axiomViolations.any fun v =>
    match v.status with | .Timeout _ => true | _ => false

  let verified := missingSignatures.isEmpty && axiomViolations.isEmpty

  let overallStatus : VerificationStatus :=
    if verified then .Success
    else if hasTimeout then .Timeout maxDepth
    else .Failed s!"{missingSignatures.length} missing signatures, \
                    {axiomViolations.length} axiom violations, \
                    {unmappedObjects.length} unmapped objects"

  { candidate, status := overallStatus, produced := some produced, verified,
    missingSignatures, unmappedObjects, axiomViolations }

-- ============================================================
-- solveInverse: the main search loop
-- ============================================================

/-- Try each candidate in order; return the first that passes verification.
    `forward` is the CAS operator being inverted (e.g., `fun c => some (decategorify c s)`).
    Returns `none` if no candidate passes within the given depth bound. -/
def solveInverse
    (target     : Theory)
    (forward    : Theory → Option Theory)
    (candidates : List Theory)
    (maxDepth   : Nat := 200)
    : Option (Theory × VerificationResult) :=
  candidates.findSome? fun candidate =>
    match forward candidate with
    | none          => none   -- forward operator failed to compile this candidate
    | some produced =>
      let result := computeStructuralDiff candidate produced target maxDepth
      if result.verified then some (candidate, result) else none

/-- Evaluate all candidates and return every VerificationResult.
    Used for iterative LLM feedback: even failing results carry structured
    diffs (missingSignatures, axiomViolations) that guide the next proposal. -/
def evaluateAll
    (target     : Theory)
    (forward    : Theory → Option Theory)
    (candidates : List Theory)
    (maxDepth   : Nat := 200)
    : List VerificationResult :=
  candidates.map fun candidate =>
    match forward candidate with
    | none =>
      { candidate, status := .Failed "forward operator failed to compile",
        produced := none, verified := false,
        missingSignatures := [], unmappedObjects := [], axiomViolations := [] }
    | some produced =>
      computeStructuralDiff candidate produced target maxDepth

-- ============================================================
-- Human-readable summary
-- ============================================================

def VerificationResult.summary (r : VerificationResult) : String :=
  let prod := r.produced.map (·.name) |>.getD "(failed to compile)"
  s!"Candidate: {r.candidate.name}\n" ++
  s!"Produced:  {prod}\n" ++
  s!"Status:    {r.status}\n" ++
  (if r.missingSignatures.isEmpty then ""
   else "Missing morphism shapes:\n" ++
        (r.missingSignatures.map (fun s => s!"  • {s}") |> String.intercalate "\n") ++ "\n") ++
  (if r.unmappedObjects.isEmpty then ""
   else s!"Unmapped objects: {r.unmappedObjects.map toString |> String.intercalate ", "}\n") ++
  (if r.axiomViolations.isEmpty then ""
   else "Axiom violations:\n" ++
        (r.axiomViolations.map (fun v => s!"  • {v}") |> String.intercalate "\n") ++ "\n")

end CatLab
