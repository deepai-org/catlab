/-
  CatLab -- Well-formedness Validation

  Checks that a theory is internally consistent:
  - All morphism domains/codomains reference declared objects
  - All axiom paths reference declared morphisms
  - No duplicate generator names
  - Doctrine constraints are satisfied
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Batteries.Data.HashMap

namespace CatLab

/-- A validation error -/
inductive ValidationError where
  | duplicateName (name : Name)
  | undeclaredObject (referencedIn : String) (name : Name)
  | undeclaredMorphism (referencedIn : String) (name : Name)
  | doctrineViolation (message : String)
  | boundaryMismatch (morphismName : String) (expected : String) (got : String)
  deriving Repr, Inhabited

instance : ToString ValidationError where
  toString
    | .duplicateName n => s!"Duplicate generator name: {n}"
    | .undeclaredObject ctx n => s!"Undeclared object '{n}' referenced in {ctx}"
    | .undeclaredMorphism ctx n => s!"Undeclared morphism '{n}' referenced in {ctx}"
    | .doctrineViolation msg => s!"Doctrine violation: {msg}"
    | .boundaryMismatch m e g => s!"Boundary mismatch in '{m}': expected codomain {e}, got domain {g}"

/-- Check for duplicate names across all generators.
    Uses a HashMap for O(N) total instead of O(N²) seen-list scanning. -/
def checkDuplicates (t : Theory) : List ValidationError :=
  let names := t.allNames
  let (_, dups) := names.foldl (fun acc n =>
    let (seen, errs) := acc
    if seen[n]? == some true then (seen, ValidationError.duplicateName n :: errs)
    else (seen.insert n true, errs))
    (({} : Std.HashMap Name Bool), ([] : List ValidationError))
  dups

/-- Build a set of all known generator names for O(1) membership tests. -/
private def knownNameSet (t : Theory) : Std.HashMap Name Bool :=
  t.allNames.foldl (fun acc n => acc.insert n true) {}

/-- Check that morphism domain/codomain atoms reference declared objects or morphisms -/
def checkMorphismReferences (t : Theory) : List ValidationError :=
  let known := knownNameSet t
  t.morphisms.flatMap fun m =>
    let domErrors := m.domain.atoms.filterMap fun a =>
      if known[a]? == some true then none
      else some (ValidationError.undeclaredObject s!"morphism '{m.id.name}' domain" a)
    let codErrors := m.codomain.atoms.filterMap fun a =>
      if known[a]? == some true then none
      else some (ValidationError.undeclaredObject s!"morphism '{m.id.name}' codomain" a)
    domErrors ++ codErrors

/-- Check that axiom paths reference declared generators -/
def checkAxiomReferences (t : Theory) : List ValidationError :=
  let known := knownNameSet t
  t.axioms.flatMap fun ax =>
    (ax.leftPath.atoms ++ ax.rightPath.atoms).filterMap fun a =>
      if known[a]? == some true then none
      else some (ValidationError.undeclaredMorphism s!"axiom '{ax.id.name}'" a)

/-- Check doctrine-specific constraints -/
def checkDoctrine (t : Theory) : List ValidationError :=
  match t.doctrine.doctrine with
  | .LawvereTheory =>
    -- Lawvere theories must have at least one sort
    if t.objects.isEmpty then [.doctrineViolation "Lawvere theory must have at least one sort"]
    else []
  | .Topos =>
    -- Topoi should have a subobject classifier
    let hasOmega := t.objects.any fun o => o.id.name == Name.root "Ω"
    if !hasOmega then [.doctrineViolation "Topos should have subobject classifier Ω"]
    else []
  | _ => []

/-- Infer the codomain of an expression using a prebuilt morphism index (O(1) per atom).
    For compositions, returns the codomain of the second factor. -/
private partial def inferCodomain (idx : Std.HashMap Name Generator1) (e : Expr) : Option Expr :=
  match e with
  | .atom gid => (idx[gid.name]?).map (·.codomain)
  | .comp _ g => inferCodomain idx g
  | .id obj => some obj
  | _ => none

/-- Infer the domain of an expression using a prebuilt morphism index. -/
private partial def inferDomain (idx : Std.HashMap Name Generator1) (e : Expr) : Option Expr :=
  match e with
  | .atom gid => (idx[gid.name]?).map (·.domain)
  | .comp f _ => inferDomain idx f
  | .id obj => some obj
  | _ => none

/-- Check that all Expr.comp nodes have matching boundaries:
    in `comp f g`, the codomain of f must match the domain of g. -/
private partial def checkCompBoundaries (idx : Std.HashMap Name Generator1) (context : String) (e : Expr) : List ValidationError :=
  match e with
  | .comp f g =>
    let innerErrors := checkCompBoundaries idx context f ++ checkCompBoundaries idx context g
    let boundaryError := match inferCodomain idx f, inferDomain idx g with
      | some cod, some dom =>
        if cod.beq dom then []
        else [ValidationError.boundaryMismatch context s!"{cod.toName}" s!"{dom.toName}"]
      | _, _ => []  -- can't infer; skip
    innerErrors ++ boundaryError
  | .prod a b | .coprod a b | .hom a b | .tensor a b =>
    checkCompBoundaries idx context a ++ checkCompBoundaries idx context b
  | .id obj => checkCompBoundaries idx context obj
  | .sigma _ base fam | .pi _ base fam =>
    checkCompBoundaries idx context base ++ checkCompBoundaries idx context fam
  | .fiber m p => checkCompBoundaries idx context m ++ checkCompBoundaries idx context p
  | .proj _ s => checkCompBoundaries idx context s
  | .inj _ s => checkCompBoundaries idx context s
  | .app f x => checkCompBoundaries idx context f ++ checkCompBoundaries idx context x
  | .limit d | .colimit d => checkCompBoundaries idx context d
  | .natComponent n x => checkCompBoundaries idx context n ++ checkCompBoundaries idx context x
  | .path A x y => checkCompBoundaries idx context A ++ checkCompBoundaries idx context x ++ checkCompBoundaries idx context y
  | .refl x => checkCompBoundaries idx context x
  | .pathJ mot rc tgt pf => checkCompBoundaries idx context mot ++ checkCompBoundaries idx context rc ++ checkCompBoundaries idx context tgt ++ checkCompBoundaries idx context pf
  | .hcomp sys base => checkCompBoundaries idx context sys ++ checkCompBoundaries idx context base
  | .fill sys base => checkCompBoundaries idx context sys ++ checkCompBoundaries idx context base
  | .coe p a => checkCompBoundaries idx context p ++ checkCompBoundaries idx context a
  | .lam _ dom body => checkCompBoundaries idx context dom ++ checkCompBoundaries idx context body
  | _ => []

/-- Check composition boundaries across all axioms in a theory -/
def checkCompositionBoundaries (t : Theory) : List ValidationError :=
  -- Build morphism index once; reused for every axiom boundary check
  let idx := t.morphismIndex
  t.axioms.flatMap fun ax =>
    checkCompBoundaries idx s!"axiom '{ax.id.name}' LHS" ax.leftPath ++
    checkCompBoundaries idx s!"axiom '{ax.id.name}' RHS" ax.rightPath

-- ============================================================
-- Universe Consistency (Option C: Constraint Solver)
--
-- Assigns each object/expression a universe level variable and
-- checks that all constraints are satisfiable. Catches:
--   1. U : U (universe stratification)
--   2. Impredicativity (Π(x:A).B must be at max(level(A), level(B)))
-- ============================================================

/-- Infer the universe level of an Expr. Returns `none` for expressions
    without a meaningful universe level (morphisms, bound vars, etc.).
    Objects get their level from the objLevel map. -/
private partial def inferLevel (objLevel : Std.HashMap Name Nat) (e : Expr) : Option Nat :=
  match e with
  | .univ n       => some (n + 1)    -- U_n : U_{n+1}, so U_n lives at level n+1
  | .terminal     => some 0
  | .initial      => some 0
  | .unit         => some 0
  | .atom gid     => objLevel[gid.name]?
  | .prod a b     =>
    match inferLevel objLevel a, inferLevel objLevel b with
    | some la, some lb => some (max la lb)
    | _, _ => none
  | .coprod a b   =>
    match inferLevel objLevel a, inferLevel objLevel b with
    | some la, some lb => some (max la lb)
    | _, _ => none
  | .sigma _ base body =>
    match inferLevel objLevel base, inferLevel objLevel body with
    | some lb, some lf => some (max lb lf)
    | _, _ => none
  | .pi _ base body =>
    -- Predicativity: Π(x:A).B lives at max(level(A), level(B))
    match inferLevel objLevel base, inferLevel objLevel body with
    | some lb, some lf => some (max lb lf)
    | _, _ => none
  | .path A _ _   => inferLevel objLevel A    -- path type lives where A lives
  | .hom a b      =>
    match inferLevel objLevel a, inferLevel objLevel b with
    | some la, some lb => some (max la lb)
    | _, _ => none
  | _ => none

/-- Check universe consistency of a theory.
    Strategy: assign each object the minimum universe level consistent with
    its morphism signatures, then check for contradictions.

    A morphism f : A → B where A or B is `univ n` constrains:
      - If codomain is `univ n`: the domain type must live at level ≤ n
        (i.e., it classifies types at level n, so inputs are types at level ≤ n)
      - If domain is `univ n`: the codomain must live at level ≥ n+1
        (i.e., consuming a universe-level value requires being at least that level)

    A morphism f : A → A where A = `univ n` is fine (endomorphism on universe).
    But `code : univ n → U` and `decode : U → univ n` with `decode ∘ code = id`
    forces `U` to be isomorphic to `univ n`, meaning `U` must live at level n+1.
    If `self : 1 → U` with `decode(self) = U`, then U ∈ U, requiring level(U) > level(U). -/
def checkUniverseConsistency (t : Theory) : List ValidationError :=
  -- Only check for MLTT / HoTT theories (categorical theories don't have universe issues)
  match t.doctrine.doctrine with
  | .MartinLofTypeTheory | .CubicalTypeTheory | .CohesiveHomotopyTypeTheory => doCheck t
  | _ => []
where
  doCheck (t : Theory) : List ValidationError :=
    -- Phase 1: Assign initial universe levels to objects
    -- Start everything at level 0, then propagate constraints upward
    let initLevels : Std.HashMap Name Nat :=
      t.objects.foldl (fun acc o => acc.insert o.id.name 0) {}

    -- Phase 2: Propagate constraints from morphisms (fixed-point iteration)
    -- A morphism f : A → univ n means A classifies types at level n, so level(A) ≥ n+1
    -- A morphism f : univ n → A means A receives universe-level data, so level(A) ≥ n+1
    let rec propagate (levels : Std.HashMap Name Nat) (fuel : Nat) : Std.HashMap Name Nat :=
      match fuel with
      | 0 => levels
      | fuel' + 1 =>
        let newLevels := t.morphisms.foldl (fun acc m =>
          let domLevel := inferLevel acc m.domain
          let codLevel := inferLevel acc m.codomain
          -- If domain is univ n, codomain object must be at level ≥ n+1
          let acc' := match m.domain with
            | .univ n => match m.codomain with
              | .atom gid =>
                let cur := acc[gid.name]?.getD 0
                if cur < n + 1 then acc.insert gid.name (n + 1) else acc
              | _ => acc
            | _ => acc
          -- If codomain is univ n, domain object must be at level ≤ n (type classification)
          -- But if domain is also an object, it needs to live at a level where it can
          -- be a member of univ n, meaning the TYPE of domain needs to be ≤ univ n
          -- i.e., level(domain) ≤ n
          let acc'' := match m.codomain with
            | .univ n => match m.domain with
              | .atom gid =>
                -- This is fine: domain maps into universe, no level bump needed
                -- But if there's a reverse morphism, constraints will propagate
                acc'
              | _ => acc'
            | _ => acc'
          -- Propagate through Σ/Π types in domain/codomain
          let acc''' := match domLevel, codLevel with
            | some dl, some cl =>
              -- If an object appears in both domain and codomain at different levels,
              -- it must be at the max
              t.objects.foldl (fun a o =>
                let n := o.id.name
                let inDom := m.domain.atoms.any (· == n)
                let inCod := m.codomain.atoms.any (· == n)
                if inDom || inCod then
                  let cur := a[n]?.getD 0
                  let req := if inDom && inCod then max dl cl
                             else if inDom then dl else cl
                  if cur < req then a.insert n req else a
                else a
              ) acc''
            | _, _ => acc''
          acc'''
        ) levels
        if newLevels.toList.all (fun (k, v) => levels[k]?.getD 0 == v)
        then newLevels  -- Fixed point reached
        else propagate newLevels fuel'
    let finalLevels := propagate initLevels 20

    -- Phase 3: Check for contradictions
    -- Look for self-referential universe membership
    let errors := t.morphisms.foldl (fun acc m =>
      -- Pattern: decode : U → univ n with code : univ n → U
      -- If there exists `self : 1 → U` with axiom `comp(self, decode) = U`
      -- then U ∈ U, which requires level(U) > level(U) — contradiction
      match m.domain, m.codomain with
      | .atom domId, .univ n =>
        -- f : X → univ n  means X classifies types at level n
        -- Check if there's a reverse morphism univ n → X (making X ≅ univ n)
        let hasReverse := t.morphisms.any fun m' =>
          match m'.domain, m'.codomain with
          | .univ n', .atom codId => n' == n && codId.name == domId.name
          | _, _ => false
        if hasReverse then
          let objLevel := finalLevels[domId.name]?.getD 0
          -- X ≅ univ n means X must live at level n+1
          -- Check if any morphism puts X inside univ n (via an axiom like decode(self) = X)
          let hasSelfRef := t.axioms.any fun ax =>
            -- Check if any axiom equates something to the atom X
            -- where the LHS involves composing through decode
            let mentionsObj := ax.rightPath.atoms.any (· == domId.name) ||
                              ax.leftPath.atoms.any (· == domId.name)
            let mentionsDecode := ax.rightPath.atoms.any (· == m.id.name) ||
                                 ax.leftPath.atoms.any (· == m.id.name)
            mentionsObj && mentionsDecode
          if hasSelfRef then
            -- U ≅ univ n means U must live at level n+1
            -- But self-referential code means U ∈ univ n, requiring level(U) ≤ n
            -- This is always a contradiction: n+1 ≤ n is impossible
            ValidationError.doctrineViolation
              s!"Universe inconsistency: '{domId.name}' is isomorphic to univ {n} (level {n+1}) but contains a self-referential code. This violates universe stratification (Girard's paradox)." :: acc
          else acc
        else acc
      | _, _ => acc
    ) ([] : List ValidationError)
    errors

-- ============================================================
-- Strict Positivity for HITDecls
--
-- A HIT constructor is strictly positive if the type being defined
-- does NOT appear to the left of any arrow (→/Π) in the constructor's
-- body. Violations allow encoding Y-combinators → inconsistency.
--
-- Example violation: `bad_make : (Bad → Nat) → Bad`
--   Here `Bad` appears left of `→` in its own constructor.
-- ============================================================

/-- Check if a name appears in the "negative" (left-of-arrow) position in an Expr.
    Negative positions are:
      - Domain of a `pi` / function type
      - Domain of a `hom`
    Positive positions are everywhere else. -/
private partial def appearsNegative (target : Name) : Expr → Bool
  | .pi _ base body =>
    -- base is in negative position; body is in positive position
    -- (but body could contain more pi's that flip again)
    appearsAnywhere target base || appearsNegative target body
  | .hom dom cod =>
    appearsAnywhere target dom || appearsNegative target cod
  | .sigma _ base body =>
    appearsNegative target base || appearsNegative target body
  | .prod a b =>
    appearsNegative target a || appearsNegative target b
  | .coprod a b =>
    appearsNegative target a || appearsNegative target b
  | .path A x y =>
    appearsNegative target A || appearsNegative target x || appearsNegative target y
  | .comp f g => appearsNegative target f || appearsNegative target g
  | .app f x => appearsNegative target f || appearsNegative target x
  | .lam _ dom body => appearsAnywhere target dom || appearsNegative target body
  | _ => false
where
  /-- Check if a name appears anywhere in an expression. -/
  appearsAnywhere (target : Name) : Expr → Bool
    | .atom gid => gid.name == target
    | .comp f g => appearsAnywhere target f || appearsAnywhere target g
    | .prod a b | .coprod a b | .tensor a b | .hom a b =>
      appearsAnywhere target a || appearsAnywhere target b
    | .id e => appearsAnywhere target e
    | .sigma _ b f | .pi _ b f | .lam _ b f =>
      appearsAnywhere target b || appearsAnywhere target f
    | .path A x y =>
      appearsAnywhere target A || appearsAnywhere target x || appearsAnywhere target y
    | .refl x => appearsAnywhere target x
    | .app f x => appearsAnywhere target f || appearsAnywhere target x
    | .fiber m p => appearsAnywhere target m || appearsAnywhere target p
    | .proj _ s | .inj _ s => appearsAnywhere target s
    | .limit d | .colimit d => appearsAnywhere target d
    | .natComponent n x => appearsAnywhere target n || appearsAnywhere target x
    | .pathJ m r t p =>
      appearsAnywhere target m || appearsAnywhere target r ||
      appearsAnywhere target t || appearsAnywhere target p
    | .hcomp s b | .fill s b | .coe s b =>
      appearsAnywhere target s || appearsAnywhere target b
    | _ => false

/-- Check strict positivity of all HIT declarations in a theory.
    For each HITDecl, verify that the HIT's own name does not appear
    in a negative (left-of-arrow) position in any of its constructors. -/
def checkStrictPositivity (t : Theory) : List ValidationError :=
  t.hitDecls.flatMap fun hit =>
    hit.constructors.filterMap fun ctor =>
      if appearsNegative hit.name ctor.body then
        some (ValidationError.doctrineViolation
          s!"Strict positivity violation in HIT '{hit.name}': constructor '{ctor.name}' has '{hit.name}' in a negative position (left of →). This allows encoding paradoxes.")
      else none

-- ============================================================
-- Predicativity check for Π-types
--
-- In predicative MLTT, Π(x:A).B lives at max(level(A), level(B)).
-- If a theory uses Π(x : univ n). B where B : univ m with m ≤ n,
-- the Π-type must be at level n, not m. This prevents impredicative
-- encodings that collapse the universe hierarchy.
-- ============================================================

/-- Walk all expressions in a theory checking that Π-types don't
    violate predicativity. Reports violations where a Π-type with
    domain at level n is used as if it lived at level < n. -/
def checkPredicativity (t : Theory) : List ValidationError :=
  -- Only relevant for MLTT
  match t.doctrine.doctrine with
  | .MartinLofTypeTheory | .CubicalTypeTheory | .CohesiveHomotopyTypeTheory =>
    let objLevels : Std.HashMap Name Nat :=
      t.objects.foldl (fun acc o => acc.insert o.id.name 0) {}
    -- Check morphism types for predicativity violations
    t.morphisms.flatMap fun m =>
      checkExprPredicativity objLevels s!"morphism '{m.id.name}' domain" m.domain ++
      checkExprPredicativity objLevels s!"morphism '{m.id.name}' codomain" m.codomain
  | _ => []
where
  /-- Check a single expression for predicativity violations. -/
  checkExprPredicativity (objLevels : Std.HashMap Name Nat) (ctx : String) : Expr → List ValidationError
    | .pi _ base body =>
      -- Check if domain is a universe
      let violations := match base with
        | .univ n =>
          -- The Π-type Π(x : U_n). B must live at level ≥ n+1
          -- Check if body is claimed to be at a lower level
          match inferLevel objLevels body with
          | some bodyLevel =>
            if bodyLevel < n + 1 then
              [ValidationError.doctrineViolation
                s!"Predicativity violation in {ctx}: Π(x : univ {n}). B where B is at level {bodyLevel}, but Π-type must be at level ≥ {n + 1}"]
            else []
          | none => []
        | _ => []
      violations ++
        checkExprPredicativity objLevels ctx base ++
        checkExprPredicativity objLevels ctx body
    | .sigma _ base body =>
      checkExprPredicativity objLevels ctx base ++
      checkExprPredicativity objLevels ctx body
    | .prod a b | .coprod a b | .hom a b | .tensor a b =>
      checkExprPredicativity objLevels ctx a ++
      checkExprPredicativity objLevels ctx b
    | .path A x y =>
      checkExprPredicativity objLevels ctx A ++
      checkExprPredicativity objLevels ctx x ++
      checkExprPredicativity objLevels ctx y
    | .comp f g =>
      checkExprPredicativity objLevels ctx f ++
      checkExprPredicativity objLevels ctx g
    | .app f x =>
      checkExprPredicativity objLevels ctx f ++
      checkExprPredicativity objLevels ctx x
    | .lam _ d b =>
      checkExprPredicativity objLevels ctx d ++
      checkExprPredicativity objLevels ctx b
    | _ => []

/-- Run all validation checks on a theory -/
def validate (t : Theory) : List ValidationError :=
  checkDuplicates t ++
  checkMorphismReferences t ++
  checkAxiomReferences t ++
  checkDoctrine t ++
  checkCompositionBoundaries t ++
  checkUniverseConsistency t ++
  checkStrictPositivity t ++
  checkPredicativity t

/-- Is a theory well-formed? -/
def Theory.isValid (t : Theory) : Bool :=
  (validate t).isEmpty

/-- Pretty-print validation results -/
def validationReport (t : Theory) : String :=
  let errors := validate t
  if errors.isEmpty then s!"✓ Theory '{t.name}' is well-formed."
  else
    let errorLines := errors.map toString |> String.intercalate "\n  "
    s!"✗ Theory '{t.name}' has {errors.length} error(s):\n  {errorLines}"

-- ============================================================
-- Categorical Typechecker
-- ============================================================

/-- Infer the domain and codomain of a categorical expression.
    Takes a prebuilt morphism index for O(1) per-atom lookup.
    Returns `Except.ok (domain, codomain)` if well-formed, or an error string. -/
private partial def inferTypeIdx (t : Theory) (idx : Std.HashMap Name Generator1)
    (objIdx : Std.HashMap Name Generator0) (e : Expr) : Except String (Expr × Expr) :=
  match e with
  | .atom gid =>
    match idx[gid.name]? with
    | some m => Except.ok (m.domain, m.codomain)
    | none =>
      if objIdx[gid.name]? |>.isSome then Except.error s!"{gid.name} is an object, not a morphism"
      else Except.error s!"Unknown generator: {gid.name}"
  | .id obj => Except.ok (obj, obj)
  | .comp f g => do
    let (domF, codF) ← inferTypeIdx t idx objIdx f
    let (domG, codG) ← inferTypeIdx t idx objIdx g
    if !codF.alphaEquiv domG then
      Except.error s!"Composition boundary mismatch: cod({f.toName}) = {codF.toName} ≠ dom({g.toName}) = {domG.toName}"
    Except.ok (domF, codG)
  | .prod a b => do
    let (domA, codA) ← inferTypeIdx t idx objIdx a
    let (domB, codB) ← inferTypeIdx t idx objIdx b
    Except.ok (.prod domA domB, .prod codA codB)
  | .tensor f g => do
    let (domF, codF) ← inferTypeIdx t idx objIdx f
    let (domG, codG) ← inferTypeIdx t idx objIdx g
    Except.ok (.tensor domF domG, .tensor codF codG)
  | _ => Except.error s!"Type inference not implemented for {e.toName}"

/-- Public API: infer type of an expression in a theory. -/
partial def inferType (t : Theory) (e : Expr) : Except String (Expr × Expr) :=
  inferTypeIdx t t.morphismIndex t.objectIndex e

/-- Typecheck an entire theory: verify all axioms equate parallel morphisms
    (same domain and codomain on left and right paths).
    Builds morphism and object indices once, then reuses for all axioms. -/
def typecheckTheory (t : Theory) : List String :=
  let idx := t.morphismIndex
  let objIdx := t.objectIndex
  t.axioms.filterMap fun ax =>
    match inferTypeIdx t idx objIdx ax.leftPath, inferTypeIdx t idx objIdx ax.rightPath with
    | .ok (domL, codL), .ok (domR, codR) =>
      if !domL.alphaEquiv domR || !codL.alphaEquiv codR then
        some s!"Axiom '{ax.id.name}' is ill-typed: LHS ({domL.toName} → {codL.toName}) vs RHS ({domR.toName} → {codR.toName})"
      else none
    | .error e, _ => some s!"Axiom '{ax.id.name}' LHS: {e}"
    | _, .error e => some s!"Axiom '{ax.id.name}' RHS: {e}"

-- ============================================================
-- Doctrine Inference
-- ============================================================

/-- Collect doctrine constraints from a single Expr node (non-recursive).
    Returns the minimum doctrine required by this node's constructor. -/
private def exprConstraint : Expr → Doctrine
  | .prod ..      => .CartesianCategory
  | .terminal     => .CartesianCategory
  | .coprod ..    => .FinitelyCocomplete
  | .initial      => .FinitelyCocomplete
  | .tensor ..    => .MonoidalCategory
  | .hom ..       => .CartesianClosed       -- internal hom
  | .sigma ..     => .MartinLofTypeTheory   -- Σ-types
  | .pi ..        => .MartinLofTypeTheory   -- Π-types
  | .fiber ..     => .FinitelyComplete      -- pullback/fiber
  | .limit ..     => .FinitelyComplete
  | .colimit ..   => .FinitelyCocomplete
  | .natComponent .. => .Category           -- just functorial, no extra structure
  | .path ..      => .MartinLofTypeTheory  -- identity/path type
  | .refl ..      => .MartinLofTypeTheory  -- reflexivity
  | .pathJ ..     => .MartinLofTypeTheory  -- J-eliminator (path induction)
  | .hcomp ..     => .CubicalTypeTheory   -- Kan filler (cubical composition)
  | .fill ..      => .CubicalTypeTheory   -- box interior (cubical fill)
  | .coe ..       => .CubicalTypeTheory   -- transport/coercion along path
  | .lam ..       => .MartinLofTypeTheory  -- λ-abstraction
  | .univ ..      => .MartinLofTypeTheory  -- universe levels
  | _             => .Category              -- atoms, id, comp, unit, var, bvar, fvar, app, proj, inj

/-- Walk an Expr tree, collecting the join of all doctrine constraints. -/
private partial def exprDoctrineWalk (e : Expr) : Doctrine :=
  let here := exprConstraint e
  match e with
  | .comp f g         => Doctrine.join here (Doctrine.join (exprDoctrineWalk f) (exprDoctrineWalk g))
  | .prod a b         => Doctrine.join here (Doctrine.join (exprDoctrineWalk a) (exprDoctrineWalk b))
  | .coprod a b       => Doctrine.join here (Doctrine.join (exprDoctrineWalk a) (exprDoctrineWalk b))
  | .tensor a b       => Doctrine.join here (Doctrine.join (exprDoctrineWalk a) (exprDoctrineWalk b))
  | .hom a b          => Doctrine.join here (Doctrine.join (exprDoctrineWalk a) (exprDoctrineWalk b))
  | .id obj           => Doctrine.join here (exprDoctrineWalk obj)
  | .sigma _ b f      => Doctrine.join here (Doctrine.join (exprDoctrineWalk b) (exprDoctrineWalk f))
  | .pi _ b f         => Doctrine.join here (Doctrine.join (exprDoctrineWalk b) (exprDoctrineWalk f))
  | .fiber m p        => Doctrine.join here (Doctrine.join (exprDoctrineWalk m) (exprDoctrineWalk p))
  | .proj _ s         => Doctrine.join here (exprDoctrineWalk s)
  | .inj _ s          => Doctrine.join here (exprDoctrineWalk s)
  | .app f x          => Doctrine.join here (Doctrine.join (exprDoctrineWalk f) (exprDoctrineWalk x))
  | .limit d          => Doctrine.join here (exprDoctrineWalk d)
  | .colimit d        => Doctrine.join here (exprDoctrineWalk d)
  | .natComponent n x => Doctrine.join here (Doctrine.join (exprDoctrineWalk n) (exprDoctrineWalk x))
  | .path A x y       => Doctrine.join here (Doctrine.join (exprDoctrineWalk A) (Doctrine.join (exprDoctrineWalk x) (exprDoctrineWalk y)))
  | .refl x           => Doctrine.join here (exprDoctrineWalk x)
  | .pathJ m r t p    => Doctrine.join here (Doctrine.join (exprDoctrineWalk m) (Doctrine.join (exprDoctrineWalk r) (Doctrine.join (exprDoctrineWalk t) (exprDoctrineWalk p))))
  | .hcomp sys base   => Doctrine.join here (Doctrine.join (exprDoctrineWalk sys) (exprDoctrineWalk base))
  | .fill sys base    => Doctrine.join here (Doctrine.join (exprDoctrineWalk sys) (exprDoctrineWalk base))
  | .coe p a          => Doctrine.join here (Doctrine.join (exprDoctrineWalk p) (exprDoctrineWalk a))
  | .lam _ d b        => Doctrine.join here (Doctrine.join (exprDoctrineWalk d) (exprDoctrineWalk b))
  | _                 => here

/-- Infer the minimum doctrine required to host a theory, based on the Expr
    constructors used in its morphism signatures and axiom paths.

    This is a bottom-up constraint-collection pass: every Expr node contributes
    a minimum doctrine (e.g., `prod` → CartesianCategory, `tensor` → Monoidal),
    and the join across all nodes gives the inferred doctrine.

    Named generators (e.g., an object called "Ω") also contribute:
    an object named Ω implies a subobject classifier → Topos doctrine. -/
def inferDoctrine (t : Theory) : Doctrine :=
  let base := Doctrine.Category
  -- Collect from morphism domains/codomains
  let fromMorphisms := t.morphisms.foldl (fun acc m =>
    Doctrine.join acc (Doctrine.join (exprDoctrineWalk m.domain) (exprDoctrineWalk m.codomain))
  ) base
  -- Collect from axiom paths
  let fromAxioms := t.axioms.foldl (fun acc ax =>
    Doctrine.join acc (Doctrine.join (exprDoctrineWalk ax.leftPath) (exprDoctrineWalk ax.rightPath))
  ) fromMorphisms
  -- Named generator heuristics
  let hasOmega := t.objects.any fun o =>
    o.id.name == Name.root "Ω" || o.id.name == Name.root "Omega"
  let withOmega := if hasOmega then Doctrine.join fromAxioms .ElementaryTopos else fromAxioms
  withOmega

/-- Result of doctrine inference: whether the stated doctrine matches, needs
    upgrading, or is higher than what the theory actually uses. -/
inductive DoctrineInferenceResult where
  | matches         : DoctrineInferenceResult
  | upgraded (stated inferred : Doctrine) : DoctrineInferenceResult
  | overstated (stated inferred : Doctrine) : DoctrineInferenceResult
  deriving Repr

instance : ToString DoctrineInferenceResult where
  toString
    | .matches => "Doctrine matches"
    | .upgraded s i => s!"Doctrine upgraded: {repr s} → {repr i}"
    | .overstated s i => s!"Doctrine overstated: stated {repr s}, only needs {repr i}"

/-- Check a theory's stated doctrine against its inferred doctrine.
    If the inferred doctrine is richer, returns `upgraded` with the correct doctrine. -/
def checkDoctrineInference (t : Theory) : DoctrineInferenceResult :=
  let inferred := inferDoctrine t
  let stated := t.doctrine.doctrine
  if stated == inferred then .matches
  else if inferred.rank > stated.rank then .upgraded stated inferred
  else .overstated stated inferred

/-- Auto-upgrade a theory's doctrine to the minimum required by its content.
    Returns the theory unchanged if the stated doctrine is already sufficient. -/
def Theory.autoUpgradeDoctrine (t : Theory) : Theory :=
  let inferred := inferDoctrine t
  if inferred.rank > t.doctrine.doctrine.rank then
    { t with doctrine := { t.doctrine with doctrine := inferred } }
  else t

end CatLab
