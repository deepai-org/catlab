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
  | _ => []

/-- Check composition boundaries across all axioms in a theory -/
def checkCompositionBoundaries (t : Theory) : List ValidationError :=
  -- Build morphism index once; reused for every axiom boundary check
  let idx := t.morphismIndex
  t.axioms.flatMap fun ax =>
    checkCompBoundaries idx s!"axiom '{ax.id.name}' LHS" ax.leftPath ++
    checkCompBoundaries idx s!"axiom '{ax.id.name}' RHS" ax.rightPath

/-- Run all validation checks on a theory -/
def validate (t : Theory) : List ValidationError :=
  checkDuplicates t ++
  checkMorphismReferences t ++
  checkAxiomReferences t ++
  checkDoctrine t ++
  checkCompositionBoundaries t

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

end CatLab
