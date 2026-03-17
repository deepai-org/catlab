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

/-- Check for duplicate names across all generators -/
def checkDuplicates (t : Theory) : List ValidationError :=
  let names := t.allNames
  let rec findDups : List Name → List Name → List ValidationError
    | [], _ => []
    | n :: ns, seen =>
      if seen.contains n then .duplicateName n :: findDups ns seen
      else findDups ns (n :: seen)
  findDups names []

/-- Check that morphism domain/codomain atoms reference declared objects or morphisms -/
def checkMorphismReferences (t : Theory) : List ValidationError :=
  let knownNames := t.allNames
  t.morphisms.flatMap fun m =>
    let domAtoms := m.domain.atoms
    let codAtoms := m.codomain.atoms
    let domErrors := domAtoms.filterMap fun a =>
      if knownNames.contains a then none
      else some (ValidationError.undeclaredObject s!"morphism '{m.id.name}' domain" a)
    let codErrors := codAtoms.filterMap fun a =>
      if knownNames.contains a then none
      else some (ValidationError.undeclaredObject s!"morphism '{m.id.name}' codomain" a)
    domErrors ++ codErrors

/-- Check that axiom paths reference declared generators -/
def checkAxiomReferences (t : Theory) : List ValidationError :=
  let knownNames := t.allNames
  t.axioms.flatMap fun ax =>
    let leftAtoms := ax.leftPath.atoms
    let rightAtoms := ax.rightPath.atoms
    let allAtoms := leftAtoms ++ rightAtoms
    allAtoms.filterMap fun a =>
      if knownNames.contains a then none
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

/-- Infer the codomain of an expression, given the theory's morphism table.
    For atoms, looks up the morphism's codomain. For compositions, returns
    the codomain of the second factor. Returns none for non-morphism exprs. -/
private partial def inferCodomain (t : Theory) (e : Expr) : Option Expr :=
  match e with
  | .atom gid => (t.findMorphism gid.name).map (·.codomain)
  | .comp _ g => inferCodomain t g
  | .id obj => some obj
  | _ => none

/-- Infer the domain of an expression. -/
private partial def inferDomain (t : Theory) (e : Expr) : Option Expr :=
  match e with
  | .atom gid => (t.findMorphism gid.name).map (·.domain)
  | .comp f _ => inferDomain t f
  | .id obj => some obj
  | _ => none

/-- Check that all Expr.comp nodes have matching boundaries:
    in `comp f g`, the codomain of f must match the domain of g. -/
private partial def checkCompBoundaries (t : Theory) (context : String) (e : Expr) : List ValidationError :=
  match e with
  | .comp f g =>
    let innerErrors := checkCompBoundaries t context f ++ checkCompBoundaries t context g
    let boundaryError := match inferCodomain t f, inferDomain t g with
      | some cod, some dom =>
        if cod.beq dom then []
        else [ValidationError.boundaryMismatch context s!"{cod.toName}" s!"{dom.toName}"]
      | _, _ => []  -- can't infer; skip
    innerErrors ++ boundaryError
  | .prod a b | .coprod a b | .hom a b | .tensor a b =>
    checkCompBoundaries t context a ++ checkCompBoundaries t context b
  | .id obj => checkCompBoundaries t context obj
  | .sigma _ base fam | .pi _ base fam =>
    checkCompBoundaries t context base ++ checkCompBoundaries t context fam
  | .fiber m p => checkCompBoundaries t context m ++ checkCompBoundaries t context p
  | .proj _ s => checkCompBoundaries t context s
  | .inj _ s => checkCompBoundaries t context s
  | .app f x => checkCompBoundaries t context f ++ checkCompBoundaries t context x
  | .limit d | .colimit d => checkCompBoundaries t context d
  | .natComponent n x => checkCompBoundaries t context n ++ checkCompBoundaries t context x
  | _ => []

/-- Check composition boundaries across all axioms in a theory -/
def checkCompositionBoundaries (t : Theory) : List ValidationError :=
  t.axioms.flatMap fun ax =>
    checkCompBoundaries t s!"axiom '{ax.id.name}' LHS" ax.leftPath ++
    checkCompBoundaries t s!"axiom '{ax.id.name}' RHS" ax.rightPath

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
    Returns `Except.ok (domain, codomain)` if well-formed, or an error string. -/
partial def inferType (t : Theory) (e : Expr) : Except String (Expr × Expr) :=
  match e with
  | .atom gid =>
    match t.findMorphism gid.name with
    | some m => Except.ok (m.domain, m.codomain)
    | none =>
      if t.isObjectName gid.name then Except.error s!"{gid.name} is an object, not a morphism"
      else Except.error s!"Unknown generator: {gid.name}"
  | .id obj => Except.ok (obj, obj)
  | .comp f g => do
    let (domF, codF) ← inferType t f
    let (domG, codG) ← inferType t g
    if !codF.alphaEquiv domG then
      Except.error s!"Composition boundary mismatch: cod({f.toName}) = {codF.toName} ≠ dom({g.toName}) = {domG.toName}"
    Except.ok (domF, codG)
  | .prod a b => do
    let (domA, codA) ← inferType t a
    let (domB, codB) ← inferType t b
    Except.ok (.prod domA domB, .prod codA codB)
  | .tensor f g => do
    let (domF, codF) ← inferType t f
    let (domG, codG) ← inferType t g
    Except.ok (.tensor domF domG, .tensor codF codG)
  | _ => Except.error s!"Type inference not implemented for {e.toName}"

/-- Typecheck an entire theory: verify all axioms equate parallel morphisms
    (same domain and codomain on left and right paths). -/
def typecheckTheory (t : Theory) : List String :=
  t.axioms.filterMap fun ax =>
    match inferType t ax.leftPath, inferType t ax.rightPath with
    | .ok (domL, codL), .ok (domR, codR) =>
      if !domL.alphaEquiv domR || !codL.alphaEquiv codR then
        some s!"Axiom '{ax.id.name}' is ill-typed: LHS ({domL.toName} → {codL.toName}) vs RHS ({domR.toName} → {codR.toName})"
      else none
    | .error e, _ => some s!"Axiom '{ax.id.name}' LHS: {e}"
    | _, .error e => some s!"Axiom '{ax.id.name}' RHS: {e}"

end CatLab
