/-
  CatLab -- Well-formedness Validation

  Checks that a theory is internally consistent:
  - All morphism domains/codomains reference declared objects
  - All axiom paths reference declared morphisms
  - No duplicate generator names
  - Doctrine constraints are satisfied
-/

import Catlab.Core.Theory

namespace CatLab

/-- A validation error -/
inductive ValidationError where
  | duplicateName (name : String)
  | undeclaredObject (referencedIn : String) (name : String)
  | undeclaredMorphism (referencedIn : String) (name : String)
  | doctrineViolation (message : String)
  deriving Repr, Inhabited

instance : ToString ValidationError where
  toString
    | .duplicateName n => s!"Duplicate generator name: {n}"
    | .undeclaredObject ctx n => s!"Undeclared object '{n}' referenced in {ctx}"
    | .undeclaredMorphism ctx n => s!"Undeclared morphism '{n}' referenced in {ctx}"
    | .doctrineViolation msg => s!"Doctrine violation: {msg}"

/-- Collect all atom names referenced in an expression -/
def Expr.atoms : Expr → List String
  | .atom gid => [gid.name]
  | Expr.id obj => obj.atoms
  | .comp f g => f.atoms ++ g.atoms
  | .prod a b => a.atoms ++ b.atoms
  | .coprod a b => a.atoms ++ b.atoms
  | .hom a b => a.atoms ++ b.atoms
  | .tensor a b => a.atoms ++ b.atoms
  | .sigma _ base fam => base.atoms ++ fam.atoms
  | .pi _ base fam => base.atoms ++ fam.atoms
  | .fiber m p => m.atoms ++ p.atoms
  | .proj _ s => s.atoms
  | .inj _ t => t.atoms
  | .unit | .terminal | .initial | .var _ => []

/-- Check for duplicate names across all generators -/
def checkDuplicates (t : Theory) : List ValidationError :=
  let names := t.allNames
  let rec findDups : List String → List String → List ValidationError
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
    let hasOmega := t.objects.any fun o => o.id.name == "Ω"
    if !hasOmega then [.doctrineViolation "Topos should have subobject classifier Ω"]
    else []
  | _ => []

/-- Run all validation checks on a theory -/
def validate (t : Theory) : List ValidationError :=
  checkDuplicates t ++
  checkMorphismReferences t ++
  checkAxiomReferences t ++
  checkDoctrine t

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

end CatLab
