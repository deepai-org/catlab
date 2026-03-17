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
  | duplicateName (name : Name)
  | undeclaredObject (referencedIn : String) (name : Name)
  | undeclaredMorphism (referencedIn : String) (name : Name)
  | doctrineViolation (message : String)
  deriving Repr, Inhabited

instance : ToString ValidationError where
  toString
    | .duplicateName n => s!"Duplicate generator name: {n}"
    | .undeclaredObject ctx n => s!"Undeclared object '{n}' referenced in {ctx}"
    | .undeclaredMorphism ctx n => s!"Undeclared morphism '{n}' referenced in {ctx}"
    | .doctrineViolation msg => s!"Doctrine violation: {msg}"

/-- Collect all atom GeneratorIds referenced in an expression (preserving kind info) -/
def Expr.atomIds : Expr → List GeneratorId
  | .atom gid => [gid]
  | Expr.id obj => obj.atomIds
  | .comp f g => f.atomIds ++ g.atomIds
  | .prod a b => a.atomIds ++ b.atomIds
  | .coprod a b => a.atomIds ++ b.atomIds
  | .hom a b => a.atomIds ++ b.atomIds
  | .tensor a b => a.atomIds ++ b.atomIds
  | .sigma _ base fam => base.atomIds ++ fam.atomIds
  | .pi _ base fam => base.atomIds ++ fam.atomIds
  | .fiber m p => m.atomIds ++ p.atomIds
  | .proj _ s => s.atomIds
  | .inj _ t => t.atomIds
  | .app f x => f.atomIds ++ x.atomIds
  | .limit d => d.atomIds
  | .colimit d => d.atomIds
  | .natComponent n x => n.atomIds ++ x.atomIds
  | .unit | .terminal | .initial | .var _ => []

/-- Collect all atom names referenced in an expression (convenience wrapper) -/
def Expr.atoms (e : Expr) : List Name :=
  e.atomIds.map (·.name)

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
