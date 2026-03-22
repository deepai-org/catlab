/-
  CatLab — Dependent Theories (TheoryFamily)

  A TheoryFamily is a fibered structure over a base theory:
  for each "model" of the base, there is a fiber theory.

  Example: Module is a TheoryFamily over Ring.
    For any ring R (with its concrete mul, add, etc.),
    the fiber is the theory of R-modules.

  This avoids hardcoding hundreds of theory variants by
  parameterizing theories over their dependencies.

  A "Model" here is syntactic: it's a GeneratorMap that assigns
  concrete names to each generator of the base theory. The fiber
  function uses these names to build the fiber theory with the
  base operations substituted in.

  Key operations:
    - TheoryFamily.fiber: get the fiber theory for a given model
    - TheoryFamily.flatten: substitute a model into the fiber,
      producing a standalone Theory (the Grothendieck flattening)
    - TheoryFamily.totalTheory: merge base + fiber into one theory
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

-- ============================================================
-- Syntactic Models
-- ============================================================

/-- A syntactic model of a theory: an assignment of concrete Exprs
    to each generator. This is the "point" of the base in the
    fibration — it tells the fiber which concrete operations to use.

    For example, a model of Ring might map:
      R ↦ ℤ, add ↦ int_add, mul ↦ int_mul, zero ↦ int_zero, one ↦ int_one -/
structure SyntacticModel where
  /-- The theory being modeled -/
  theory : Theory
  /-- Maps object generators to concrete Exprs -/
  onObjects : GeneratorMap
  /-- Maps morphism generators to concrete Exprs -/
  onMorphisms : GeneratorMap
  deriving Inhabited

namespace SyntacticModel

/-- Create a model from a list of (name, expr) pairs.
    Automatically classifies into object vs morphism mappings
    using the theory's generator index. -/
def ofList (t : Theory) (pairs : List (String × Expr)) : SyntacticModel :=
  let objNames := t.objects.map (·.id.name)
  let (objPairs, morPairs) := pairs.partition fun (n, _) =>
    objNames.any (· == .root n)
  { theory := t
    onObjects := GeneratorMap.ofList (objPairs.map fun (n, e) => (gid n, e))
    onMorphisms := GeneratorMap.ofList (morPairs.map fun (n, e) => (gid n 0 .morphism, e)) }

/-- Apply this model's substitutions to an Expr: replace atoms
    that reference base generators with their concrete assignments. -/
def applyToExpr (m : SyntacticModel) (e : Expr) : Expr :=
  e.mapAtoms fun atom =>
    match atom with
    | .atom gid =>
      match m.onObjects.find? gid with
      | some v => v
      | none =>
        match m.onMorphisms.find? gid with
        | some v => v
        | none => atom
    | other => other

end SyntacticModel

-- ============================================================
-- Theory Families
-- ============================================================

/-- A dependent theory: a base theory plus a fiber constructor.

    The fiber takes a SyntacticModel of the base and returns
    a Theory parameterized by that model's concrete operations.

    Example:
      ModuleFamily.base = Ring
      ModuleFamily.fiberOf(model_of_ℤ) = Theory of ℤ-modules -/
structure TheoryFamily where
  /-- The base theory that the family is indexed over -/
  base : Theory
  /-- Given a syntactic model of the base, produce the fiber theory.
      The fiber may reference the model's generators in its
      domains/codomains/axioms. -/
  fiberOf : SyntacticModel → Theory
  /-- Human-readable name for the family -/
  name : String := ""

namespace TheoryFamily

/-- The "generic" fiber: instantiate the family with the identity model
    (base generators map to themselves). This gives the most general
    version of the fiber theory. -/
def genericFiber (fam : TheoryFamily) : Theory :=
  let idModel : SyntacticModel := {
    theory := fam.base
    onObjects := GeneratorMap.ofList (fam.base.objects.map fun o => (o.id, .atom o.id))
    onMorphisms := GeneratorMap.ofList (fam.base.morphisms.map fun m => (m.id, .atom m.id))
  }
  fam.fiberOf idModel

/-- Flatten: given a concrete model of the base, produce a standalone
    theory that merges the base (as instantiated) with the fiber.

    This is the Grothendieck construction at the theory level:
    the total theory contains both the base structure (via the model)
    and the fiber structure (parameterized by the model). -/
def flatten (fam : TheoryFamily) (model : SyntacticModel) : Theory :=
  let fiber := fam.fiberOf model
  -- The fiber already has the model's operations substituted in.
  -- We return the fiber directly — it's a complete standalone theory.
  fiber

/-- Total theory: merge the base theory's generators with the generic
    fiber's generators into a single theory. This is useful for
    getting the "full signature" of the family.

    Objects/morphisms/axioms from both base and fiber are combined,
    with the fiber referencing base generators by their original names. -/
def totalTheory (fam : TheoryFamily) : Theory :=
  let fiber := fam.genericFiber
  let baseObjs := fam.base.objects
  let baseMors := fam.base.morphisms
  let baseAxioms := fam.base.axioms
  -- Filter out fiber generators that duplicate base generators
  let baseObjNames := baseObjs.map (·.id.name)
  let baseMorNames := baseMors.map (·.id.name)
  let fiberObjs := fiber.objects.filter fun o =>
    !(baseObjNames.any (· == o.id.name))
  let fiberMors := fiber.morphisms.filter fun m =>
    !(baseMorNames.any (· == m.id.name))
  { name := if fam.name == "" then s!"{fam.base.name}-Family" else fam.name
    doctrine := fiber.doctrine
    objects := baseObjs ++ fiberObjs
    morphisms := baseMors ++ fiberMors
    axioms := baseAxioms ++ fiber.axioms }

/-- Instantiate the family at a named model, producing a flattened theory
    with a descriptive name. -/
def instantiate (fam : TheoryFamily) (modelName : String) (model : SyntacticModel) : Theory :=
  let result := fam.flatten model
  { result with name := s!"{fam.name}({modelName})" }

end TheoryFamily

-- ============================================================
-- Constructing Families from Existing Theories
-- ============================================================

/-- Check if an Expr references only names from a given set
    (i.e., it operates purely on base-theory objects). -/
private def exprUsesOnly (e : Expr) (names : List Name) : Bool :=
  e.atoms.all fun n => names.any (· == n)

def extractFamily (base : Theory) (total : Theory) (familyName : String := "") : TheoryFamily :=
  let baseObjNames := base.objects.map (·.id.name)
  { base := base
    name := if familyName == "" then s!"{total.name}/{base.name}" else familyName
    fiberOf := fun model =>
      -- Objects: keep non-base objects
      let fiberObjs := total.objects.filter fun o =>
        !(baseObjNames.any (· == o.id.name))
      -- Morphisms: keep morphisms that touch at least one non-base object.
      -- A morphism operating purely on base objects belongs to the base,
      -- even if it shares a name with a fiber morphism.
      let fiberMors := total.morphisms.filter fun m =>
        !(exprUsesOnly m.domain baseObjNames && exprUsesOnly m.codomain baseObjNames)
      let fiberMors := fiberMors.map fun m =>
        { m with
          domain := model.applyToExpr m.domain
          codomain := model.applyToExpr m.codomain }
      -- Axioms: keep axioms that reference at least one fiber morphism
      let fiberMorNames := fiberMors.map (·.id.name)
      let fiberAxioms := total.axioms.filter fun a =>
        let allAtoms := a.leftPath.atoms ++ a.rightPath.atoms
        allAtoms.any fun n => fiberMorNames.any (· == n)
      let fiberAxioms := fiberAxioms.map fun a =>
        { a with
          leftPath := model.applyToExpr a.leftPath
          rightPath := model.applyToExpr a.rightPath }
      { name := s!"{total.name}[{model.theory.name}]"
        doctrine := total.doctrine
        objects := fiberObjs
        morphisms := fiberMors
        axioms := fiberAxioms }
  }

end CatLab
