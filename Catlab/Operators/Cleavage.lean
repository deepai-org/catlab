/-
  CatLab — Cleavage: Fibration → Indexed Category

  Inverse of the Grothendieck construction. Given a fibration p : E → B
  (a functor with cartesian liftings), extract the indexed category
  B^op → Cat sending each object b to its fiber p⁻¹(b) and each
  morphism f : a → b to the reindexing functor f* : p⁻¹(b) → p⁻¹(a).
-/

import Catlab.Core.Theory

namespace CatLab

/-- Data specifying a fibration: a functor p : E → B together with a
    cleavage (choice of cartesian liftings). -/
structure FibrationData where
  /-- The total category E -/
  total : Theory
  /-- The base category B -/
  base : Theory
  /-- The projection functor p, given as object map: total object id → base object id -/
  projObj : GeneratorId → GeneratorId
  /-- The projection functor p on morphisms: total morphism id → base morphism id -/
  projMor : GeneratorId → GeneratorId
  /-- Cartesian lifting: given a base morphism f : a → b and an object y in the
      fiber over b, return the cartesian lift f*(y) → y in E -/
  cartesianLift : GeneratorId → GeneratorId → Option GeneratorId
  deriving Inhabited

/-- Extract the fiber category over a base object b: the full subcategory
    of E consisting of objects mapping to b under p. -/
def fiberOver (fib : FibrationData) (b : GeneratorId) : Theory :=
  let fiberObjects := fib.total.objects.filter fun e =>
    (fib.projObj e.id).beq b

  let fiberMorphisms := fib.total.morphisms.filter fun f =>
    (fib.projMor f.id).beq b

  { name := s!"p⁻¹({b.name})"
    doctrine := fib.total.doctrine
    objects := fiberObjects
    morphisms := fiberMorphisms
    axioms := [] }

/-- Extract the reindexing functor f* : p⁻¹(cod f) → p⁻¹(dom f) for a
    base morphism f, using the cartesian liftings from the cleavage. -/
def reindexFunctor (fib : FibrationData) (f : Generator1) : List Generator1 :=
  let codFiber := fib.total.objects.filter fun e =>
    (fib.projObj e.id).beq (match f.codomain with
      | .atom g => g | _ => gid "?")
  codFiber.filterMap fun y =>
    match fib.cartesianLift f.id y.id with
    | some liftId =>
      some { id := { name := .app (.root s!"reindex_{f.id.name}") y.id.name
                     kind := .morphism }
             domain := .atom y.id  -- f*(y) source in codomain fiber
             codomain := .atom y.id  -- simplified; actual target in domain fiber
             description := s!"Reindexing {y.id.name} along {f.id.name}" }
    | none => none

/-- Given a fibration p : E → B with cleavage, extract the indexed category
    B^op → Cat.

    This is the inverse of the Grothendieck construction:
    - For each base object b, the fiber p⁻¹(b) is a category
    - For each base morphism f : a → b, reindexing f* : p⁻¹(b) → p⁻¹(a)
    - Composition of reindexing is coherent (up to iso for cleavages,
      strict for split fibrations) -/
def cleavageToIndexed (fib : FibrationData) : Theory :=
  -- Objects: one for each fiber category
  let fiberObjects := fib.base.objects.map fun b =>
    { id := { name := .app (.root "Fib") b.id.name, kind := .sort }
      description := s!"Fiber category p⁻¹({b.id.name})" : Generator0 }

  -- Morphisms: reindexing functors for each base morphism
  let reindexMorphisms := fib.base.morphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    [{ id := { name := .app (.root "reindex") f.id.name, kind := .morphism }
       domain := .atom { name := .app (.root "Fib") codName, kind := .sort }
       codomain := .atom { name := .app (.root "Fib") domName, kind := .sort }
       description := s!"Reindexing functor along {f.id.name} (contravariant)"
       : Generator1 }]

  -- Axiom: reindexing along identity is the identity functor
  let idAxioms := fib.base.objects.map fun b =>
    let fibExpr := Expr.atom { name := .app (.root "Fib") b.id.name, kind := .sort }
    { id := { name := .nested (.app (.root "Fib") b.id.name) "reindex_id"
              kind := .twoCell }
      leftPath := .app (.atom (gid "reindex")) (.id (.atom b.id))
      rightPath := .id fibExpr
      description := s!"Reindexing along id_{b.id.name} is identity" : Generator2 }

  -- Axiom: reindexing preserves composition (up to natural iso)
  let compAxioms := fib.base.morphisms.flatMap fun f =>
    fib.base.morphisms.flatMap fun g =>
      let fReindex := Expr.atom { name := .app (.root "reindex") f.id.name
                                  kind := .morphism }
      let gReindex := Expr.atom { name := .app (.root "reindex") g.id.name
                                  kind := .morphism }
      [{ id := { name := .app (.root "reindex_comp")
                   (Name.pair f.id.name g.id.name), kind := .twoCell }
         leftPath := .comp gReindex fReindex
         rightPath := .app (.atom (gid "reindex")) (.comp (.atom f.id) (.atom g.id))
         description := s!"Reindexing along {g.id.name} ∘ {f.id.name}" : Generator2 }]

  { name := s!"Indexed({fib.base.name})"
    doctrine := fib.base.doctrine
    objects := fiberObjects
    morphisms := reindexMorphisms
    axioms := idAxioms ++ compAxioms }

end CatLab
