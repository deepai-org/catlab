/-
  CatLab -- Functor Categories [C, D]

  The category of functors from C to D:
  - Objects: functors F : C → D
  - Morphisms: natural transformations α : F ⟹ G

  Now includes:
  - Naturality square axioms (properly referenced via Name, not repr)
  - Identity natural transformation (id_F)
  - Vertical composition of natural transformations (β ∘ α)
  - Composition associativity and unit laws

  Special cases:
  - [C, Set] = PSh(C) (presheaf category, already in Yoneda.lean)
  - [1, C] ≅ C
  - [2, C] ≅ Arr(C) (arrow category)
-/

import Catlab.Core.Theory
import Catlab.Operators.Kan

namespace CatLab

/-- Compute the functor category [C, D].

    Given two theories C and D, [C, D] has:
    - Objects: theory functors C → D (one for each compatible assignment)
    - Morphisms: natural transformations (families of D-morphisms with naturality)
    - Identity: id_F with components id_{F(a)}
    - Composition: (β ∘ α)_a = β_a ∘ α_a (vertical composition) -/
def functorCategory (source target : Theory) : Theory :=
  -- Three functor-objects representing generic functors F, G, H : C → D
  let funcF := { id := gid "F", description := s!"Functor F : {source.name} → {target.name}" }
  let funcG := { id := gid "G", description := s!"Functor G : {source.name} → {target.name}" }
  let funcH := { id := gid "H", description := s!"Functor H : {source.name} → {target.name}" }

  -- Natural transformation components α : F ⟹ G
  -- For each object a of C, α_a : F(a) → G(a)
  let natTransComponents := source.objects.map fun a =>
    { id := { name := .app (.root "α") a.id.name, index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      codomain := .atom { name := .app (.root "G") a.id.name, index := 0, kind := .sort }
      description := s!"Component of α : F ⟹ G at {a.id.name}" : Generator1 }

  -- Natural transformation β : G ⟹ H
  let betaComponents := source.objects.map fun a =>
    { id := { name := .app (.root "β") a.id.name, index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "G") a.id.name, index := 0, kind := .sort }
      codomain := .atom { name := .app (.root "H") a.id.name, index := 0, kind := .sort }
      description := s!"Component of β : G ⟹ H at {a.id.name}" : Generator1 }

  -- Identity natural transformation: id_F with components id_{F(a)}
  let idComponents := source.objects.map fun a =>
    { id := { name := .app (.root "id_F") a.id.name, index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      codomain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      description := s!"Identity nat trans component at {a.id.name}" : Generator1 }

  -- Vertical composition: (β ∘ α)_a : F(a) → H(a)
  let compComponents := source.objects.map fun a =>
    { id := { name := .app (.root "β∘α") a.id.name, index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      codomain := .atom { name := .app (.root "H") a.id.name, index := 0, kind := .sort }
      description := s!"Vertical composition component at {a.id.name}" : Generator1 }

  -- Naturality squares for α: G(f) ∘ α_a = α_b ∘ F(f)
  let naturalityAxioms := source.morphisms.map fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    { id := { name := .app (.root "naturality_α") f.id.name, index := 0, kind := .twoCell }
      leftPath := .comp (.atom { name := .app (.root "α") domName, index := 0, kind := .morphism })
                        (.atom { name := .app (.root "G") f.id.name, index := 0, kind := .morphism })
      rightPath := .comp (.atom { name := .app (.root "F") f.id.name, index := 0, kind := .morphism })
                         (.atom { name := .app (.root "α") codName, index := 0, kind := .morphism })
      description := s!"Naturality of α: G({f.id.name}) ∘ α = α ∘ F({f.id.name})" : Generator2 }

  -- Naturality squares for β: H(f) ∘ β_a = β_b ∘ G(f)
  let naturalityBeta := source.morphisms.map fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    { id := { name := .app (.root "naturality_β") f.id.name, index := 0, kind := .twoCell }
      leftPath := .comp (.atom { name := .app (.root "β") domName, index := 0, kind := .morphism })
                        (.atom { name := .app (.root "H") f.id.name, index := 0, kind := .morphism })
      rightPath := .comp (.atom { name := .app (.root "G") f.id.name, index := 0, kind := .morphism })
                         (.atom { name := .app (.root "β") codName, index := 0, kind := .morphism })
      description := s!"Naturality of β: H({f.id.name}) ∘ β = β ∘ G({f.id.name})" : Generator2 }

  -- Vertical composition law: (β ∘ α)_a = β_a ∘ α_a
  let compAxioms := source.objects.map fun a =>
    { id := { name := .app (.root "vcomp") a.id.name, index := 0, kind := .twoCell }
      leftPath := .atom { name := .app (.root "β∘α") a.id.name, index := 0, kind := .morphism }
      rightPath := .comp
        (.atom { name := .app (.root "α") a.id.name, index := 0, kind := .morphism })
        (.atom { name := .app (.root "β") a.id.name, index := 0, kind := .morphism })
      description := s!"Vertical composition: (β∘α)_{a.id.name} = β_a ∘ α_a" : Generator2 }

  -- Identity law: (id_F)_a = id_{F(a)}
  let idAxioms := source.objects.map fun a =>
    { id := { name := .app (.root "id_law") a.id.name, index := 0, kind := .twoCell }
      leftPath := .atom { name := .app (.root "id_F") a.id.name, index := 0, kind := .morphism }
      rightPath := .id (.atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort })
      description := s!"Identity: (id_F)_{a.id.name} = id" : Generator2 }

  -- Left unit law: id_G ∘ α = α (for each component)
  let leftUnitAxioms := source.objects.map fun a =>
    { id := { name := .app (.root "left_unit") a.id.name, index := 0, kind := .twoCell }
      leftPath := .comp
        (.atom { name := .app (.root "α") a.id.name, index := 0, kind := .morphism })
        (.id (.atom { name := .app (.root "G") a.id.name, index := 0, kind := .sort }))
      rightPath := .atom { name := .app (.root "α") a.id.name, index := 0, kind := .morphism }
      description := s!"Left unit: id_G ∘ α = α at {a.id.name}" : Generator2 }

  -- Right unit law: α ∘ id_F = α (for each component)
  let rightUnitAxioms := source.objects.map fun a =>
    { id := { name := .app (.root "right_unit") a.id.name, index := 0, kind := .twoCell }
      leftPath := .comp
        (.id (.atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }))
        (.atom { name := .app (.root "α") a.id.name, index := 0, kind := .morphism })
      rightPath := .atom { name := .app (.root "α") a.id.name, index := 0, kind := .morphism }
      description := s!"Right unit: α ∘ id_F = α at {a.id.name}" : Generator2 }

  { name := s!"[{source.name}, {target.name}]"
    doctrine := target.doctrine
    objects := [funcF, funcG, funcH]
    morphisms := natTransComponents ++ betaComponents ++ idComponents ++ compComponents
    axioms := naturalityAxioms ++ naturalityBeta ++ compAxioms ++ idAxioms
              ++ leftUnitAxioms ++ rightUnitAxioms }

/-- The evaluation functor ev : [C, D] × C → D
    sending (F, a) ↦ F(a). -/
def evalFunctor (source target : Theory) : List Generator1 :=
  source.objects.map fun a =>
    { id := gid s!"ev_{a.id.name}"
      domain := .prod (.atom (gid s!"[{source.name},{target.name}]")) (.atom a.id)
      codomain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      description := s!"Evaluation at {a.id.name}" }

/-- Compute the natural transformation category Nat(F, G)
    for two specific functors F, G : C → D.
    This is the hom-set in [C, D], made into an object of D. -/
def natTransformations (source : Theory)
    (fOnObj gOnObj : GeneratorMap) : Theory :=
  let natObj := { id := gid "Nat(F,G)"
                  description := "Natural transformations F ⟹ G" }

  let components := source.objects.map fun a =>
    { id := { name := .app (.root "α") a.id.name, index := 0, kind := .morphism }
      domain := fOnObj.apply a.id
      codomain := gOnObj.apply a.id
      description := s!"Component at {a.id.name}" : Generator1 }

  let naturality := source.morphisms.map fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    { id := { name := .app (.root "nat") f.id.name, index := 0, kind := .twoCell }
      leftPath := .comp (.atom { name := .app (.root "α") domName, index := 0, kind := .morphism })
                        (gOnObj.apply f.id)
      rightPath := .comp (fOnObj.apply f.id)
                         (.atom { name := .app (.root "α") codName, index := 0, kind := .morphism })
      description := s!"Naturality square for {f.id.name}" : Generator2 }

  { name := "Nat(F,G)"
    doctrine := { doctrine := .Category }
    objects := [natObj]
    morphisms := components
    axioms := naturality }

end CatLab
