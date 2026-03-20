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
  -- The functor category object
  let funcObj := { id := gid s!"[{source.name},{target.name}]"
                   description := s!"Functor category [{source.name}, {target.name}]" }

  -- Natural transformation components: for each object a of C,
  -- a morphism α_a : F(a) → G(a) in D
  let natTransComponents := source.objects.map fun a =>
    { id := { name := .app (.root "α") a.id.name, index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      codomain := .atom { name := .app (.root "G") a.id.name, index := 0, kind := .sort }
      description := s!"Component of natural transformation at {a.id.name}" : Generator1 }

  -- Identity natural transformation: id_F with components id_{F(a)}
  let idComponents := source.objects.map fun a =>
    { id := { name := .app (.root "id_F") a.id.name, index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      codomain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      description := s!"Identity nat trans component at {a.id.name}" : Generator1 }

  -- Vertical composition: (β ∘ α)_a = β_a ∘ α_a
  let compComponents := source.objects.map fun a =>
    { id := { name := .app (.root "β∘α") a.id.name, index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort }
      codomain := .atom { name := .app (.root "H") a.id.name, index := 0, kind := .sort }
      description := s!"Vertical composition component at {a.id.name}" : Generator1 }

  -- Naturality squares: for each morphism f : a → b in C,
  -- G(f) ∘ α_a = α_b ∘ F(f)
  let naturalityAxioms := source.morphisms.map fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    { id := { name := .app (.root "naturality") f.id.name, index := 0, kind := .twoCell }
      leftPath := .comp (.atom { name := .app (.root "α") domName, index := 0, kind := .morphism })
                        (.atom { name := .app (.root "G") f.id.name, index := 0, kind := .morphism })
      rightPath := .comp (.atom { name := .app (.root "F") f.id.name, index := 0, kind := .morphism })
                         (.atom { name := .app (.root "α") codName, index := 0, kind := .morphism })
      description := s!"Naturality: G({f.id.name}) ∘ α = α ∘ F({f.id.name})" : Generator2 }

  -- Vertical composition law: (β ∘ α)_a = β_a ∘ α_a
  let compAxioms := source.objects.map fun a =>
    { id := { name := .app (.root "vcomp") a.id.name, index := 0, kind := .twoCell }
      leftPath := .atom { name := .app (.root "β∘α") a.id.name, index := 0, kind := .morphism }
      rightPath := .comp
        (.atom { name := .app (.root "α") a.id.name, index := 0, kind := .morphism })
        (.atom { name := .app (.root "β") a.id.name, index := 0, kind := .morphism })
      description := s!"Vertical composition: (β∘α)_{a.id.name} = β ∘ α" : Generator2 }

  -- Identity law: (id_F)_a = id_{F(a)}
  let idAxioms := source.objects.map fun a =>
    { id := { name := .app (.root "id_law") a.id.name, index := 0, kind := .twoCell }
      leftPath := .atom { name := .app (.root "id_F") a.id.name, index := 0, kind := .morphism }
      rightPath := .id (.atom { name := .app (.root "F") a.id.name, index := 0, kind := .sort })
      description := s!"Identity: (id_F)_{a.id.name} = id" : Generator2 }

  { name := s!"[{source.name}, {target.name}]"
    doctrine := target.doctrine
    objects := [funcObj]
    morphisms := natTransComponents ++ idComponents ++ compComponents
    axioms := naturalityAxioms ++ compAxioms ++ idAxioms }

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
