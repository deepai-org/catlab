/-
  CatLab — Kan Extensions (Lan, Ran)

  "All concepts are Kan extensions." — Saunders Mac Lane

  Given a functor K : A → B and a functor F : A → C,
  - Left Kan extension  (Lan_K F) : B → C  is the "best approximation from the left"
  - Right Kan extension (Ran_K F) : B → C  is the "best approximation from the right"

  Computed via the (co)end formulas:
    (Lan_K F)(b) = ∫^{a ∈ A} Hom(Ka, b) ⊗ F(a)   (colimit formula)
    (Ran_K F)(b) = ∫_{a ∈ A} [Hom(b, Ka), F(a)]    (limit formula)
-/

import Catlab.Core.Theory

namespace CatLab

/-- A functor between theories, mapping generators to generators.
    Uses explicit GeneratorMaps instead of opaque closures. -/
structure TheoryFunctor where
  name : String
  source : Theory
  target : Theory
  /-- How objects map -/
  onObjects : GeneratorMap
  /-- How morphisms map -/
  onMorphisms : GeneratorMap

/-- Compute the left Kan extension Lan_K F.

    For each object b in B, (Lan_K F)(b) is the colimit (coend)
    over all a in A of Hom(Ka, b) × F(a). -/
def leftKan (k : TheoryFunctor) (f : TheoryFunctor) : Theory :=
  -- For each object b in K.target (= B), compute the coend
  let lanObjects := k.target.objects.map fun b =>
    { id := { name := .root s!"Lan({b.id.name})", index := 0 }
      description := s!"Left Kan extension at {b.id.name}: colimit over A" }

  -- The universal cocone: for each a in A, we have a map
  -- Hom(Ka, b) × F(a) → (Lan_K F)(b)
  let lanMorphisms := k.target.objects.flatMap fun b =>
    k.source.objects.map fun a =>
      let aName := a.id.name.toString
      let bName := b.id.name.toString
      { id := { name := .root s!"lan_component_{aName}_{bName}", index := 0 }
        domain := .prod (.hom (k.onObjects.apply a.id) (.atom b.id))
                        (f.onObjects.apply a.id)
        codomain := .atom { name := .root s!"Lan({b.id.name})", index := 0 }
        description := s!"Lan cocone component at ({aName},{bName})" }

  -- Dinaturality / coend condition: for each morphism m : a → a' in A,
  -- the two ways of mapping through the cocone agree.
  -- lan_component_{a,b} = lan_component_{a',b} ∘ (Hom(Km, id_b) × F(m))
  let dinaturality := k.source.morphisms.flatMap fun m =>
    let domName := m.domain.toName.toString
    let codName := m.codomain.toName.toString
    k.target.objects.map fun b =>
      let bName := b.id.name.toString
      { id := { name := .root s!"lan_dinat_{m.id.name}_{bName}", index := 0, kind := .twoCell }
        leftPath := .atom { name := .root s!"lan_component_{domName}_{bName}", index := 0, kind := .morphism }
        rightPath := .atom { name := .root s!"lan_component_{codName}_{bName}", index := 0, kind := .morphism }
        description := s!"Dinaturality for Lan along {m.id.name} at {bName}" : Generator2 }

  { name := s!"Lan_{k.name}({f.name})"
    doctrine := f.target.doctrine
    objects := lanObjects
    morphisms := lanMorphisms
    axioms := dinaturality }

/-- Compute the right Kan extension Ran_K F.

    For each object b in B, (Ran_K F)(b) is the limit (end)
    over all a in A of [Hom(b, Ka), F(a)]. -/
def rightKan (k : TheoryFunctor) (f : TheoryFunctor) : Theory :=
  let ranObjects := k.target.objects.map fun b =>
    { id := { name := .root s!"Ran({b.id.name})", index := 0 }
      description := s!"Right Kan extension at {b.id.name}: limit over A" }

  let ranMorphisms := k.target.objects.flatMap fun b =>
    k.source.objects.map fun a =>
      { id := { name := .root s!"ran_component_{a.id.name}_{b.id.name}", index := 0 }
        domain := .atom { name := .root s!"Ran({b.id.name})", index := 0 }
        codomain := .hom (.hom (.atom b.id) (k.onObjects.apply a.id))
                         (f.onObjects.apply a.id)
        description := s!"Ran cone component at ({a.id.name},{b.id.name})" }

  -- Dinaturality / end condition: for each morphism m : a → a' in A,
  -- the cone components are compatible.
  let dinaturality := k.source.morphisms.flatMap fun m =>
    let domName := m.domain.toName.toString
    let codName := m.codomain.toName.toString
    k.target.objects.map fun b =>
      let bName := b.id.name.toString
      { id := { name := .root s!"ran_dinat_{m.id.name}_{bName}", index := 0, kind := .twoCell }
        leftPath := .atom { name := .root s!"ran_component_{domName}_{bName}", index := 0, kind := .morphism }
        rightPath := .atom { name := .root s!"ran_component_{codName}_{bName}", index := 0, kind := .morphism }
        description := s!"Dinaturality for Ran along {m.id.name} at {bName}" : Generator2 }

  { name := s!"Ran_{k.name}({f.name})"
    doctrine := f.target.doctrine
    objects := ranObjects
    morphisms := ranMorphisms
    axioms := dinaturality }

end CatLab
