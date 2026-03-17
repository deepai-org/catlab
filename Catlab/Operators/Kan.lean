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

/-- A functor between theories, mapping generators to generators -/
structure TheoryFunctor where
  name : String
  source : Theory
  target : Theory
  /-- How objects map -/
  onObjects : GeneratorId → Expr
  /-- How morphisms map -/
  onMorphisms : GeneratorId → Expr

/-- Compute the left Kan extension Lan_K F.

    For each object b in B, (Lan_K F)(b) is the colimit (coend)
    over all a in A of Hom(Ka, b) × F(a). -/
def leftKan (k : TheoryFunctor) (f : TheoryFunctor) : Theory :=
  -- For each object b in K.target (= B), compute the coend
  let lanObjects := k.target.objects.map fun b =>
    { id := ⟨s!"Lan({b.id.name})", 0⟩
      description := s!"Left Kan extension at {b.id.name}: colimit over A" }

  -- The universal cocone: for each a in A, we have a map
  -- Hom(Ka, b) × F(a) → (Lan_K F)(b)
  let lanMorphisms := k.target.objects.flatMap fun b =>
    k.source.objects.map fun a =>
      { id := ⟨s!"lan_component_{a.id.name}_{b.id.name}", 0⟩
        domain := .prod (.hom (k.onObjects a.id) (.atom b.id))
                        (f.onObjects a.id)
        codomain := .atom ⟨s!"Lan({b.id.name})", 0⟩
        description := s!"Lan cocone component at ({a.id.name},{b.id.name})" }

  -- Dinaturality / coend condition: the cocone is compatible with morphisms in A
  let dinaturality := k.source.morphisms.map fun m =>
    { id := ⟨s!"lan_dinat_{m.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"lan_component_{repr m.domain}_{repr m.codomain}", 0⟩) (.atom ⟨"coend_glue", 0⟩)
      rightPath := .atom ⟨s!"lan_component_{repr m.codomain}_{repr m.codomain}", 0⟩
      description := s!"Dinaturality for Lan along {m.id.name}" }

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
    { id := ⟨s!"Ran({b.id.name})", 0⟩
      description := s!"Right Kan extension at {b.id.name}: limit over A" }

  let ranMorphisms := k.target.objects.flatMap fun b =>
    k.source.objects.map fun a =>
      { id := ⟨s!"ran_component_{a.id.name}_{b.id.name}", 0⟩
        domain := .atom ⟨s!"Ran({b.id.name})", 0⟩
        codomain := .hom (.hom (.atom b.id) (k.onObjects a.id))
                         (f.onObjects a.id)
        description := s!"Ran cone component at ({a.id.name},{b.id.name})" }

  { name := s!"Ran_{k.name}({f.name})"
    doctrine := f.target.doctrine
    objects := ranObjects
    morphisms := ranMorphisms
    axioms := [] }

end CatLab
