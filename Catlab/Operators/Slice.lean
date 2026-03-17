/-
  CatLab — Slice Category (C/X)

  Given a theory C and an object X in C, the slice category C/X has:
  - Objects: morphisms f : A → X in C
  - Morphisms: commuting triangles over X
  - Axioms: inherited from C, relativized to the slice

  This is the "local context" operator.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute the slice theory C/X.

    Objects of C/X are morphisms into X.
    Morphisms of C/X are commuting triangles. -/
def slice (t : Theory) (x : Expr) : Theory :=
  -- Objects of C/X: each morphism f : A → X in the original theory
  -- whose codomain matches x becomes an object
  let sliceObjects := t.morphisms.filterMap fun g =>
    -- In a full implementation, we'd check codomain == x structurally
    some { id := { name := .root s!"({g.id.name} → X)", index := 0 }
           description := s!"Slice object: {g.id.name} over X" }

  -- Morphisms of C/X: for each pair of slice objects (f : A → X, g : B → X),
  -- a morphism h : A → B such that g ∘ h = f
  -- This is a placeholder; full implementation would enumerate commuting triangles
  let sliceMorphisms : List Generator1 := []

  { name := s!"{t.name}/X"
    doctrine := t.doctrine
    objects := sliceObjects
    morphisms := sliceMorphisms
    axioms := [] }

/-- The forgetful functor C/X → C: sends (f : A → X) ↦ A -/
def sliceForgetful (t : Theory) (x : Expr) : List Generator1 :=
  t.morphisms.filterMap fun g =>
    some { id := { name := .root s!"forget_{g.id.name}", index := 0 }
           domain := .atom { name := .root s!"({g.id.name} → X)", index := 0 }
           codomain := g.domain
           description := s!"Forgetful: slice object to domain" }

end CatLab
