/-
  CatLab — Kleisli Category

  Given a monad T on a category C, the Kleisli category C_T has:
  - Objects: same as C
  - Morphisms A → B in C_T: morphisms A → T(B) in C
  - Composition: uses the monad multiplication μ
  - Identity: the unit η_A : A → T(A)
-/

import Catlab.Core.Theory
import Catlab.Operators.Monad

namespace CatLab

/-- Compute the Kleisli category C_T for a monad T.

    Objects are the same as the base category. A Kleisli morphism
    A → B is a morphism A → T(B) in the base. Composition of
    f♯ : A → T(B) and g♯ : B → T(C) is μ_C ∘ T(g♯) ∘ f♯.
    The identity on A is η_A : A → T(A). -/
def kleisliCategory (m : MonadData) : Theory :=
  -- Objects are the same as the base category
  let klObjects := m.base.objects.map fun a =>
    { id := { name := a.id.name, kind := .sort }
      description := s!"Kleisli object {a.id.name}" }

  -- For each morphism f : A → B in the base, we get a Kleisli morphism
  -- A → B whose underlying map is η_B ∘ f : A → T(B)
  let klMorphisms := m.base.morphisms.map fun f =>
    { id := { name := .app (.root "kl") f.id.name, kind := .morphism }
      domain := f.domain
      codomain := f.codomain
      description := s!"Kleisli morphism from {f.id.name}" }

  -- Kleisli identity: η_A : A → T(A) represents id_A in Kleisli
  let klIdentities := m.base.objects.map fun a =>
    { id := { name := .app (.root "η") a.id.name, kind := .morphism }
      domain := .atom a.id
      codomain := .atom a.id
      description := s!"Kleisli identity (unit) on {a.id.name}" }

  -- Left unit law: η ⊛ f = f
  let leftUnitAxioms := m.base.morphisms.map fun f =>
    let klF := { name := .app (.root "kl") f.id.name, kind := .morphism }
    let domName := f.domain.toName
    let klId := { name := .app (.root "η") domName, kind := .morphism }
    { id := gid s!"kl_left_unit_{f.id.name}"
      leftPath := .comp (.atom klId) (.atom klF)
      rightPath := .atom klF
      description := s!"Left unit: η ⊛ f = f for {f.id.name}" }

  -- Right unit law: f ⊛ η = f
  let rightUnitAxioms := m.base.morphisms.map fun f =>
    let klF := { name := .app (.root "kl") f.id.name, kind := .morphism }
    let codName := f.codomain.toName
    let klId := { name := .app (.root "η") codName, kind := .morphism }
    { id := gid s!"kl_right_unit_{f.id.name}"
      leftPath := .comp (.atom klF) (.atom klId)
      rightPath := .atom klF
      description := s!"Right unit: f ⊛ η = f for {f.id.name}" }

  { name := s!"{m.base.name}_T"
    doctrine := m.base.doctrine
    objects := klObjects
    morphisms := klMorphisms ++ klIdentities
    axioms := leftUnitAxioms ++ rightUnitAxioms }

end CatLab
