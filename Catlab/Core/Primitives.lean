/-
  CatLab -- Tier 1 Primitives: Initial and Terminal Theories

  The two boundary objects in the category of theories, together with
  their canonical morphisms. These are the foundation for the Tier 2
  combinators:

    Coproduct(T₁, T₂) = pushout (initialMorphism T₁) (initialMorphism T₂)
    Terminal collapse  = terminalMorphism T
-/

import Catlab.Core.Equality

namespace CatLab

/-- The initial theory ⊥: no generators, no axioms.
    Every theory T has a unique morphism ⊥ → T (the empty map).
    The pushout of T₁ ← ⊥ → T₂ is the coproduct (disjoint union) of T₁ and T₂. -/
def initialTheory : Theory :=
  { name     := "⊥"
    doctrine := { doctrine := .Category }
    objects  := []
    morphisms := []
    axioms   := [] }

/-- The terminal theory ⊤: a single object ⋆ with only its identity.
    Every theory T has a unique morphism T → ⊤ (collapse all to ⋆). -/
def terminalTheory : Theory :=
  let star : GeneratorId := { name := .root "⋆", kind := .sort }
  { name      := "⊤"
    doctrine  := { doctrine := .Category }
    objects   := [{ id := star }]
    morphisms := []
    axioms    := [] }

/-- The unique morphism ⊥ → T: empty maps on both objects and morphisms. -/
def initialMorphism (t : Theory) : TheoryMorphism :=
  { name        := s!"⊥ → {t.name}"
    source      := initialTheory
    target      := t
    onObjects   := GeneratorMap.empty
    onMorphisms := GeneratorMap.empty }

/-- The unique morphism T → ⊤: sends every object to ⋆ and every morphism to id(⋆). -/
def terminalMorphism (t : Theory) : TheoryMorphism :=
  let star : Expr := .atom { name := .root "⋆", kind := .sort }
  { name        := s!"{t.name} → ⊤"
    source      := t
    target      := terminalTheory
    onObjects   := GeneratorMap.ofList (t.objects.map   fun o => (o.id, star))
    onMorphisms := GeneratorMap.ofList (t.morphisms.map fun m => (m.id, .id star)) }

end CatLab
