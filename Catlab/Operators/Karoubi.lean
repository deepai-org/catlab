/-
  CatLab — Karoubi Envelope (Idempotent Completion)

  Given a theory C, the Karoubi envelope Split(C) formally splits all idempotents.

  Objects: pairs (A, e) where e : A → A is idempotent (e ∘ e = e).
  Morphisms: (A,e) → (B,f) are morphisms g : A → B with f ∘ g ∘ e = g.

  Every idempotent in Split(C) splits, and C embeds fully faithfully via A ↦ (A, id_A).
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

/-- Compute the Karoubi envelope (idempotent completion) of a theory.

    For each object A, we include (A, id_A) as an object.
    For each endomorphism e : A → A, we add a split object with
    retraction r and section s satisfying s ∘ r = e and r ∘ s = id. -/
def karoubiEnvelope (t : Theory) : Theory :=
  -- Every object A gives rise to the trivial splitting (A, id_A)
  let trivialObjects : List Generator0 := t.objects.map fun obj =>
    { id := ⟨s!"({obj.id.name},id)", 0⟩
      description := s!"Karoubi object ({obj.id.name}, id)" }

  -- For each endomorphism e : A → A, add a split object
  let endoMorphisms := t.morphisms.filter fun m =>
    m.domain == m.codomain
  let endoObjects : List Generator0 := endoMorphisms.map fun m =>
    { id := ⟨s!"({m.id.name}_split)", 0⟩
      description := s!"Karoubi split object for endomorphism {m.id.name}" }

  -- For each split object, add retraction r : A → split and section s : split → A
  let splitMorphisms : List Generator1 := endoMorphisms.flatMap fun m =>
    [{ id := ⟨s!"r_{m.id.name}", 0⟩
       domain := m.domain
       codomain := .atom ⟨s!"({m.id.name}_split)", 0⟩
       description := s!"Retraction for splitting {m.id.name}" },
     { id := ⟨s!"s_{m.id.name}", 0⟩
       domain := .atom ⟨s!"({m.id.name}_split)", 0⟩
       codomain := m.domain
       description := s!"Section for splitting {m.id.name}" }]

  -- Axiom: s ∘ r = e
  let factorAxioms : List Generator2 := endoMorphisms.map fun m =>
    { id := ⟨s!"split_factor_{m.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"s_{m.id.name}", 0⟩) (.atom ⟨s!"r_{m.id.name}", 0⟩)
      rightPath := .atom m.id
      description := s!"Splitting axiom: s ∘ r = {m.id.name}" }

  -- Axiom: r ∘ s = id_(split)
  let retractionAxioms : List Generator2 := endoMorphisms.map fun m =>
    { id := ⟨s!"split_retract_{m.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"r_{m.id.name}", 0⟩) (.atom ⟨s!"s_{m.id.name}", 0⟩)
      rightPath := Expr.id (.atom ⟨s!"({m.id.name}_split)", 0⟩)
      description := s!"Retraction axiom: r ∘ s = id" }

  { name := s!"Split({t.name})"
    doctrine := t.doctrine
    objects := trivialObjects ++ endoObjects
    morphisms := t.morphisms ++ splitMorphisms
    axioms := t.axioms ++ factorAxioms ++ retractionAxioms }

end CatLab
