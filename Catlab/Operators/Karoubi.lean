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
    { id := gid s!"({obj.id.name},id)"
      description := s!"Karoubi object ({obj.id.name}, id)" }

  -- For each endomorphism e : A → A, add a split object
  let endoMorphisms := t.morphisms.filter fun m =>
    m.domain == m.codomain
  let endoObjects : List Generator0 := endoMorphisms.map fun m =>
    { id := gid s!"({m.id.name}_split)"
      description := s!"Karoubi split object for endomorphism {m.id.name}" }

  -- For each split object, add retraction r : A → split and section s : split → A
  let splitMorphisms : List Generator1 := endoMorphisms.flatMap fun m =>
    [{ id := gid s!"r_{m.id.name}"
       domain := m.domain
       codomain := .atom (gid s!"({m.id.name}_split)")
       description := s!"Retraction for splitting {m.id.name}" },
     { id := gid s!"s_{m.id.name}"
       domain := .atom (gid s!"({m.id.name}_split)")
       codomain := m.domain
       description := s!"Section for splitting {m.id.name}" }]

  -- Axiom: s ∘ r = e
  let factorAxioms : List Generator2 := endoMorphisms.map fun m =>
    { id := gid s!"split_factor_{m.id.name}"
      leftPath := .comp (.atom (gid s!"s_{m.id.name}")) (.atom (gid s!"r_{m.id.name}"))
      rightPath := .atom m.id
      description := s!"Splitting axiom: s ∘ r = {m.id.name}" }

  -- Axiom: r ∘ s = id_(split)
  let retractionAxioms : List Generator2 := endoMorphisms.map fun m =>
    { id := gid s!"split_retract_{m.id.name}"
      leftPath := .comp (.atom (gid s!"r_{m.id.name}")) (.atom (gid s!"s_{m.id.name}"))
      rightPath := Expr.id (.atom (gid s!"({m.id.name}_split)"))
      description := s!"Retraction axiom: r ∘ s = id" }

  (Theory.mk' s!"Split({t.name})" t.doctrine
    (t.objects ++ trivialObjects ++ endoObjects)
    (t.morphisms ++ splitMorphisms)
    (t.axioms ++ factorAxioms ++ retractionAxioms)).dedup

end CatLab
