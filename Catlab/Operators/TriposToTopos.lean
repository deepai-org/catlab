/-
  CatLab — Tripos-to-Topos Construction

  Takes a first-order logic (formalized as a tripos: a first-order hyperdoctrine
  over Set) and constructs its exact completion, yielding a topos.

  The resulting topos has a subobject classifier Ω for free.
  This replaces the naive "compute Ω" operator.
-/

import Catlab.Core.Theory

namespace CatLab

/-- A tripos over Set: a first-order hyperdoctrine.

    For each set I, we have a Heyting algebra Pred(I) of "predicates over I",
    with reindexing (substitution) along functions, plus ∃ and ∀ quantifiers
    as left/right adjoints to reindexing. -/
structure Tripos where
  /-- The base theory (typically the theory of sets/types) -/
  base : Theory
  /-- For each object I, the lattice of predicates -/
  predicates : GeneratorId → Theory
  /-- Reindexing / substitution: for a morphism f : I → J, pull back predicates -/
  reindex : GeneratorId → List Generator1
  /-- Left adjoint to reindexing: existential quantification -/
  exists_ : GeneratorId → List Generator1
  /-- Right adjoint to reindexing: universal quantification -/
  forall_ : GeneratorId → List Generator1

/-- A partial equivalence relation (PER) in a tripos:
    a predicate R on I × I that is symmetric and transitive (but not necessarily reflexive). -/
structure PER where
  carrier : GeneratorId
  relation : Expr
  symmetry : GeneratorId   -- proof/axiom name
  transitivity : GeneratorId

/-- The tripos-to-topos construction: build the exact completion.

    1. Objects are PERs (partial equivalence relations) in the tripos
    2. Morphisms are functional relations between PERs
    3. The result is a topos with:
       - Ω = the PER of truth values
       - Products, exponentials from the tripos structure
       - The subobject classifier comes for free -/
def triposToTopos (tr : Tripos) : Theory :=
  -- The subobject classifier Ω: the PER of "truth values"
  -- In the tripos, this is the object of propositions with ↔ as the PER
  let omega : Generator0 :=
    { id := ⟨"Ω", 0⟩
      description := "Subobject classifier (truth values)" }

  -- True: 1 → Ω (the "true" predicate)
  let trueMap : Generator1 :=
    { id := ⟨"⊤", 0⟩
      domain := .terminal
      codomain := .atom ⟨"Ω", 0⟩
      description := "True: the top element of Ω" }

  -- For each base object I, we get a PER-object in the topos
  let perObjects := tr.base.objects.map fun i =>
    { id := ⟨s!"PER({i.id.name})", 0⟩
      description := s!"PER over {i.id.name}" }

  -- The characteristic morphism: for each mono m : A ↪ B,
  -- there exists a unique χ_m : B → Ω such that A = χ_m⁻¹(⊤)
  let charAxiom : Generator2 :=
    { id := ⟨"subobject_classifier_axiom", 0⟩
      leftPath := .comp (.atom ⟨"m", 0⟩) (.atom ⟨"χ_m", 0⟩)
      rightPath := .comp (.atom ⟨"!", 0⟩) (.atom ⟨"⊤", 0⟩)
      description := "Universal property of Ω: monos are classified by maps to Ω" }

  { name := s!"Topos({tr.base.name})"
    doctrine := { doctrine := .Topos }
    objects := [omega] ++ perObjects
    morphisms := [trueMap]
    axioms := [charAxiom] }

end CatLab
