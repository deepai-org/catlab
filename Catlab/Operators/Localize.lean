/-
  CatLab — Simplicial & Bousfield Localization

  Simplicial Localization: forces a class of morphisms W to become invertible,
  producing the ∞-categorical localization C[W⁻¹].

  Bousfield Localization: localizes with respect to a homology theory E,
  inverting all E-equivalences. Essential for stable homotopy theory.
-/

import Catlab.Core.Theory

namespace CatLab

/-- A class of "weak equivalences" in a theory: morphisms we want to invert. -/
structure WeakEquivalences where
  /-- The morphism generators to be inverted -/
  morphisms : List GeneratorId
  /-- The underlying theory -/
  theory : Theory

/-- Simplicial localization C[W⁻¹]: formally invert the weak equivalences.

    For each w : A → B in W, we add a formal inverse w⁻¹ : B → A
    and axioms w ∘ w⁻¹ = id, w⁻¹ ∘ w = id.

    In the ∞-categorical setting, these become homotopy inverses
    (computed via hammock localization). -/
def simplicialLocalize (we : WeakEquivalences) : Theory :=
  -- Add formal inverses for each weak equivalence
  let inverses := we.morphisms.filterMap fun wId =>
    we.theory.findMorphism wId.name |>.map fun w =>
      { id := gid s!"{wId.name}⁻¹"
        domain := w.codomain
        codomain := w.domain
        description := s!"Formal inverse of {wId.name}" }

  -- Add invertibility axioms
  let leftInvAxioms := we.morphisms.filterMap fun wId =>
    we.theory.findMorphism wId.name |>.map fun w =>
      { id := gid s!"left_inv_{wId.name}"
        leftPath := .comp (.atom (gid s!"{wId.name}⁻¹")) (.atom wId)
        rightPath := .id w.codomain
        description := s!"w⁻¹ ∘ w = id for {wId.name}" }

  let rightInvAxioms := we.morphisms.filterMap fun wId =>
    we.theory.findMorphism wId.name |>.map fun w =>
      { id := gid s!"right_inv_{wId.name}"
        leftPath := .comp (.atom wId) (.atom (gid s!"{wId.name}⁻¹"))
        rightPath := .id w.domain
        description := s!"w ∘ w⁻¹ = id for {wId.name}" }

  { we.theory with
    name := s!"{we.theory.name}[W⁻¹]"
    morphisms := we.theory.morphisms ++ inverses
    axioms := we.theory.axioms ++ leftInvAxioms ++ rightInvAxioms }

/-- A homology theory E, used for Bousfield localization.
    An E-equivalence is a morphism f such that E(f) is an isomorphism.
    Equivalences are stored as an explicit list (not a closure) so they can
    be inspected, serialized, and combined without black-box evaluation. -/
structure HomologyTheory where
  name : String
  /-- Which morphisms are E-equivalences -/
  equivalences : List GeneratorId
  /-- Optional classifier: given a theory, compute its equivalences dynamically.
      Prefer populating `equivalences` directly when possible. -/
  computeEquivalences : Option (Theory → List GeneratorId) := none

/-- Bousfield localization L_E: localize with respect to a homology theory.

    An object X is E-local if for every E-equivalence f : A → B,
    Hom(B, X) → Hom(A, X) is a bijection.

    L_E(X) is the universal E-local approximation of X. -/
def bousfieldLocalize (t : Theory) (e : HomologyTheory) : Theory :=
  -- Use dynamic computation if provided, otherwise use the stored list
  let eEquivs := match e.computeEquivalences with
    | some f => f t
    | none => e.equivalences
  let we := WeakEquivalences.mk eEquivs t
  let localized := simplicialLocalize we

  -- Add E-local objects: for each object X, create L_E(X)
  let localObjects := t.objects.map fun x =>
    { id := gid s!"L_{e.name}({x.id.name})"
      description := s!"{e.name}-localization of {x.id.name}" }

  -- Localization maps: X → L_E(X)
  let locMaps := t.objects.map fun x =>
    { id := gid s!"loc_{x.id.name}"
      domain := .atom x.id
      codomain := .atom (gid s!"L_{e.name}({x.id.name})")
      description := s!"Localization map for {x.id.name}" }

  { localized with
    name := s!"L_{e.name}({t.name})"
    doctrine := { doctrine := .StableCategory }
    objects := localized.objects ++ localObjects
    morphisms := localized.morphisms ++ locMaps }

end CatLab
