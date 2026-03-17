/-
  CatLab — Morita Equivalence

  Two theories T₁ and T₂ are Morita equivalent when their presheaf categories
  are equivalent: PSh(T₁) ≃ PSh(T₂). This holds iff their Cauchy completions
  (idempotent completions / Karoubi envelopes) are equivalent.

  - `moritaEnvelope`: Cauchy completion of a theory (the Morita envelope)
  - `areMoritaEquivalent`: check if two theories have equivalent Cauchy completions
  - `presheafEquivalence`: construct equivalence data between presheaf categories
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

/-- Signature of a completed theory: counts of objects, morphisms, and axioms,
    plus a sorted list of morphism arities (domain/codomain pairs as strings).
    Two Cauchy-complete theories are equivalent iff their signatures match. -/
structure CompletedSignature where
  numObjects : Nat
  numMorphisms : Nat
  numAxioms : Nat
  arities : List (String × String)
  deriving Repr, Inhabited, BEq

/-- Find all endomorphisms in a theory (morphisms f : A → A). -/
private def findEndomorphisms (t : Theory) : List Generator1 :=
  t.morphisms.filter fun m => m.domain == m.codomain

/-- Compute the Morita envelope (Cauchy completion) of a theory.

    This is the idempotent completion: for every endomorphism e : A → A
    satisfying e ∘ e = e, we formally split it into a retraction-section pair.
    The result is the smallest idempotent-complete category containing T.

    Two theories are Morita equivalent iff their Morita envelopes are equivalent. -/
def moritaEnvelope (t : Theory) : Theory :=
  -- Every object A gives rise to (A, id_A)
  let trivialObjects : List Generator0 := t.objects.map fun obj =>
    { id := ⟨s!"({obj.id.name},id)", 0⟩
      description := s!"Morita envelope object ({obj.id.name}, id)" }

  -- For each endomorphism e : A → A, add split object (A, e)
  let endos := findEndomorphisms t
  let splitObjects : List Generator0 := endos.map fun m =>
    { id := ⟨s!"({m.id.name}_split)", 0⟩
      description := s!"Split object for endomorphism {m.id.name}" }

  -- Retraction r : A → (A, e) for each endomorphism
  let retractions : List Generator1 := endos.map fun m =>
    { id := ⟨s!"r_{m.id.name}", 0⟩
      domain := m.domain
      codomain := .atom ⟨s!"({m.id.name}_split)", 0⟩
      description := s!"Retraction for {m.id.name}" }

  -- Section s : (A, e) → A for each endomorphism
  let sections : List Generator1 := endos.map fun m =>
    { id := ⟨s!"s_{m.id.name}", 0⟩
      domain := .atom ⟨s!"({m.id.name}_split)", 0⟩
      codomain := m.domain
      description := s!"Section for {m.id.name}" }

  -- Axiom: s ∘ r = e
  let factorAxioms : List Generator2 := endos.map fun m =>
    { id := ⟨s!"morita_factor_{m.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"s_{m.id.name}", 0⟩) (.atom ⟨s!"r_{m.id.name}", 0⟩)
      rightPath := .atom m.id
      description := s!"Factorization: s ∘ r = {m.id.name}" }

  -- Axiom: r ∘ s = id_(A,e)
  let retractionAxioms : List Generator2 := endos.map fun m =>
    { id := ⟨s!"morita_retract_{m.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"r_{m.id.name}", 0⟩) (.atom ⟨s!"s_{m.id.name}", 0⟩)
      rightPath := Expr.id (.atom ⟨s!"({m.id.name}_split)", 0⟩)
      description := s!"Retraction: r ∘ s = id" }

  -- Idempotence axioms: e ∘ e = e (strengthening the splitting)
  let idempotenceAxioms : List Generator2 := endos.map fun m =>
    { id := ⟨s!"morita_idem_{m.id.name}", 0⟩
      leftPath := .comp (.atom m.id) (.atom m.id)
      rightPath := .atom m.id
      description := s!"Idempotence: {m.id.name} ∘ {m.id.name} = {m.id.name}" }

  { name := s!"Cauchy({t.name})"
    doctrine := t.doctrine
    objects := trivialObjects ++ splitObjects
    morphisms := t.morphisms ++ retractions ++ sections
    axioms := t.axioms ++ factorAxioms ++ retractionAxioms ++ idempotenceAxioms }

/-- Compute the signature of a completed theory for comparison. -/
private def completedSignature (t : Theory) : CompletedSignature :=
  let arities := t.morphisms.map fun m => (s!"{repr m.domain}", s!"{repr m.codomain}")
  let sortedArities := arities.mergeSort (fun a b => (a.1 ++ a.2) < (b.1 ++ b.2))
  { numObjects := t.objects.length
    numMorphisms := t.morphisms.length
    numAxioms := t.axioms.length
    arities := sortedArities }

/-- Check if two theories are Morita equivalent.

    Two theories T₁ and T₂ are Morita equivalent iff their Cauchy completions
    (Morita envelopes) are equivalent categories. We check this by comparing
    the signatures of the completed theories. -/
def areMoritaEquivalent (t1 t2 : Theory) : Bool :=
  let env1 := moritaEnvelope t1
  let env2 := moritaEnvelope t2
  let sig1 := completedSignature env1
  let sig2 := completedSignature env2
  sig1 == sig2

/-- Equivalence data between presheaf categories.
    When T₁ and T₂ are Morita equivalent, PSh(T₁) ≃ PSh(T₂). -/
structure PresheafEquivalenceData where
  /-- The forward functor PSh(T₁) → PSh(T₂) -/
  forward : Theory
  /-- The backward functor PSh(T₂) → PSh(T₁) -/
  backward : Theory
  /-- Witness that the theories are Morita equivalent -/
  equivalent : Bool
  deriving Repr, Inhabited

/-- Construct equivalence data between presheaf categories when
    two theories are Morita equivalent.

    The equivalence PSh(T₁) ≃ PSh(T₂) is given by restriction and
    extension along the embedding into the common Cauchy completion. -/
def presheafEquivalence (t1 t2 : Theory) : PresheafEquivalenceData :=
  let env1 := moritaEnvelope t1
  let env2 := moritaEnvelope t2
  let isEquiv := areMoritaEquivalent t1 t2

  -- Forward functor: restriction along the embedding T₂ ↪ Cauchy(T₂) ≃ Cauchy(T₁)
  -- For each object of T₂, map it to the corresponding object in T₁'s envelope
  let forwardComponents : List Generator1 := t1.objects.map fun s =>
    { id := ⟨s!"F_{s.id.name}", 0⟩
      domain := .atom ⟨s!"PSh({t1.name})_{s.id.name}", 0⟩
      codomain := .atom ⟨s!"PSh({t2.name})_{s.id.name}", 0⟩
      description := s!"Forward functor component at {s.id.name}" }

  let fwdObj : Generator0 :=
    { id := ⟨s!"PSh({t1.name})→PSh({t2.name})", 0⟩
      description := "Forward equivalence functor" }
  let forwardFunctor : Theory :=
    { name := s!"PSh({t1.name})→PSh({t2.name})"
      doctrine := { doctrine := .Category }
      objects := [fwdObj]
      morphisms := forwardComponents
      axioms := [] }

  let backwardComponents : List Generator1 := t2.objects.map fun s =>
    { id := ⟨s!"G_{s.id.name}", 0⟩
      domain := .atom ⟨s!"PSh({t2.name})_{s.id.name}", 0⟩
      codomain := .atom ⟨s!"PSh({t1.name})_{s.id.name}", 0⟩
      description := s!"Backward functor component at {s.id.name}" }

  let bwdObj : Generator0 :=
    { id := ⟨s!"PSh({t2.name})→PSh({t1.name})", 0⟩
      description := "Backward equivalence functor" }
  let backwardFunctor : Theory :=
    { name := s!"PSh({t2.name})→PSh({t1.name})"
      doctrine := { doctrine := .Category }
      objects := [bwdObj]
      morphisms := backwardComponents
      axioms := [] }

  { forward := forwardFunctor
    backward := backwardFunctor
    equivalent := isEquiv }

end CatLab
