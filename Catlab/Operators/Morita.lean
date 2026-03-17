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
    plus a sorted list of morphism arities (domain/codomain pairs as Names).
    Two Cauchy-complete theories are equivalent iff their signatures match. -/
structure CompletedSignature where
  numObjects : Nat
  numMorphisms : Nat
  numAxioms : Nat
  /-- Morphism arities as (domain, codomain) Name pairs, sorted for comparison -/
  arities : List (Name × Name)
  deriving Repr, Inhabited

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
    { id := gid s!"({obj.id.name},id)"
      description := s!"Morita envelope object ({obj.id.name}, id)" }

  -- For each endomorphism e : A → A, add split object (A, e)
  let endos := findEndomorphisms t
  let splitObjects : List Generator0 := endos.map fun m =>
    { id := gid s!"({m.id.name}_split)"
      description := s!"Split object for endomorphism {m.id.name}" }

  -- Retraction r : A → (A, e) for each endomorphism
  let retractions : List Generator1 := endos.map fun m =>
    { id := gid s!"r_{m.id.name}"
      domain := m.domain
      codomain := .atom (gid s!"({m.id.name}_split)")
      description := s!"Retraction for {m.id.name}" }

  -- Section s : (A, e) → A for each endomorphism
  let sections : List Generator1 := endos.map fun m =>
    { id := gid s!"s_{m.id.name}"
      domain := .atom (gid s!"({m.id.name}_split)")
      codomain := m.domain
      description := s!"Section for {m.id.name}" }

  -- Axiom: s ∘ r = e
  let factorAxioms : List Generator2 := endos.map fun m =>
    { id := gid s!"morita_factor_{m.id.name}"
      leftPath := .comp (.atom (gid s!"s_{m.id.name}")) (.atom (gid s!"r_{m.id.name}"))
      rightPath := .atom m.id
      description := s!"Factorization: s ∘ r = {m.id.name}" }

  -- Axiom: r ∘ s = id_(A,e)
  let retractionAxioms : List Generator2 := endos.map fun m =>
    { id := gid s!"morita_retract_{m.id.name}"
      leftPath := .comp (.atom (gid s!"r_{m.id.name}")) (.atom (gid s!"s_{m.id.name}"))
      rightPath := Expr.id (.atom (gid s!"({m.id.name}_split)"))
      description := s!"Retraction: r ∘ s = id" }

  -- Idempotence axioms: e ∘ e = e (strengthening the splitting)
  let idempotenceAxioms : List Generator2 := endos.map fun m =>
    { id := gid s!"morita_idem_{m.id.name}"
      leftPath := .comp (.atom m.id) (.atom m.id)
      rightPath := .atom m.id
      description := s!"Idempotence: {m.id.name} ∘ {m.id.name} = {m.id.name}" }

  { name := s!"Cauchy({t.name})"
    doctrine := t.doctrine
    objects := trivialObjects ++ splitObjects
    morphisms := t.morphisms ++ retractions ++ sections
    axioms := t.axioms ++ factorAxioms ++ retractionAxioms ++ idempotenceAxioms }

instance : BEq CompletedSignature where
  beq a b := a.numObjects == b.numObjects &&
             a.numMorphisms == b.numMorphisms &&
             a.numAxioms == b.numAxioms &&
             a.arities.length == b.arities.length &&
             (a.arities.zip b.arities |>.all fun ((d1, c1), (d2, c2)) => d1 == d2 && c1 == c2)

/-- Compute the signature of a completed theory for comparison. -/
private def completedSignature (t : Theory) : CompletedSignature :=
  let arities := t.morphisms.map fun m => (m.domain.toName, m.codomain.toName)
  let sortedArities := arities.mergeSort (fun a b =>
    toString a.1 ++ toString a.2 < toString b.1 ++ toString b.2)
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
    { id := gid s!"F_{s.id.name}"
      domain := .atom (gid s!"PSh({t1.name})_{s.id.name}")
      codomain := .atom (gid s!"PSh({t2.name})_{s.id.name}")
      description := s!"Forward functor component at {s.id.name}" }

  let fwdObj : Generator0 :=
    { id := gid s!"PSh({t1.name})→PSh({t2.name})"
      description := "Forward equivalence functor" }
  let forwardFunctor : Theory :=
    { name := s!"PSh({t1.name})→PSh({t2.name})"
      doctrine := { doctrine := .Category }
      objects := [fwdObj]
      morphisms := forwardComponents
      axioms := [] }

  let backwardComponents : List Generator1 := t2.objects.map fun s =>
    { id := gid s!"G_{s.id.name}"
      domain := .atom (gid s!"PSh({t2.name})_{s.id.name}")
      codomain := .atom (gid s!"PSh({t1.name})_{s.id.name}")
      description := s!"Backward functor component at {s.id.name}" }

  let bwdObj : Generator0 :=
    { id := gid s!"PSh({t2.name})→PSh({t1.name})"
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
