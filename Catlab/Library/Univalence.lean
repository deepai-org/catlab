/-
  CatLab — Univalence Infrastructure

  This module defines the key concepts needed for a complete ∞-topos:

  1. **isProp / isContr / isEquiv** — Expr-level macros for h-level predicates
  2. **fiber / Equiv** — The equivalence type as a Σ-type
  3. **ua / idToEquiv** — The Univalence Axiom as global constants
  4. **Ω (hProp)** — The subobject classifier (universe of propositions)

  All definitions use existing Expr constructors (pi, sigma, path, univ, app, lam).
  No new AST nodes are needed.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

-- ============================================================
-- Expr-level macros for HoTT predicates
-- ============================================================

/-- isProp(A) := Π(x y : A). path(A, x, y)
    A type is a proposition if any two elements are equal. -/
def Expr.isProp (A : Expr) : Expr :=
  .pi "x" A (.pi "y" A (.path (A.liftBVars 2 0) (.bvar 1) (.bvar 0)))

/-- isContr(A) := Σ(center : A). Π(x : A). path(A, center, x)
    A type is contractible if it has a center and all points are equal to it. -/
def Expr.isContr (A : Expr) : Expr :=
  .sigma "center" A
    (.pi "x" (A.liftBVars 1 0)
      (.path (A.liftBVars 2 0) (.bvar 1) (.bvar 0)))

/-- fiber(f, y) := Σ(x : A). path(B, app(f, x), y)
    The homotopy fiber of f : A → B over a point y : B. -/
def Expr.hfiber (A B f y : Expr) : Expr :=
  .sigma "x" A
    (.path (B.liftBVars 1 0) (.app (f.liftBVars 1 0) (.bvar 0)) (y.liftBVars 1 0))

/-- isEquiv(f) := Π(y : B). isContr(fiber(f, y))
    A map f : A → B is an equivalence if all its fibers are contractible. -/
def Expr.isEquiv (A B f : Expr) : Expr :=
  .pi "y" B
    (Expr.isContr (Expr.hfiber (A.liftBVars 1 0) (B.liftBVars 1 0) (f.liftBVars 1 0) (.bvar 0)))

/-- Equiv(A, B) := Σ(f : A → B). isEquiv(f)
    The type of equivalences between A and B. -/
def Expr.equiv (A B : Expr) : Expr :=
  .sigma "f" (.pi "_" A B)
    (Expr.isEquiv (A.liftBVars 1 0) (B.liftBVars 1 0) (.bvar 0))

/-- isProp as a standalone predicate on a universe element. -/
def Expr.hProp (n : Nat := 0) : Expr :=
  .sigma "A" (.univ n) (Expr.isProp (.bvar 0))

-- ============================================================
-- The Univalence Theory
-- ============================================================

/-- Theory of Univalence: the core axioms connecting equivalences and paths in U.

    Contains:
    - Two sorts A, B at universe level n
    - ua : Equiv(A, B) → path(U_n, A, B)
    - idToEquiv : path(U_n, A, B) → Equiv(A, B)
    - Roundtrip axioms: ua ∘ idToEquiv = id, idToEquiv ∘ ua = id -/
def TheoryOfUnivalence (n : Nat := 0) : Theory :=
  let U := Expr.univ n
  let A := Expr.atom { name := .root "A", kind := .sort }
  let B := Expr.atom { name := .root "B", kind := .sort }
  let equivAB := Expr.equiv A B
  let pathAB := Expr.path U A B
  { name := s!"Univalence(U_{n})"
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects := [
      { id := { name := .root "A", kind := .sort }, description := "Type A" },
      { id := { name := .root "B", kind := .sort }, description := "Type B" }
    ]
    morphisms := [
      -- ua : Equiv(A,B) → path(U_n, A, B)
      { id := { name := .root "ua", kind := .morphism }
        domain := equivAB
        codomain := pathAB
        description := s!"Univalence: ua turns equivalences into paths in U_{n}" },
      -- idToEquiv : path(U_n, A, B) → Equiv(A, B)
      { id := { name := .root "idToEquiv", kind := .morphism }
        domain := pathAB
        codomain := equivAB
        description := s!"Canonical map: paths in U_{n} give equivalences" }
    ]
    axioms := [
      -- ua ∘ idToEquiv = id  (ua is a retraction)
      { id := { name := .root "ua_retraction", kind := .twoCell }
        leftPath := .comp (.atom { name := .root "idToEquiv", kind := .morphism })
                          (.atom { name := .root "ua", kind := .morphism })
        rightPath := .id pathAB
        description := "ua ∘ idToEquiv = id (ua is a retraction)" },
      -- idToEquiv ∘ ua = id  (ua is a section)
      { id := { name := .root "ua_section", kind := .twoCell }
        leftPath := .comp (.atom { name := .root "ua", kind := .morphism })
                          (.atom { name := .root "idToEquiv", kind := .morphism })
        rightPath := .id equivAB
        description := "idToEquiv ∘ ua = id (ua is a section)" }
    ] }

-- ============================================================
-- The Subobject Classifier Ω
-- ============================================================

/-- Theory of hProp (the subobject classifier Ω of an ∞-topos).

    Ω := Σ(A : U_0). isProp(A)

    This is the universe of mere propositions. In a 1-topos this would be
    the subobject classifier {true, false}. In an ∞-topos it is the type
    of all h-propositions (types with at most one element up to paths). -/
def TheoryOfSubobjectClassifier : Theory :=
  let omegaId : GeneratorId := { name := .root "Ω", kind := .sort }
  { name := "SubobjectClassifier"
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects := [
      { id := omegaId
        description := "Ω = Σ(A : U₀). isProp(A) — the subobject classifier" }
    ]
    morphisms := [
      -- true : 1 → Ω  (the unit type is a proposition)
      { id := { name := .root "⊤_prop", kind := .morphism }
        domain := .terminal
        codomain := .atom omegaId
        description := "⊤ : 1 → Ω (unit is a proposition)" },
      -- false : 1 → Ω  (the empty type is a proposition)
      { id := { name := .root "⊥_prop", kind := .morphism }
        domain := .terminal
        codomain := .atom omegaId
        description := "⊥ : 1 → Ω (empty is a proposition)" },
      -- ∧ : Ω × Ω → Ω  (conjunction = product of propositions)
      { id := { name := .root "∧", kind := .morphism }
        domain := .prod (.atom omegaId) (.atom omegaId)
        codomain := .atom omegaId
        description := "Conjunction ∧ : Ω × Ω → Ω" },
      -- ∨ : Ω × Ω → Ω  (disjunction = truncated coproduct)
      { id := { name := .root "∨", kind := .morphism }
        domain := .prod (.atom omegaId) (.atom omegaId)
        codomain := .atom omegaId
        description := "Disjunction ∨ : Ω × Ω → Ω (propositionally truncated coproduct)" },
      -- ¬ : Ω → Ω  (negation = function to empty)
      { id := { name := .root "¬", kind := .morphism }
        domain := .atom omegaId
        codomain := .atom omegaId
        description := "Negation ¬ : Ω → Ω" },
      -- ⇒ : Ω × Ω → Ω  (implication = function type between propositions)
      { id := { name := .root "⇒", kind := .morphism }
        domain := .prod (.atom omegaId) (.atom omegaId)
        codomain := .atom omegaId
        description := "Implication ⇒ : Ω × Ω → Ω" }
    ]
    axioms := [
      -- De Morgan / Heyting algebra axioms
      -- ¬⊥ = ⊤
      { id := { name := .root "neg_bot", kind := .twoCell }
        leftPath := .comp (.atom { name := .root "⊥_prop", kind := .morphism })
                          (.atom { name := .root "¬", kind := .morphism })
        rightPath := .atom { name := .root "⊤_prop", kind := .morphism }
        description := "¬⊥ = ⊤" },
      -- ¬⊤ = ⊥
      { id := { name := .root "neg_top", kind := .twoCell }
        leftPath := .comp (.atom { name := .root "⊤_prop", kind := .morphism })
                          (.atom { name := .root "¬", kind := .morphism })
        rightPath := .atom { name := .root "⊥_prop", kind := .morphism }
        description := "¬⊤ = ⊥" }
    ] }

end CatLab
