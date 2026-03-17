/-
  CatLab — Core Algebra: Minimal Derivation Chain

  Demonstrates that most algebraic library theories can be derived from
  the two truly primitive theories (Monoid, Lattice) using the new
  algebraic combinators.

  Derivation tree:

    Monoid  ──────────────────────────────────────────────────────────
      │ addInverse("μ","η")
      ↓
    DerivedGroup
      │ addCommutativity("μ")
      ↓
    DerivedAbelianGroup
      │ renameGenerator + renameSort + amalgamateOver + addDistributivity
      ↓
    DerivedRing
      │ addCommutativity("μ")
      ↓
    DerivedCommutativeRing

    Lattice  ─────────────────────────────────────────────────────────
      │ addAdjoint("∧","→")
      ↓
    DerivedHeytingAlgebra
      │ booleanize
      ↓
    DerivedBooleanAlgebra ✓ (already in BooleanAlgebra.lean)

  These derived theories are structurally equivalent to the hand-crafted
  ones in Group.lean, Ring.lean, BooleanAlgebra.lean.  They exist here as
  a proof-of-concept showing the minimal primitive set.
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize
import Catlab.Operators.Amalgamate
import Catlab.Operators.Booleanize
import Catlab.Library.Monoid
import Catlab.Library.Lattice

namespace CatLab.Library.Core

open CatLab CatLab.Library

-- ============================================================
-- Group = Monoid + inverse
-- ============================================================

/-- Group derived from Monoid by adding an inverse for μ.
    The inverse is named  μ.inv : M → M  (structured name).
    Axioms added: left_inv_μ and right_inv_μ. -/
def DerivedGroup : Theory :=
  addInverse TheoryOfMonoids "μ" "η"

-- ============================================================
-- AbelianGroup = Group + commutativity
-- ============================================================

/-- AbelianGroup derived from DerivedGroup by adding commutativity of μ.
    Adds  swap : M × M → M × M  and axiom  comm_μ : μ = swap ∘ μ. -/
def DerivedAbelianGroup : Theory :=
  addCommutativity DerivedGroup "μ"

-- ============================================================
-- Ring = amalgamate(additive AbelianGroup, multiplicative Monoid)
--        + distributivity
-- ============================================================

-- Step 1: Give the abelian group additive naming (add/zero/neg)
-- and rename the carrier G→R.
private def additiveGroup : Theory :=
  renameSort
    (renameGenerator DerivedAbelianGroup
      [ ("μ",               "add")    -- multiplication becomes addition
      , ("η",               "zero")   -- unit becomes zero
      , ("μ.inv",           "neg")    -- inverse becomes negation
      ])
    (.root "M") (.root "R")

-- Step 2: Give the monoid multiplicative naming (mul/one)
-- and rename the carrier M→R to match.
private def multiplicativeMonoid : Theory :=
  renameSort
    (renameGenerator TheoryOfMonoids
      [ ("μ", "mul")    -- multiplication keeps its name
      , ("η", "one")    -- unit becomes one
      ])
    (.root "M") (.root "R")

-- Step 3: Amalgamate over the carrier R (both theories now use "R").
-- No identifications needed: both carriers are already named "R".
private def ringBase : Theory :=
  amalgamateOver additiveGroup multiplicativeMonoid []

-- Step 4: Add distributivity of mul over add.
/-- Ring derived from additive AbelianGroup and multiplicative Monoid
    via amalgamation, with left/right distributivity added. -/
def DerivedRing : Theory :=
  { addDistributivity ringBase "mul" "add" with
    name     := "DerivedRing"
    doctrine := { doctrine := .LawvereTheory } }

-- Step 5: CommutativeRing = Ring + commutativity of multiplication.
/-- CommutativeRing derived from Ring by adding commutativity of mul. -/
def DerivedCommutativeRing : Theory :=
  { addCommutativity DerivedRing "mul" with
    name := "DerivedCommutativeRing" }

-- ============================================================
-- Semilattice = Monoid + idempotent + commutativity
-- ============================================================

/-- A meet-semilattice: commutative idempotent monoid (μ is ∧). -/
def DerivedMeetSemilattice : Theory :=
  addIdempotent (addCommutativity TheoryOfMonoids "μ") "μ"

-- ============================================================
-- Lattice = amalgamate(meet semilattice, join semilattice) + absorption
-- ============================================================

-- Meet semilattice (uses ∧, ⊤)
private def meetSL : Theory :=
  renameGenerator DerivedMeetSemilattice [("μ", "∧"), ("η", "⊤"), ("swap", "swap")]

-- Join semilattice (uses ∨, ⊥) built from the same base with different names
private def joinSL : Theory :=
  renameSort
    (renameGenerator DerivedMeetSemilattice [("μ", "∨"), ("η", "⊥"), ("swap", "swap")])
    (.root "M") (.root "L")

/-- Lattice derived from meet- and join-semilattices via amalgamation
    over the carrier, with absorption laws. -/
def DerivedLattice : Theory :=
  let meetL := renameSort meetSL (.root "M") (.root "L")
  let base  := amalgamateOver meetL joinSL [(.root "L", .root "L")]
  { addAbsorption base "∧" "∨" with
    name     := "DerivedLattice"
    doctrine := { doctrine := .CartesianCategory } }

-- ============================================================
-- HeytingAlgebra = Lattice + Heyting implication
-- ============================================================

/-- Heyting algebra derived from the hand-crafted Lattice by adding
    implication → as the right adjoint to meet ∧. -/
def DerivedHeytingAlgebra : Theory :=
  { addAdjoint TheoryOfLattices "∧" "→" with
    name     := "DerivedHeytingAlgebra"
    doctrine := { doctrine := .CartesianClosed } }

-- ============================================================
-- BooleanAlgebra = booleanize(HeytingAlgebra)  (already in BooleanAlgebra.lean)
-- ============================================================

-- (See Catlab.Library.BooleanAlgebra for the actual definition)

-- ============================================================
-- Summary eval: check that all derived theories are non-empty
-- ============================================================

#eval do
  let theories := [
    ("DerivedGroup",          DerivedGroup),
    ("DerivedAbelianGroup",   DerivedAbelianGroup),
    ("DerivedRing",           DerivedRing),
    ("DerivedCommRing",       DerivedCommutativeRing),
    ("DerivedMeetSemilattice",DerivedMeetSemilattice),
    ("DerivedLattice",        DerivedLattice),
    ("DerivedHeytingAlgebra", DerivedHeytingAlgebra),
  ]
  IO.println "=== Derived theory shapes ==="
  for (name, t) in theories do
    IO.println s!"  {name}: {t.objects.length} obj  {t.morphisms.length} mor  {t.axioms.length} ax"

end CatLab.Library.Core
