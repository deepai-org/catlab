/-
  CatLab — Test Infrastructure

  Shared helpers: assertions, the canonical theory list, and smoke-test runners.
-/

import Catlab.Core.Theory
import Catlab.Library.Monoid
import Catlab.Library.Group
import Catlab.Library.Ring
import Catlab.Library.BooleanAlgebra
import Catlab.Library.Poset
import Catlab.Library.Lattice
import Catlab.Library.Semiring
import Catlab.Library.Module
import Catlab.Library.Category

namespace CatLab.Tests

open CatLab.Library

-- ============================================================
-- Assertion helpers
-- ============================================================

/-- Base assertion: throws an IO error on failure so `lake build` fails in CI.
    The error message is displayed as a Lean diagnostic. -/
def check (msg : String) (cond : Bool) : IO Unit := do
  if cond then
    IO.println s!"[PASS] {msg}"
  else
    throw (IO.userError s!"[FAIL] {msg}")

/-- Equality assertion with formatted diff output. -/
def assertEq {α} [BEq α] [ToString α] (msg : String) (actual expected : α) : IO Unit := do
  if actual == expected then
    IO.println s!"[PASS] {msg}"
  else
    throw (IO.userError s!"[FAIL] {msg} — expected {expected}, got {actual}")

/-- Assert `actual >= expected`. -/
def assertGe (msg : String) (actual expected : Nat) : IO Unit :=
  check s!"{msg} (>= {expected}, got {actual})" (actual >= expected)

/-- Assert exact object/morphism/axiom counts of a theory. -/
def assertTheoryShape (msg : String) (t : Theory) (objs morphs axioms : Nat) : IO Unit := do
  assertEq s!"{msg}.objects" t.objects.length objs
  assertEq s!"{msg}.morphisms" t.morphisms.length morphs
  assertEq s!"{msg}.axioms" t.axioms.length axioms

/-- Smoke-test: operator terminates and returns a non-empty-named Theory. -/
def smoke (label : String) (t : Theory) : IO Unit :=
  check s!"smoke {label}" (!t.name.isEmpty)

-- ============================================================
-- Canonical library theory list
-- ============================================================

/-- All 12 library theories with display names.
    Used by category-A and category-B tests to iterate. -/
def allLibTheories : List (String × Theory) :=
  [ ("Monoid",         TheoryOfMonoids)
  , ("Group",          TheoryOfGroups)
  , ("AbelianGroup",   TheoryOfAbelianGroups)
  , ("Ring",           TheoryOfRings)
  , ("CommRing",       TheoryOfCommutativeRings)
  , ("Category",       TheoryOfCategories)
  , ("Poset",          TheoryOfPosets)
  , ("Lattice",        TheoryOfLattices)
  , ("BoolAlgebra",    TheoryOfBooleanAlgebra)
  , ("HeytingAlgebra", TheoryOfHeytingAlgebra)
  , ("Semiring",       TheoryOfSemirings)
  , ("Module",         TheoryOfModules "R")
  ]

end CatLab.Tests
