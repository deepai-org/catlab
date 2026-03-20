/-
  CatLab — Negative / Adversarial Validation Tests

  Tests that INVALID theories are correctly rejected by `validate`.
  Complements Test_Validate.lean which only checks that valid theories pass.
-/

import Catlab.Tests.TestCore
import Catlab.Core.Validate
import Catlab.Operators.Opposite

namespace CatLab.Tests.Negative

open CatLab CatLab.Tests

-- ============================================================
-- Helpers
-- ============================================================

/-- Assert that validate returns at least one error. -/
def assertInvalid (label : String) (t : Theory) : IO Unit := do
  let errors := CatLab.validate t
  if errors.isEmpty then
    throw (IO.userError s!"[FAIL] {label}: expected validation errors but got none")
  else
    IO.println s!"[PASS] {label}: got {errors.length} error(s) as expected"

/-- Assert that validate returns no errors. -/
def assertValid (label : String) (t : Theory) : IO Unit := do
  let errors := CatLab.validate t
  if !errors.isEmpty then
    throw (IO.userError s!"[FAIL] {label}: expected valid but got {errors.length} errors")
  else
    IO.println s!"[PASS] {label}: validates correctly"

/-- Assert that at least one error matches a predicate. -/
def assertHasError (label : String) (t : Theory) (pred : ValidationError → Bool) : IO Unit := do
  let errors := CatLab.validate t
  if errors.any pred then
    IO.println s!"[PASS] {label}: found expected error type"
  else
    throw (IO.userError s!"[FAIL] {label}: expected error not found among {errors.length} errors")

/-- Shorthand for building a minimal theory. -/
def mkTheory (name : String) (d : Doctrine) (objs : List Generator0)
    (morphs : List Generator1 := []) (axs : List Generator2 := []) : Theory :=
  { name := name
    doctrine := { doctrine := d }
    objects := objs
    morphisms := morphs
    axioms := axs }

/-- Shorthand for a simple object generator. -/
def obj (name : String) : Generator0 :=
  { id := gid name }

/-- Shorthand for a simple morphism generator. -/
def mor (name : String) (dom cod : String) : Generator1 :=
  { id := gid name (k := .morphism)
    domain := .atom (gid dom)
    codomain := .atom (gid cod) }

/-- Shorthand for a simple axiom with two atom paths. -/
def ax (name : String) (lhs rhs : Expr) : Generator2 :=
  { id := gid name (k := .twoCell)
    leftPath := lhs
    rightPath := rhs }

-- ============================================================
-- 1. Duplicate names are caught
-- ============================================================

#eval do
  IO.println "\n=== negative: duplicate names ==="

  -- Two objects with same name
  let t := mkTheory "DupObjs" .Category [obj "X", obj "X"]
  assertHasError "duplicate objects" t fun
    | .duplicateName _ => true
    | _ => false

  -- Object and morphism sharing a name
  let t := mkTheory "DupObjMor" .Category
    [obj "f", obj "Y"]
    [mor "f" "f" "Y"]
  assertHasError "object-morphism name collision" t fun
    | .duplicateName _ => true
    | _ => false

  -- Three duplicates
  let t := mkTheory "TripleDup" .Category [obj "A", obj "A", obj "A"]
  let errors := CatLab.validate t
  let dupCount := errors.filter fun (e : ValidationError) =>
    match e with | .duplicateName _ => true | _ => false
  check "triple dup produces >=2 duplicate errors" (dupCount.length >= 2)

-- ============================================================
-- 2. Undeclared references are caught
-- ============================================================

#eval do
  IO.println "\n=== negative: undeclared references ==="

  -- Morphism domain references non-existent object
  let t := mkTheory "BadDom" .Category
    [obj "Y"]
    [mor "f" "X" "Y"]
  assertHasError "undeclared domain object" t fun
    | .undeclaredObject _ _ => true
    | _ => false

  -- Morphism codomain references non-existent object
  let t := mkTheory "BadCod" .Category
    [obj "X"]
    [mor "f" "X" "Z"]
  assertHasError "undeclared codomain object" t fun
    | .undeclaredObject _ _ => true
    | _ => false

  -- Axiom references non-existent morphism
  let t := mkTheory "BadAxiomRef" .Category
    [obj "X", obj "Y"]
    [mor "f" "X" "Y"]
    [ax "eq1" (.atom (gid "f" (k := .morphism))) (.atom (gid "g" (k := .morphism)))]
  assertHasError "undeclared morphism in axiom" t fun
    | .undeclaredMorphism _ _ => true
    | _ => false

  -- Both domain and codomain undeclared
  let t := mkTheory "BothBad" .Category
    []
    [mor "f" "A" "B"]
  let errors := CatLab.validate t
  let objErrors := errors.filter fun (e : ValidationError) =>
    match e with | .undeclaredObject _ _ => true | _ => false
  check "both dom/cod undeclared => >=2 errors" (objErrors.length >= 2)

-- ============================================================
-- 3. Doctrine violations are caught
-- ============================================================

#eval do
  IO.println "\n=== negative: doctrine violations ==="

  -- LawvereTheory with no objects
  let t := mkTheory "EmptyLawvere" .LawvereTheory []
  assertHasError "Lawvere with no objects" t fun
    | .doctrineViolation _ => true
    | _ => false

  -- Topos without omega
  let t := mkTheory "NoOmegaTopos" .Topos [obj "X", obj "Y"]
  assertHasError "Topos without Ω" t fun
    | .doctrineViolation _ => true
    | _ => false

  -- Topos WITH omega should not trigger doctrine error
  let tGood := mkTheory "GoodTopos" .Topos
    [{ id := gid "Ω" }, obj "X"]
  let errors := CatLab.validate tGood
  let docErrors := errors.filter fun (e : ValidationError) =>
    match e with | .doctrineViolation _ => true | _ => false
  check "Topos with Ω has no doctrine violation" (docErrors.isEmpty)

-- ============================================================
-- 4. Boundary mismatches
-- ============================================================

#eval do
  IO.println "\n=== negative: boundary mismatches ==="

  -- comp(f, g) where cod(f) != dom(g)
  -- f : X -> Y, g : Z -> W, axiom says comp(f, g) = something
  let t := mkTheory "BadComp" .Category
    [obj "X", obj "Y", obj "Z", obj "W"]
    [mor "f" "X" "Y", mor "g" "Z" "W", mor "h" "X" "W"]
    [ax "badcomp"
      (.comp (.atom (gid "f" (k := .morphism))) (.atom (gid "g" (k := .morphism))))
      (.atom (gid "h" (k := .morphism)))]
  assertHasError "boundary mismatch in composition" t fun
    | .boundaryMismatch _ _ _ => true
    | _ => false

  -- Valid composition should not trigger boundary error
  let tOk := mkTheory "GoodComp" .Category
    [obj "X", obj "Y", obj "Z"]
    [mor "f" "X" "Y", mor "g" "Y" "Z", mor "h" "X" "Z"]
    [ax "goodcomp"
      (.comp (.atom (gid "f" (k := .morphism))) (.atom (gid "g" (k := .morphism))))
      (.atom (gid "h" (k := .morphism)))]
  let errors := CatLab.validate tOk
  let bndErrors := errors.filter fun (e : ValidationError) =>
    match e with | .boundaryMismatch _ _ _ => true | _ => false
  check "valid composition has no boundary error" (bndErrors.isEmpty)

-- ============================================================
-- 5. Operators don't fix broken input
-- ============================================================

#eval do
  IO.println "\n=== negative: operators propagate errors ==="

  -- Broken theory with undeclared reference
  let broken := mkTheory "Broken" .Category
    [obj "X"]
    [mor "f" "X" "GHOST"]

  -- opposite of broken should still have errors
  let opp := opposite broken
  assertInvalid "opposite(broken) still invalid" opp

  -- Specifically should still have undeclared reference
  assertHasError "opposite(broken) has undeclared ref" opp fun
    | .undeclaredObject _ _ => true
    | _ => false

-- ============================================================
-- 6. Empty/degenerate theories
-- ============================================================

#eval do
  IO.println "\n=== negative: empty and degenerate theories ==="

  -- Completely empty Category theory should validate cleanly
  let empty := mkTheory "Empty" .Category [] [] []
  assertValid "empty Category theory" empty

  -- Theory with only objects, no morphisms
  let objOnly := mkTheory "ObjOnly" .Category [obj "X", obj "Y"]
  assertValid "objects-only theory" objOnly

  -- Theory with only morphisms but no objects => undeclared errors
  let morOnly := mkTheory "MorOnly" .Category []
    [mor "f" "X" "Y"]
  assertInvalid "morphisms without objects" morOnly

-- ============================================================
-- 7. Multiple error categories simultaneously
-- ============================================================

#eval do
  IO.println "\n=== negative: multiple simultaneous errors ==="

  -- Theory with duplicates AND undeclared refs AND doctrine violation
  let chaos := mkTheory "Chaos" .LawvereTheory
    []  -- no objects => doctrine violation
    [mor "f" "A" "B"]  -- undeclared refs
  let errors := CatLab.validate chaos
  let hasDoctrine := errors.any fun | .doctrineViolation _ => true | _ => false
  let hasUndeclared := errors.any fun | .undeclaredObject _ _ => true | _ => false
  check "chaos: has doctrine error" hasDoctrine
  check "chaos: has undeclared error" hasUndeclared
  check "chaos: multiple error categories" (errors.length >= 2)

-- ============================================================
-- 8. Regression: self-referential morphism (X -> X) is valid
-- ============================================================

#eval do
  IO.println "\n=== negative: edge cases that SHOULD be valid ==="

  -- Endomorphism
  let t := mkTheory "Endo" .Category
    [obj "X"]
    [mor "f" "X" "X"]
  assertValid "endomorphism X -> X" t

  -- Identity-like axiom with self-composition
  let t := mkTheory "SelfComp" .Category
    [obj "X"]
    [mor "f" "X" "X"]
    [ax "idem"
      (.comp (.atom (gid "f" (k := .morphism))) (.atom (gid "f" (k := .morphism))))
      (.atom (gid "f" (k := .morphism)))]
  assertValid "self-composition axiom" t

end CatLab.Tests.Negative
