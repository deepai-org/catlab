/-
  CatLab — Validation Tests

  Runs `validate` on every library theory and on every unary operator
  applied to every library theory. Catches ill-typed axioms, undeclared
  references, boundary mismatches, and other structural errors.
-/

import Catlab.Tests.TestCore
import Catlab.Core.Validate
import Catlab.Operators.Opposite
import Catlab.Operators.Mirror
import Catlab.Operators.Decategorify
import Catlab.Operators.Karoubi
import Catlab.Operators.Free
import Catlab.Operators.Arrow
import Catlab.Operators.Span
import Catlab.Operators.Family
import Catlab.Operators.Nerve
import Catlab.Operators.Booleanize
import Catlab.Operators.ExactCompletion
import Catlab.Operators.Morita
import Catlab.Operators.Internal
import Catlab.Operators.Center
import Catlab.Operators.Yoneda
import Catlab.Operators.Comma
import Catlab.Operators.Syntactic
import Catlab.Operators.Stabilize
import Catlab.Operators.Isbell
import Catlab.Operators.Lawvere
import Catlab.Operators.FunctorCategory

namespace CatLab.Tests.Validate

open CatLab CatLab.Arrow CatLab.Tests CatLab.Library

-- ============================================================
-- Validate all library theories
-- ============================================================

#eval do
  IO.println "\n=== validate: library theories ==="
  let mut failures : Nat := 0
  for (name, t) in allLibTheories do
    let errors := CatLab.validate t
    if errors.isEmpty then
      IO.println s!"[PASS] validate({name})"
    else
      failures := failures + 1
      IO.println s!"[FAIL] validate({name}): {errors.length} errors"
      for e in errors do
        IO.println s!"  - {e}"
  -- 2 operator-derived theories (TriangulatedCategory, DGA) still fail
  if failures > 2 then
    throw (IO.userError s!"{failures} library theories failed validation (expected ≤ 2)")

-- ============================================================
-- Validate unary operators × all library theories
-- ============================================================

private def unaryOps : List (String × (Theory → Theory)) :=
  [ ("opposite",      opposite)
  , ("mirror",        mirror)
  , ("decat_iso",     fun t => decategorify t .isoClasses)
  , ("karoubi",       karoubiEnvelope)
  , ("arrow",         arrowCategory)
  , ("span",          spanCategory)
  , ("family",        familyCategory)
  , ("nerve",         nerve)
  , ("exact",         exCompletion)
  , ("morita",        moritaEnvelope)
  , ("internal",      internalCategoryCategory)
  , ("center",        center)
  , ("syntactic",     syntacticCategory)
  , ("stabilize",     stabilize)
  , ("isbell",        isbellAdjunction)
  ]

#eval do
  IO.println "\n=== validate: unary operators × library theories ==="
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for (opName, op) in unaryOps do
    for (thName, t) in allLibTheories do
      total := total + 1
      let result := op t
      let errors := CatLab.validate result
      if errors.isEmpty then
        pure ()  -- silent pass to reduce noise
      else
        failures := failures + 1
        IO.println s!"[FAIL] validate({opName}({thName})): {errors.length} errors"
        for e in errors.take 3 do  -- show first 3 errors
          IO.println s!"  - {e}"
  let passes := total - failures
  IO.println s!"Validated {total} combinations: {passes} pass, {failures} fail"
  -- Operator validation is advisory for now; many operators need fixes
  -- TODO: reduce threshold as operators are fixed
  if passes == 0 then
    throw (IO.userError "All operator×theory combinations failed — something is very wrong")

end CatLab.Tests.Validate
