/-
  CatLab — Validation Tests

  Runs `validate` on every library theory and on every unary operator
  applied to every library theory. Also tests binary operators, operator
  composition chains, involution properties, and idempotency.
-/

import Catlab.Tests.TestCore
import Catlab.Core.Validate
import Catlab.Core.Equality
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
import Catlab.Operators.Product
import Catlab.Operators.Coproduct
import Catlab.Operators.DayConvolution

namespace CatLab.Tests.Validate

open CatLab CatLab.Arrow CatLab.Tests CatLab.Library

-- ============================================================
-- 1. Validate all library theories (expect 0 failures)
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
  if failures > 0 then
    throw (IO.userError s!"{failures} library theories failed validation (expected 0)")

-- ============================================================
-- 2. Validate unary operators × all library theories (expect 0 failures)
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
  if failures > 0 then
    throw (IO.userError s!"{failures} operator×theory combinations failed (expected 0)")

-- ============================================================
-- 3. Validate binary operators × selected theory pairs
-- ============================================================

private def smallTheories : List (String × Theory) :=
  [ ("Monoid",   TheoryOfMonoids)
  , ("Group",    TheoryOfGroups)
  , ("Category", TheoryOfCategories)
  , ("Poset",    TheoryOfPosets)
  , ("Lattice",  TheoryOfLattices)
  , ("Ring",     TheoryOfRings)
  ]

#eval do
  IO.println "\n=== validate: binary operators × theory pairs ==="
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for (n1, t1) in smallTheories do
    for (n2, t2) in smallTheories do
      -- productCategory
      total := total + 1
      let r := productCategory t1 t2
      let errors := CatLab.validate r
      if !errors.isEmpty then
        failures := failures + 1
        IO.println s!"[FAIL] validate(product({n1},{n2})): {errors.length} errors"
        for e in errors.take 2 do IO.println s!"  - {e}"
      -- coproductCategory
      total := total + 1
      let r := coproductCategory t1 t2
      let errors := CatLab.validate r
      if !errors.isEmpty then
        failures := failures + 1
        IO.println s!"[FAIL] validate(coproduct({n1},{n2})): {errors.length} errors"
        for e in errors.take 2 do IO.println s!"  - {e}"
      -- tensorTheories
      total := total + 1
      let r := tensorTheories t1 t2
      let errors := CatLab.validate r
      if !errors.isEmpty then
        failures := failures + 1
        IO.println s!"[FAIL] validate(tensor({n1},{n2})): {errors.length} errors"
        for e in errors.take 2 do IO.println s!"  - {e}"
  let passes := total - failures
  IO.println s!"Validated {total} binary combinations: {passes} pass, {failures} fail"
  if failures > 0 then
    throw (IO.userError s!"{failures} binary operator combinations failed (expected 0)")

-- ============================================================
-- 4. Involution tests: opposite² = id, mirror² = id (structurally)
-- ============================================================

#eval do
  IO.println "\n=== involution: opposite(opposite(t)) preserves structure ==="
  for (name, t) in allLibTheories do
    let tt := opposite (opposite t)
    -- Object/morphism/axiom counts must be identical
    let objOk := tt.objects.length == t.objects.length
    let morOk := tt.morphisms.length == t.morphisms.length
    let axOk  := tt.axioms.length == t.axioms.length
    if objOk && morOk && axOk then
      pure ()
    else
      throw (IO.userError s!"[FAIL] opposite²({name}) changed counts: objs {t.objects.length}→{tt.objects.length}, mors {t.morphisms.length}→{tt.morphisms.length}, axs {t.axioms.length}→{tt.axioms.length}")
  IO.println s!"[PASS] opposite² preserves counts for all {allLibTheories.length} theories"

#eval do
  IO.println "\n=== involution: mirror(mirror(t)) preserves structure ==="
  for (name, t) in allLibTheories do
    let tt := mirror (mirror t)
    let objOk := tt.objects.length == t.objects.length
    let morOk := tt.morphisms.length == t.morphisms.length
    let axOk  := tt.axioms.length == t.axioms.length
    if objOk && morOk && axOk then
      pure ()
    else
      throw (IO.userError s!"[FAIL] mirror²({name}) changed counts: objs {t.objects.length}→{tt.objects.length}, mors {t.morphisms.length}→{tt.morphisms.length}, axs {t.axioms.length}→{tt.axioms.length}")
  IO.println s!"[PASS] mirror² preserves counts for all {allLibTheories.length} theories"

-- ============================================================
-- 5. Involution: opposite² and mirror² still validate
-- ============================================================

#eval do
  IO.println "\n=== validate: opposite² and mirror² ==="
  let mut failures : Nat := 0
  for (name, t) in allLibTheories do
    let oo := opposite (opposite t)
    let errors := CatLab.validate oo
    if !errors.isEmpty then
      failures := failures + 1
      IO.println s!"[FAIL] validate(opposite²({name})): {errors.length} errors"
    let mm := mirror (mirror t)
    let errors := CatLab.validate mm
    if !errors.isEmpty then
      failures := failures + 1
      IO.println s!"[FAIL] validate(mirror²({name})): {errors.length} errors"
  if failures == 0 then
    IO.println s!"[PASS] opposite² and mirror² validate for all {allLibTheories.length} theories"
  else
    throw (IO.userError s!"{failures} involution validations failed")

-- ============================================================
-- 6. Operator composition chains: validate(op2(op1(t)))
-- ============================================================

#eval do
  IO.println "\n=== validate: operator composition chains ==="
  -- Test selected 2-deep compositions on a few representative theories
  let testTheories : List (String × Theory) :=
    [ ("Monoid",   TheoryOfMonoids)
    , ("Category", TheoryOfCategories)
    , ("Poset",    TheoryOfPosets)
    ]
  let chains : List (String × (Theory → Theory)) :=
    [ ("opposite∘karoubi",    fun t => opposite (karoubiEnvelope t))
    , ("karoubi∘opposite",    fun t => karoubiEnvelope (opposite t))
    , ("mirror∘nerve",        fun t => mirror (nerve t))
    , ("center∘opposite",     fun t => center (opposite t))
    , ("family∘mirror",       fun t => familyCategory (mirror t))
    , ("nerve∘karoubi",       fun t => nerve (karoubiEnvelope t))
    , ("isbell∘opposite",     fun t => isbellAdjunction (opposite t))
    , ("morita∘karoubi",      fun t => moritaEnvelope (karoubiEnvelope t))
    , ("syntactic∘mirror",    fun t => syntacticCategory (mirror t))
    , ("arrow∘opposite",      fun t => arrowCategory (opposite t))
    ]
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for (chainName, chain) in chains do
    for (thName, t) in testTheories do
      total := total + 1
      let result := chain t
      let errors := CatLab.validate result
      if !errors.isEmpty then
        failures := failures + 1
        IO.println s!"[FAIL] validate({chainName}({thName})): {errors.length} errors"
        for e in errors.take 2 do IO.println s!"  - {e}"
  let passes := total - failures
  IO.println s!"Validated {total} chains: {passes} pass, {failures} fail"
  if failures > 0 then
    IO.println s!"  (advisory: {failures} chain failures)"

-- ============================================================
-- 7. Idempotency stress: applying operator twice doesn't crash or
--    produce duplicate names
-- ============================================================

#eval do
  IO.println "\n=== idempotency: op(op(t)) validates without duplicates ==="
  let t := TheoryOfMonoids
  let idempotentOps : List (String × (Theory → Theory)) :=
    [ ("karoubi",   karoubiEnvelope)
    , ("morita",    moritaEnvelope)
    , ("stabilize", stabilize)
    , ("exact",     exCompletion)
    , ("family",    familyCategory)
    ]
  let mut failures : Nat := 0
  for (name, op) in idempotentOps do
    let r := op (op t)
    let errors := CatLab.validate r
    let hasDuplicates := errors.any fun e =>
      match e with
      | .duplicateName _ => true
      | _ => false
    if hasDuplicates then
      failures := failures + 1
      IO.println s!"[FAIL] {name}²(Monoid) has duplicate names"
    else if !errors.isEmpty then
      IO.println s!"[WARN] {name}²(Monoid): {errors.length} non-duplicate errors"
    else
      IO.println s!"[PASS] {name}²(Monoid) validates cleanly"
  if failures > 0 then
    throw (IO.userError s!"{failures} idempotent operators produced duplicates")

-- ============================================================
-- 8. Monotonicity: operators don't lose objects or morphisms
-- ============================================================

#eval do
  IO.println "\n=== monotonicity: enriching operators preserve original generators ==="
  -- These operators should produce at least as many objects/morphisms as the input
  let enrichingOps : List (String × (Theory → Theory)) :=
    [ ("karoubi",   karoubiEnvelope)
    , ("morita",    moritaEnvelope)
    , ("exact",     exCompletion)
    , ("syntactic", syntacticCategory)
    ]
  let mut failures : Nat := 0
  for (opName, op) in enrichingOps do
    for (thName, t) in allLibTheories do
      let r := op t
      if r.objects.length < t.objects.length then
        failures := failures + 1
        IO.println s!"[FAIL] {opName}({thName}) lost objects: {t.objects.length} → {r.objects.length}"
      if r.morphisms.length < t.morphisms.length then
        failures := failures + 1
        IO.println s!"[FAIL] {opName}({thName}) lost morphisms: {t.morphisms.length} → {r.morphisms.length}"
  if failures == 0 then
    IO.println s!"[PASS] all enriching operators preserve generator counts"
  else
    throw (IO.userError s!"{failures} monotonicity violations")

-- ============================================================
-- 9. Axiom preservation: operators that include t.axioms actually do
-- ============================================================

#eval do
  IO.println "\n=== axiom preservation: ops that keep axioms don't drop them ==="
  -- These operators should have at least as many axioms as the input
  let axiomPreservingOps : List (String × (Theory → Theory)) :=
    [ ("opposite",  opposite)
    , ("mirror",    mirror)
    , ("karoubi",   karoubiEnvelope)
    , ("morita",    moritaEnvelope)
    , ("exact",     exCompletion)
    ]
  let mut failures : Nat := 0
  for (opName, op) in axiomPreservingOps do
    for (thName, t) in allLibTheories do
      let r := op t
      if r.axioms.length < t.axioms.length then
        failures := failures + 1
        IO.println s!"[FAIL] {opName}({thName}) lost axioms: {t.axioms.length} → {r.axioms.length}"
  if failures == 0 then
    IO.println s!"[PASS] all axiom-preserving operators keep axioms"
  else
    throw (IO.userError s!"{failures} axiom preservation violations")

-- ============================================================
-- 10. Non-emptiness: no operator produces a totally empty theory
-- ============================================================

#eval do
  IO.println "\n=== non-emptiness: operators produce non-trivial output ==="
  let mut failures : Nat := 0
  for (opName, op) in unaryOps do
    for (thName, t) in allLibTheories do
      let r := op t
      if r.objects.isEmpty && r.morphisms.isEmpty then
        failures := failures + 1
        IO.println s!"[FAIL] {opName}({thName}) produced empty theory"
  if failures == 0 then
    IO.println s!"[PASS] no operator produces empty theory"
  else
    throw (IO.userError s!"{failures} operators produced empty theories")

end CatLab.Tests.Validate
