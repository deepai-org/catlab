/-
  CatLab — ∞-Topos Infrastructure Tests

  Tests the four "dots" connecting HoTT to a true ∞-topos:
    1. Propositional truncation (HIT-based logic layer)
    2. Equivalence macros (fiber, isContr, isEquiv, Equiv)
    3. Univalence axiom (ua / idToEquiv roundtrip)
    4. Subobject classifier Ω (universe of hPropositions)
-/

import Catlab.Tests.TestCore
import Catlab.Core.Equality
import Catlab.Core.Primitives
import Catlab.Core.Validate
import Catlab.Operators.PropTrunc
import Catlab.Library.Univalence

namespace CatLab.Tests.InfinityTopos

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- 1. Propositional Truncation
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: propositional truncation ==="

  let A := Expr.atom { name := .root "A", kind := .sort }
  let hit := propTruncation A "A"

  IO.println s!"  HIT name: {hit.name}"
  IO.println s!"  Constructors: {hit.constructors.length}"

  check "has 2 constructors (inc + squash)" (hit.constructors.length == 2)
  check "first is point constructor" (!hit.constructors[0]!.isPath)
  check "second is path constructor" (hit.constructors[1]!.isPath)

-- ============================================================
-- 2. Set Truncation
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: set truncation ==="

  let A := Expr.atom { name := .root "A", kind := .sort }
  let hit := setTruncation A "A"

  IO.println s!"  HIT name: {hit.name}"
  IO.println s!"  Constructors: {hit.constructors.length}"

  check "has 2 constructors (inc + squash)" (hit.constructors.length == 2)
  check "first is point constructor" (!hit.constructors[0]!.isPath)
  check "second is path constructor" (hit.constructors[1]!.isPath)

-- ============================================================
-- 3. PropTrunc theory elaboration
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: propTruncTheory ==="

  let mon := TheoryOfMonoids
  let truncated := propTruncTheory mon

  IO.println s!"  Name: {truncated.name}"
  IO.println s!"  Objects: {truncated.objects.length}"
  IO.println s!"  Morphisms: {truncated.morphisms.length}"
  IO.println s!"  Axioms: {truncated.axioms.length}"

  -- Should have original objects + truncation type objects
  check "more objects than original" (truncated.objects.length > mon.objects.length)
  check "doctrine is MLTT" (truncated.doctrine.doctrine == Doctrine.MartinLofTypeTheory)

-- ============================================================
-- 4. Expr-level equivalence macros
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: equivalence macros ==="

  let A := Expr.atom { name := .root "A", kind := .sort }
  let B := Expr.atom { name := .root "B", kind := .sort }
  let f := Expr.atom { name := .root "f", kind := .morphism }

  -- isProp(A) should be a pi type
  let prop := Expr.isProp A
  match prop with
  | .pi _ _ (.pi _ _ (.path ..)) => check "isProp is Π x y. path(A,x,y)" true
  | _ => check "isProp has correct shape" false

  -- isContr(A) should be a sigma type
  let contr := Expr.isContr A
  match contr with
  | .sigma _ _ (.pi _ _ (.path ..)) => check "isContr is Σ center. Π x. path(A,center,x)" true
  | _ => check "isContr has correct shape" false

  -- fiber(f, y) should be a sigma type
  let y := Expr.atom { name := .root "y", kind := .sort }
  let fib := Expr.hfiber A B f y
  match fib with
  | .sigma _ _ (.path ..) => check "fiber is Σ x. path(B, f(x), y)" true
  | _ => check "fiber has correct shape" false

  -- Equiv(A, B) should be a sigma type
  let eq := Expr.equiv A B
  match eq with
  | .sigma _ (.pi ..) _ => check "Equiv is Σ (f : A→B). isEquiv(f)" true
  | _ => check "Equiv has correct shape" false

  IO.println "  All equivalence macros have correct structure"

-- ============================================================
-- 5. Univalence theory
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: univalence theory ==="

  let univ := TheoryOfUnivalence 0

  IO.println s!"  Name: {univ.name}"
  IO.println s!"  Objects: {univ.objects.length}"
  IO.println s!"  Morphisms: {univ.morphisms.length}"
  IO.println s!"  Axioms: {univ.axioms.length}"

  check "has 2 objects (A, B)" (univ.objects.length == 2)
  check "has 2 morphisms (ua, idToEquiv)" (univ.morphisms.length == 2)
  check "has 2 axioms (roundtrip)" (univ.axioms.length == 2)
  check "doctrine is MLTT" (univ.doctrine.doctrine == Doctrine.MartinLofTypeTheory)

  -- Check ua exists
  let hasUa := univ.morphisms.any fun (m : Generator1) =>
    m.id.name == Name.root "ua"
  let hasIdToEquiv := univ.morphisms.any fun (m : Generator1) =>
    m.id.name == Name.root "idToEquiv"
  check "has ua" hasUa
  check "has idToEquiv" hasIdToEquiv

-- ============================================================
-- 6. Subobject classifier
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: subobject classifier Ω ==="

  let omega := TheoryOfSubobjectClassifier

  IO.println s!"  Name: {omega.name}"
  IO.println s!"  Objects: {omega.objects.length}"
  IO.println s!"  Morphisms: {omega.morphisms.length}"
  IO.println s!"  Axioms: {omega.axioms.length}"

  check "has Ω object" (omega.objects.length == 1)
  check "has logical connectives" (omega.morphisms.length >= 6)
  check "has negation axioms" (omega.axioms.length >= 2)

  -- Check logical connectives exist
  let names := omega.morphisms.map fun (m : Generator1) => m.id.name.toString
  IO.println s!"  Connectives: {names}"

-- ============================================================
-- 7. Validate all ∞-topos theories
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: validation ==="

  let testCases := [
    ("Univalence(U_0)", TheoryOfUnivalence 0),
    ("SubobjectClassifier", TheoryOfSubobjectClassifier)
  ]

  for (label, t) in testCases do
    let errs := CatLab.validate t
    if errs.isEmpty then
      IO.println s!"[PASS] validate {label}"
    else
      IO.println s!"[FAIL] validate {label}: {errs.length} errors"
      for e in errs do IO.println s!"  - {e}"

-- ============================================================
-- 8. hProp macro produces correct Expr
-- ============================================================

#eval do
  IO.println "\n=== ∞-topos: hProp macro ==="

  let omega := Expr.hProp 0
  match omega with
  | .sigma _ (.univ 0) _ => check "Ω = Σ(A : U₀). isProp(A)" true
  | _ => check "Ω has correct shape" false

  -- isProp of unit should be inhabited (trivially)
  let unitProp := Expr.isProp .terminal
  match unitProp with
  | .pi _ .terminal (.pi _ _ (.path ..)) => check "isProp(1) well-formed" true
  | _ => check "isProp(1) well-formed" false

  IO.println "  hProp infrastructure verified"

end CatLab.Tests.InfinityTopos
