/-
  CatLab — Functoriality Tests

  Verifies that `opposite` and `mirror` behave as functors with respect to
  binary combinators (product, coproduct, tensor).  All checks use
  `signatureMatch` (same object/morphism/axiom counts) plus `validate`.
-/

import Catlab.Tests.TestCore
import Catlab.Core.Validate
import Catlab.Core.Equality
import Catlab.Operators.Opposite
import Catlab.Operators.Mirror
import Catlab.Operators.Product
import Catlab.Operators.Coproduct
import Catlab.Operators.DayConvolution

namespace CatLab.Tests.Functorial

open CatLab CatLab.Tests CatLab.Library

/-- Representative pairs of library theories for binary combinator tests. -/
private def testPairs : List (String × Theory × String × Theory) :=
  [ ("Monoid",   TheoryOfMonoids,     "Group",   TheoryOfGroups)
  , ("Category", TheoryOfCategories,  "Poset",   TheoryOfPosets)
  , ("Monoid",   TheoryOfMonoids,     "Monoid",  TheoryOfMonoids)
  , ("Ring",     TheoryOfRings,       "Lattice", TheoryOfLattices)
  , ("Group",    TheoryOfGroups,      "Poset",   TheoryOfPosets)
  ]

-- ============================================================
-- 1. opposite commutes with product (on signature)
-- ============================================================

#eval do
  IO.println "\n=== functorial: opposite commutes with product ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := opposite (productCategory a b)
    let rhs := productCategory (opposite a) (opposite b)
    check s!"op(prod({nA},{nB})) ≅ prod(op({nA}),op({nB}))" (lhs.signatureMatch rhs)

-- ============================================================
-- 2. opposite commutes with coproduct (on signature)
-- ============================================================

#eval do
  IO.println "\n=== functorial: opposite commutes with coproduct ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := opposite (coproductCategory a b)
    let rhs := coproductCategory (opposite a) (opposite b)
    check s!"op(coprod({nA},{nB})) ≅ coprod(op({nA}),op({nB}))" (lhs.signatureMatch rhs)

-- ============================================================
-- 3. mirror commutes with tensor (on signature)
-- ============================================================

#eval do
  IO.println "\n=== functorial: mirror commutes with tensor ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := mirror (tensorTheories a b)
    let rhs := tensorTheories (mirror a) (mirror b)
    check s!"mir(tensor({nA},{nB})) ≅ tensor(mir({nA}),mir({nB}))" (lhs.signatureMatch rhs)

-- ============================================================
-- 4. opposite commutes with tensor (on signature)
-- ============================================================

#eval do
  IO.println "\n=== functorial: opposite commutes with tensor ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := opposite (tensorTheories a b)
    let rhs := tensorTheories (opposite a) (opposite b)
    check s!"op(tensor({nA},{nB})) ≅ tensor(op({nA}),op({nB}))" (lhs.signatureMatch rhs)

-- ============================================================
-- 5. mirror swaps product and coproduct (on signature)
-- ============================================================

#eval do
  IO.println "\n=== functorial: mirror swaps product ↔ coproduct ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := mirror (productCategory a b)
    let rhs := coproductCategory (mirror a) (mirror b)
    check s!"mir(prod({nA},{nB})) ≅ coprod(mir({nA}),mir({nB}))" (lhs.signatureMatch rhs)
    let lhs2 := mirror (coproductCategory a b)
    let rhs2 := productCategory (mirror a) (mirror b)
    check s!"mir(coprod({nA},{nB})) ≅ prod(mir({nA}),mir({nB}))" (lhs2.signatureMatch rhs2)

-- ============================================================
-- 6. All composed results validate
-- ============================================================

#eval do
  IO.println "\n=== functorial: validate all composed results ==="
  let mut failures : Nat := 0
  for (nA, a, nB, b) in testPairs do
    let results : List (String × Theory) :=
      [ (s!"op(prod({nA},{nB}))",            opposite (productCategory a b))
      , (s!"prod(op({nA}),op({nB}))",        productCategory (opposite a) (opposite b))
      , (s!"op(coprod({nA},{nB}))",           opposite (coproductCategory a b))
      , (s!"coprod(op({nA}),op({nB}))",       coproductCategory (opposite a) (opposite b))
      , (s!"mir(tensor({nA},{nB}))",          mirror (tensorTheories a b))
      , (s!"tensor(mir({nA}),mir({nB}))",     tensorTheories (mirror a) (mirror b))
      , (s!"op(tensor({nA},{nB}))",           opposite (tensorTheories a b))
      , (s!"tensor(op({nA}),op({nB}))",       tensorTheories (opposite a) (opposite b))
      , (s!"mir(prod({nA},{nB}))",            mirror (productCategory a b))
      , (s!"coprod(mir({nA}),mir({nB}))",     coproductCategory (mirror a) (mirror b))
      , (s!"mir(coprod({nA},{nB}))",          mirror (coproductCategory a b))
      , (s!"prod(mir({nA}),mir({nB}))",       productCategory (mirror a) (mirror b))
      ]
    for (label, t) in results do
      let errs := CatLab.validate t
      if errs.isEmpty then
        IO.println s!"[PASS] validate {label}"
      else
        failures := failures + 1
        IO.println s!"[FAIL] validate {label}: {errs.length} errors"
        for e in errs do IO.println s!"  - {e}"
  if failures > 0 then
    throw (IO.userError s!"{failures} composed theories failed validation")

-- ============================================================
-- 7. opposite preserves morphism count
-- ============================================================

#eval do
  IO.println "\n=== functorial: opposite preserves morphism count ==="
  for (name, t) in allLibTheories do
    let ot := opposite t
    assertEq s!"op({name}).morphisms.length" ot.morphisms.length t.morphisms.length

-- ============================================================
-- 8. mirror preserves object count
-- ============================================================

#eval do
  IO.println "\n=== functorial: mirror preserves object count ==="
  for (name, t) in allLibTheories do
    let mt := mirror t
    assertEq s!"mir({name}).objects.length" mt.objects.length t.objects.length

-- ============================================================
-- 9. product is commutative on signature
-- ============================================================

#eval do
  IO.println "\n=== functorial: product commutativity ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := productCategory a b
    let rhs := productCategory b a
    check s!"prod({nA},{nB}) ≅ prod({nB},{nA})" (lhs.signatureMatch rhs)

-- ============================================================
-- 10. coproduct is commutative on signature
-- ============================================================

#eval do
  IO.println "\n=== functorial: coproduct commutativity ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := coproductCategory a b
    let rhs := coproductCategory b a
    check s!"coprod({nA},{nB}) ≅ coprod({nB},{nA})" (lhs.signatureMatch rhs)

-- ============================================================
-- 11. tensor is commutative on signature
-- ============================================================

#eval do
  IO.println "\n=== functorial: tensor commutativity ==="
  for (nA, a, nB, b) in testPairs do
    let lhs := tensorTheories a b
    let rhs := tensorTheories b a
    check s!"tensor({nA},{nB}) ≅ tensor({nB},{nA})" (lhs.signatureMatch rhs)

end CatLab.Tests.Functorial
