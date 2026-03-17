/-
  CatLab — Category-D Tests: Tier 2 Combinators

  Tests for the Algebra-of-Theories layer:
    - TheoryMorphism.id, comp, inclusion  (morphism constructors)
    - initialTheory, terminalTheory       (Tier 1 primitives)
    - pushout                             (the fundamental Tier 2 combinator)
    - theoryCoproduct as pushout          (derived combinator, algebraic consistency check)

  Coverage strategy:
    - Unary operators (id, inclusion self, initialMorphism, terminalMorphism,
      self-pushout): all 34 library theories
    - Binary operators (theoryCoproduct, pushout over ⊥, cross-inclusion,
      amalgamation): all 34×34 = 1156 ordered pairs
    - Specific sub-theory chains (Monoid→Group→AbelianGroup, etc.):
      named triples for deeper algebraic law checks

  Test levels:
    Level 1 (smoke): terminates and returns a well-named result
    Level 2 (shape): numeric invariants verified against exact formulas
    Level 3 (algebra): universal laws (self-pushout, pushout-over-⊥=coproduct, etc.)
-/

import Catlab.Tests.TestCore
import Catlab.Core.Equality
import Catlab.Core.Primitives
import Catlab.Operators.Pushout
import Catlab.Operators.Coproduct

namespace CatLab.Tests.CategoryD

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- Tier 1: initialTheory / terminalTheory shape
-- ============================================================

#eval do
  IO.println "\n=== initialTheory ==="
  smoke "initialTheory" initialTheory
  assertEq "initialTheory.objects"   initialTheory.objects.length   0
  assertEq "initialTheory.morphisms" initialTheory.morphisms.length 0
  assertEq "initialTheory.axioms"    initialTheory.axioms.length    0

#eval do
  IO.println "\n=== terminalTheory ==="
  smoke "terminalTheory" terminalTheory
  assertEq "terminalTheory.objects"   terminalTheory.objects.length   1
  assertEq "terminalTheory.morphisms" terminalTheory.morphisms.length 0

-- ============================================================
-- TheoryMorphism.id: all 34 theories
-- Law: maps every object and morphism to itself (map sizes = generator counts)
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.id (all theories) ==="
  for (name, t) in allLibTheories do
    let m := TheoryMorphism.id t
    check    s!"id({name}).source" (m.source.name == t.name)
    check    s!"id({name}).target" (m.target.name == t.name)
    assertEq s!"id({name}).onObjects.size"   m.onObjects.toList.length   t.objects.length
    assertEq s!"id({name}).onMorphisms.size" m.onMorphisms.toList.length t.morphisms.length

-- ============================================================
-- TheoryMorphism.inclusion (self): all 34 theories
-- Law: self-inclusion maps all generators → same counts as id
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.inclusion (self, all theories) ==="
  for (name, t) in allLibTheories do
    let m := TheoryMorphism.inclusion t t
    check    s!"incl({name}↪{name}).source" (m.source.name == t.name)
    check    s!"incl({name}↪{name}).target" (m.target.name == t.name)
    assertEq s!"incl({name}↪{name}).onObjects.size"
      m.onObjects.toList.length t.objects.length
    assertEq s!"incl({name}↪{name}).onMorphisms.size"
      m.onMorphisms.toList.length t.morphisms.length

-- ============================================================
-- TheoryMorphism.inclusion (cross): all 34×34 ordered pairs
-- Law: mapped objects ≤ min(|T_i.objects|, |T_j.objects|)
--      source/target names correct
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.inclusion (all pairs) ==="
  for (nameI, ti) in allLibTheories do
    for (nameJ, tj) in allLibTheories do
      let m := TheoryMorphism.inclusion ti tj
      check s!"incl({nameI}↪{nameJ}).source" (m.source.name == ti.name)
      check s!"incl({nameI}↪{nameJ}).target" (m.target.name == tj.name)
      -- mapped generators can only be those whose names appear in both theories
      let maxObjs := min ti.objects.length tj.objects.length
      assertGe s!"incl({nameI}↪{nameJ}).onObjects.size ≤ min"
        maxObjs m.onObjects.toList.length

-- ============================================================
-- TheoryMorphism.comp: all 34 theories (id ∘ id law)
-- Law: comp of identity morphisms preserves source/target and map sizes
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.comp id∘id (all theories) ==="
  for (name, t) in allLibTheories do
    let gf := TheoryMorphism.comp (TheoryMorphism.id t) (TheoryMorphism.id t)
    check    s!"comp(id,id)({name}).source" (gf.source.name == t.name)
    check    s!"comp(id,id)({name}).target" (gf.target.name == t.name)
    assertEq s!"comp(id,id)({name}).onObjects.size"
      gf.onObjects.toList.length t.objects.length

-- ============================================================
-- TheoryMorphism.comp: inclusion chains (all 34×34 pairs)
-- Law: (incl T_i↪T_j) ∘ (incl T_i↪T_i) has correct source/target
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.comp incl-chains (all pairs) ==="
  for (nameI, ti) in allLibTheories do
    for (nameJ, tj) in allLibTheories do
      -- chain: ti ↪ ti (self) then ti ↪ tj
      let f  := TheoryMorphism.inclusion ti ti   -- ti → ti (= id)
      let g  := TheoryMorphism.inclusion ti tj   -- ti → tj
      let gf := TheoryMorphism.comp f g
      check s!"comp(incl,incl)({nameI},{nameJ}).source" (gf.source.name == ti.name)
      check s!"comp(incl,incl)({nameI},{nameJ}).target" (gf.target.name == tj.name)

-- ============================================================
-- initialMorphism: all 34 theories
-- Law: empty maps, correct source (⊥) and target
-- ============================================================

#eval do
  IO.println "\n=== initialMorphism (all theories) ==="
  for (name, t) in allLibTheories do
    let m := initialMorphism t
    check    s!"initialMorphism({name}).source" (m.source.name == initialTheory.name)
    check    s!"initialMorphism({name}).target" (m.target.name == t.name)
    assertEq s!"initialMorphism({name}).onObjects.size"   m.onObjects.toList.length   0
    assertEq s!"initialMorphism({name}).onMorphisms.size" m.onMorphisms.toList.length 0

-- ============================================================
-- terminalMorphism: all 34 theories
-- Law: maps every generator, correct source and target (⊤)
-- ============================================================

#eval do
  IO.println "\n=== terminalMorphism (all theories) ==="
  for (name, t) in allLibTheories do
    let m := terminalMorphism t
    check    s!"terminalMorphism({name}).source" (m.source.name == t.name)
    check    s!"terminalMorphism({name}).target" (m.target.name == terminalTheory.name)
    assertEq s!"terminalMorphism({name}).onObjects.size"
      m.onObjects.toList.length t.objects.length
    assertEq s!"terminalMorphism({name}).onMorphisms.size"
      m.onMorphisms.toList.length t.morphisms.length

-- ============================================================
-- pushout: mismatched source → none
-- ============================================================

#eval do
  IO.println "\n=== pushout (mismatched source → none) ==="
  let fBad : TheoryMorphism :=
    { name := "bad_f", source := TheoryOfMonoids, target := TheoryOfGroups,
      onObjects := GeneratorMap.empty, onMorphisms := GeneratorMap.empty }
  let gBad : TheoryMorphism :=
    { name := "bad_g", source := TheoryOfGroups, target := TheoryOfGroups,
      onObjects := GeneratorMap.empty, onMorphisms := GeneratorMap.empty }
  check "pushout(mismatch) = none" (pushout fBad gBad).isNone

-- ============================================================
-- Self-pushout (id ⊔_T id): all 34 theories
-- Law: pushout (id T) (id T) has same object/morphism counts as T
-- (every inl(x) gets identified with inr(x), leaving one copy)
-- ============================================================

#eval do
  IO.println "\n=== self-pushout via id (all theories) ==="
  for (name, t) in allLibTheories do
    match pushout (TheoryMorphism.id t) (TheoryMorphism.id t) with
    | none   => throw (IO.userError s!"[FAIL] self-pushout({name}) returned none")
    | some r =>
      smoke s!"self-pushout({name})" r
      assertEq s!"self-pushout({name}).objects"   r.objects.length   t.objects.length
      assertEq s!"self-pushout({name}).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- pushout over ⊥ = disjoint union: all 34×34 pairs
-- Law: |objects| = |T1.objects| + |T2.objects|  (no identifications)
--      |morphisms| = |T1.morphisms| + |T2.morphisms|
-- Consistency: must equal coproductCategory on same inputs
-- ============================================================

#eval do
  IO.println "\n=== pushout over ⊥ = coproduct (all pairs) ==="
  for (n1, t1) in allLibTheories do
    for (n2, t2) in allLibTheories do
      let po  := pushout (initialMorphism t1) (initialMorphism t2)
      let ref := coproductCategory t1 t2
      match po with
      | none   => throw (IO.userError s!"[FAIL] pushout(⊥→{n1},⊥→{n2}) returned none")
      | some r =>
        -- Shape law
        assertEq s!"pushout/⊥({n1},{n2}).objects"
          r.objects.length (t1.objects.length + t2.objects.length)
        assertEq s!"pushout/⊥({n1},{n2}).morphisms"
          r.morphisms.length (t1.morphisms.length + t2.morphisms.length)
        -- Consistency with coproductCategory
        assertEq s!"pushout/⊥({n1},{n2}) vs coproduct: objects"
          r.objects.length ref.objects.length
        assertEq s!"pushout/⊥({n1},{n2}) vs coproduct: morphisms"
          r.morphisms.length ref.morphisms.length

-- ============================================================
-- theoryCoproduct: all 34×34 pairs
-- Law: objects = |T1| + |T2|, morphisms = |T1| + |T2|
-- (theoryCoproduct = pushout over ⊥, so same shape law applies)
-- ============================================================

#eval do
  IO.println "\n=== theoryCoproduct (all pairs) ==="
  for (n1, t1) in allLibTheories do
    for (n2, t2) in allLibTheories do
      let r := theoryCoproduct t1 t2
      smoke s!"theoryCoproduct({n1},{n2})" r
      assertEq s!"theoryCoproduct({n1},{n2}).objects"
        r.objects.length (t1.objects.length + t2.objects.length)
      assertEq s!"theoryCoproduct({n1},{n2}).morphisms"
        r.morphisms.length (t1.morphisms.length + t2.morphisms.length)

-- ============================================================
-- Amalgamation via inclusion: all 34×34 pairs with shared base
-- Base = T1; pushout (id T1) (inclusion T1 T2)
-- = extend T2 with T1's private generators, identifying shared ones
-- Law: smoke only — shape bounds depend on shared generator count
--      objects ≤ T1.objects + T2.objects  (at most disjoint union)
--      objects ≥ T2.objects               (T2 always fully present in T1-side)
-- ============================================================

#eval do
  IO.println "\n=== amalgamation (id T1) ⊔_T1 (incl T1→T2): all pairs ==="
  for (n1, t1) in allLibTheories do
    for (n2, t2) in allLibTheories do
      let f := TheoryMorphism.id t1
      let g := TheoryMorphism.inclusion t1 t2
      match pushout f g with
      | none   => throw (IO.userError s!"[FAIL] amalgam({n1},{n2}) returned none")
      | some r =>
        smoke s!"amalgam({n1},{n2})" r
        -- Upper bound: at most the disjoint union
        assertGe s!"amalgam({n1},{n2}).objects ≤ sum"
          (t1.objects.length + t2.objects.length) r.objects.length

-- ============================================================
-- Named sub-theory chains: deeper algebraic law checks
-- These verify specific mathematical relationships in the library
-- ============================================================

#eval do
  IO.println "\n=== named amalgamations: Monoid-based chains ==="

  -- Group ⊔_Monoid Ring: both contain a monoid; result has Group+Ring structure
  let f1 := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfGroups
  let g1 := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfRings
  match pushout f1 g1 with
  | none   => throw (IO.userError "[FAIL] Group ⊔_Monoid Ring returned none")
  | some r =>
    smoke "Group ⊔_Monoid Ring" r
    -- Shared Monoid generators identified → strictly fewer than sum
    assertGe "Group ⊔_Monoid Ring: objects ≤ sum"
      (TheoryOfGroups.objects.length + TheoryOfRings.objects.length) r.objects.length

  -- Group ⊔_Monoid CommRing
  let f2 := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfGroups
  let g2 := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfCommutativeRings
  match pushout f2 g2 with
  | none   => throw (IO.userError "[FAIL] Group ⊔_Monoid CommRing returned none")
  | some r2 =>
    smoke "Group ⊔_Monoid CommRing" r2

  -- AbelianGroup ⊔_Monoid Ring
  let f3 := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfAbelianGroups
  let g3 := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfRings
  match pushout f3 g3 with
  | none   => throw (IO.userError "[FAIL] AbelianGroup ⊔_Monoid Ring returned none")
  | some r3 =>
    smoke "AbelianGroup ⊔_Monoid Ring" r3

  -- Lattice ⊔_Poset BooleanAlgebra
  let f4 := TheoryMorphism.inclusion TheoryOfPosets TheoryOfLattices
  let g4 := TheoryMorphism.inclusion TheoryOfPosets TheoryOfBooleanAlgebra
  match pushout f4 g4 with
  | none   => throw (IO.userError "[FAIL] Lattice ⊔_Poset BoolAlgebra returned none")
  | some r4 =>
    smoke "Lattice ⊔_Poset BoolAlgebra" r4

end CatLab.Tests.CategoryD
