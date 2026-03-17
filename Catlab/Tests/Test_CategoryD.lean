/-
  CatLab — Category-D Tests: Tier 2 Combinators

  Tests for the Algebra-of-Theories layer:
    - TheoryMorphism.id, comp, inclusion  (morphism constructors)
    - initialTheory, terminalTheory       (Tier 1 primitives)
    - pushout                             (the fundamental Tier 2 combinator)
    - theoryCoproduct as pushout          (derived combinator, algebraic consistency check)

  Test levels:
    Level 1 (smoke): terminates and returns a well-named result
    Level 2 (shape): numeric invariants on objects/morphisms/axioms
    Level 3 (algebra): algebraic laws (self-pushout, pushout-over-⊥ = coproduct, etc.)
-/

import Catlab.Tests.TestCore
import Catlab.Core.Equality
import Catlab.Core.Primitives
import Catlab.Operators.Pushout
import Catlab.Operators.Coproduct

namespace CatLab.Tests.CategoryD

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- Tier 1: initialTheory / terminalTheory
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
-- TheoryMorphism.id: identity maps every generator to itself
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.id ==="
  for (name, t) in allLibTheories do
    let m := TheoryMorphism.id t
    check   s!"id({name}).source" (m.source.name == t.name)
    check   s!"id({name}).target" (m.target.name == t.name)
    assertEq s!"id({name}).onObjects.size"   m.onObjects.toList.length   t.objects.length
    assertEq s!"id({name}).onMorphisms.size" m.onMorphisms.toList.length t.morphisms.length

-- ============================================================
-- TheoryMorphism.inclusion: sub ↪ super maps by matching names
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.inclusion (self) ==="
  -- inclusion t t should map every generator (same as id)
  for (name, t) in allLibTheories do
    let m := TheoryMorphism.inclusion t t
    check s!"inclusion({name},{name}).source" (m.source.name == t.name)
    check s!"inclusion({name},{name}).target" (m.target.name == t.name)
    assertEq s!"inclusion({name},{name}).onObjects.size"
      m.onObjects.toList.length t.objects.length
    assertEq s!"inclusion({name},{name}).onMorphisms.size"
      m.onMorphisms.toList.length t.morphisms.length

#eval do
  IO.println "\n=== TheoryMorphism.inclusion (Monoid ↪ Group) ==="
  -- Every Monoid generator should appear in Group
  let m := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfGroups
  check "inclusion(Monoid,Group).source" (m.source.name == TheoryOfMonoids.name)
  check "inclusion(Monoid,Group).target" (m.target.name == TheoryOfGroups.name)
  -- Monoid objects ⊆ Group objects (by name), so all Monoid objects should be mapped
  assertEq "inclusion(Monoid,Group).onObjects.size"
    m.onObjects.toList.length TheoryOfMonoids.objects.length

-- ============================================================
-- TheoryMorphism.comp: g ∘ f has correct source/target
-- ============================================================

#eval do
  IO.println "\n=== TheoryMorphism.comp ==="
  for (name, t) in allLibTheories do
    let f := TheoryMorphism.id t
    let g := TheoryMorphism.id t
    let gf := TheoryMorphism.comp f g
    check s!"comp(id,id)({name}).source" (gf.source.name == t.name)
    check s!"comp(id,id)({name}).target" (gf.target.name == t.name)
    -- Composed map has the same domain size as the source
    assertEq s!"comp(id,id)({name}).onObjects.size"
      gf.onObjects.toList.length t.objects.length

-- ============================================================
-- initialMorphism / terminalMorphism: structure checks
-- ============================================================

#eval do
  IO.println "\n=== initialMorphism ==="
  for (name, t) in allLibTheories do
    let m := initialMorphism t
    check s!"initialMorphism({name}).source" (m.source.name == initialTheory.name)
    check s!"initialMorphism({name}).target" (m.target.name == t.name)
    assertEq s!"initialMorphism({name}).onObjects.size"   m.onObjects.toList.length   0
    assertEq s!"initialMorphism({name}).onMorphisms.size" m.onMorphisms.toList.length 0

#eval do
  IO.println "\n=== terminalMorphism ==="
  for (name, t) in allLibTheories do
    let m := terminalMorphism t
    check s!"terminalMorphism({name}).source" (m.source.name == t.name)
    check s!"terminalMorphism({name}).target" (m.target.name == terminalTheory.name)
    -- Every object and morphism in t must be mapped
    assertEq s!"terminalMorphism({name}).onObjects.size"
      m.onObjects.toList.length t.objects.length
    assertEq s!"terminalMorphism({name}).onMorphisms.size"
      m.onMorphisms.toList.length t.morphisms.length

-- ============================================================
-- pushout: None on mismatched sources
-- ============================================================

#eval do
  IO.println "\n=== pushout (mismatched source → none) ==="
  let f := initialMorphism TheoryOfMonoids
  let g := initialMorphism TheoryOfGroups
  -- f.source = ⊥ (name "⊥"), g.source = ⊥ (name "⊥") → same name, so this is NOT a mismatch
  -- Use a morphism with a different source to trigger the None branch
  let fBad : TheoryMorphism :=
    { name := "bad_f", source := TheoryOfMonoids, target := TheoryOfGroups,
      onObjects := GeneratorMap.empty, onMorphisms := GeneratorMap.empty }
  let gBad : TheoryMorphism :=
    { name := "bad_g", source := TheoryOfGroups, target := TheoryOfGroups,
      onObjects := GeneratorMap.empty, onMorphisms := GeneratorMap.empty }
  check "pushout(mismatch) = none" (pushout fBad gBad == none)

-- ============================================================
-- pushout: pushout over ⊥ = disjoint union (algebraic law)
-- ============================================================

#eval do
  IO.println "\n=== pushout over ⊥ = coproduct (shape check) ==="
  for (name, t) in allLibTheories do
    -- Pushout of ⊥ → T over ⊥ with itself: should give T ⊔ T (two tagged copies)
    let po := pushout (initialMorphism t) (initialMorphism t)
    match po with
    | none => throw (IO.userError s!"[FAIL] pushout(⊥→{name}, ⊥→{name}) returned none")
    | some r =>
      smoke s!"pushout(⊥→{name},⊥→{name})" r
      -- No T₀ generators to identify → pure disjoint union
      assertEq s!"pushout/coprod({name}).objects"
        r.objects.length (t.objects.length * 2)
      assertEq s!"pushout/coprod({name}).morphisms"
        r.morphisms.length (t.morphisms.length * 2)

-- ============================================================
-- pushout: self-pushout via id collapses to single copy
-- ============================================================

#eval do
  IO.println "\n=== self-pushout via id: pushout (id T) (id T) ≅ T ==="
  for (name, t) in allLibTheories do
    let f := TheoryMorphism.id t
    let po := pushout f f
    match po with
    | none => throw (IO.userError s!"[FAIL] self-pushout({name}) returned none")
    | some r =>
      smoke s!"self-pushout({name})" r
      -- Every T₀ generator x gets identified: inl(id(x)) ~ inr(id(x))
      -- → only one copy of each generator survives
      assertEq s!"self-pushout({name}).objects"   r.objects.length   t.objects.length
      assertEq s!"self-pushout({name}).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- pushout: amalgamation (Monoid ↪ Group and Monoid ↪ Ring)
-- ============================================================

#eval do
  IO.println "\n=== pushout: amalgamation Group ⊔_Monoid Ring ==="
  let f := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfGroups
  let g := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfRings
  match pushout f g with
  | none => throw (IO.userError "[FAIL] amalgamation returned none")
  | some r =>
    smoke "amalgam(Group ⊔_Monoid Ring)" r
    -- Shared objects (Monoid generators) get identified → count < Group + Ring - Monoid
    let expected_upper := TheoryOfGroups.objects.length + TheoryOfRings.objects.length
    assertGe "amalgam.objects ≤ sum" expected_upper r.objects.length

-- ============================================================
-- theoryCoproduct: algebraic consistency with coproductCategory
-- ============================================================

#eval do
  IO.println "\n=== theoryCoproduct vs coproductCategory (shape consistency) ==="
  for (name, t) in allLibTheories do
    let cop := theoryCoproduct t t
    let ref := coproductCategory t t
    smoke s!"theoryCoproduct({name},{name})" cop
    -- Both should produce a disjoint union with twice the generators
    assertEq s!"theoryCoproduct({name}).objects vs ref"
      cop.objects.length ref.objects.length
    assertEq s!"theoryCoproduct({name}).morphisms vs ref"
      cop.morphisms.length ref.morphisms.length

end CatLab.Tests.CategoryD
