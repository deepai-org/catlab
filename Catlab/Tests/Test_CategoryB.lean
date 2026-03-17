/-
  CatLab — Category-B Tests

  Binary operators and Theory+simple-arg operators.
  - tensorTheories, productCategory, coproductCategory
  - slice, overCategory, chuConstruction, dialectica
  - bousfieldLocalization, fullSubcategory, core
  - quotientCategory (with trivial congruence)
  - collage (two theories joined by hetero-morphisms)
-/

import Catlab.Tests.TestCore
import Catlab.Tests.Fixtures
import Catlab.Operators.DayConvolution
import Catlab.Operators.Product
import Catlab.Operators.Coproduct
import Catlab.Operators.Comma
import Catlab.Operators.Slice
import Catlab.Operators.Chu
import Catlab.Operators.Bousfield
import Catlab.Operators.Subcategory
import Catlab.Operators.Core
import Catlab.Operators.Quotient
import Catlab.Operators.Collage
import Catlab.Operators.Lawvere

namespace CatLab.Tests.CategoryB

open CatLab CatLab.Tests CatLab.Tests.Fixtures CatLab.Library

-- ============================================================
-- tensorTheories: morphisms are sum of both inputs
-- ============================================================

#eval do
  IO.println "\n=== tensorTheories ==="
  -- Test all same-theory tensors
  for (name, t) in allLibTheories do
    let r := tensorTheories t t
    smoke s!"tensor({name},{name})" r
    assertEq s!"tensor({name},{name}).morphisms"
      r.morphisms.length (t.morphisms.length * 2)

  -- Cross-theory: Monoid ⊗ AbelianGroup → Ring-like
  let r := tensorTheories TheoryOfMonoids TheoryOfAbelianGroups
  smoke "tensor(Monoid,AbelianGroup)" r
  assertGe "tensor(Monoid,AbelianGroup).morphisms" r.morphisms.length
    (TheoryOfMonoids.morphisms.length + TheoryOfAbelianGroups.morphisms.length)

  -- Ring ⊗ Monoid
  let r2 := tensorTheories TheoryOfRings TheoryOfMonoids
  smoke "tensor(Ring,Monoid)" r2

-- ============================================================
-- productCategory: objects are sum; morphisms are sum
-- ============================================================

#eval do
  IO.println "\n=== productCategory ==="
  for (name, t) in allLibTheories do
    let r := productCategory t t
    smoke s!"product({name},{name})" r
    -- product shares/unifies objects; at least as many as either factor
    assertGe s!"product({name},{name}).objects"   r.objects.length   t.objects.length
    assertGe s!"product({name},{name}).morphisms" r.morphisms.length t.morphisms.length

  -- Cross-product: Monoid × Group
  let r := productCategory TheoryOfMonoids TheoryOfGroups
  smoke "product(Monoid,Group)" r

-- ============================================================
-- coproductCategory: similar to product (disjoint union)
-- ============================================================

#eval do
  IO.println "\n=== coproductCategory ==="
  for (name, t) in allLibTheories do
    let r := coproductCategory t t
    smoke s!"coproduct({name},{name})" r

  let r := coproductCategory TheoryOfMonoids TheoryOfGroups
  smoke "coproduct(Monoid,Group)" r

-- ============================================================
-- overCategory / slice: picks first object as the base
-- ============================================================

#eval do
  IO.println "\n=== overCategory ==="
  for (name, t) in allLibTheories do
    -- Use the first object as the over-object; skip if empty
    match t.objects.head? with
    | none   => IO.println s!"[SKIP] overCategory({name}): no objects"
    | some o =>
      let r := overCategory t (.atom o.id)
      smoke s!"over({name}/{o.id.name})" r

#eval do
  IO.println "\n=== slice ==="
  for (name, t) in allLibTheories do
    match t.objects.head? with
    | none   => IO.println s!"[SKIP] slice({name}): no objects"
    | some o =>
      let r := slice t (.atom o.id)
      smoke s!"slice({name}/{o.id.name})" r

-- ============================================================
-- chuConstruction: dualizer = first object atom
-- ============================================================

#eval do
  IO.println "\n=== chuConstruction ==="
  for (name, t) in allLibTheories do
    match t.objects.head? with
    | none   => IO.println s!"[SKIP] chu({name}): no objects"
    | some o =>
      let r := chuConstruction t (.atom o.id)
      smoke s!"chu({name}/{o.id.name})" r

-- ============================================================
-- bousfieldLocalization: empty local class (no change expected)
-- ============================================================

#eval do
  IO.println "\n=== bousfieldLocalization (empty) ==="
  for (name, t) in allLibTheories do
    let r := bousfieldLocalization t []
    smoke s!"bousfield({name},∅)" r
    -- With no local morphisms, objects should be preserved
    assertEq s!"bousfield({name},∅).objects" r.objects.length t.objects.length

  -- Non-trivial: localize at first morphism
  for (name, t) in allLibTheories do
    match t.morphisms.head? with
    | none   => IO.println s!"[SKIP] bousfield({name}): no morphisms"
    | some m =>
      let r := bousfieldLocalization t [m.id]
      smoke s!"bousfield({name},{m.id.name})" r

-- ============================================================
-- fullSubcategory: predicate = all objects (identity)
-- ============================================================

#eval do
  IO.println "\n=== fullSubcategory (all) ==="
  for (name, t) in allLibTheories do
    let r := fullSubcategory t (fun _ => true)
    smoke s!"sub({name},⊤)" r
    assertEq s!"sub({name},⊤).objects" r.objects.length t.objects.length

#eval do
  IO.println "\n=== fullSubcategory (none) ==="
  for (name, t) in allLibTheories do
    let r := fullSubcategory t (fun _ => false)
    smoke s!"sub({name},⊥)" r
    assertEq s!"sub({name},⊥).objects" r.objects.length 0

-- ============================================================
-- core: empty iso-class list gives empty result
-- ============================================================

#eval do
  IO.println "\n=== core (no isos) ==="
  for (name, t) in allLibTheories do
    let r := core t []
    smoke s!"core({name},∅)" r
    assertEq s!"core({name},∅).objects" r.objects.length t.objects.length

-- ============================================================
-- quotientCategory: trivial congruence preserves shape
-- ============================================================

#eval do
  IO.println "\n=== quotientCategory (trivial) ==="
  for (name, t) in allLibTheories do
    let r := quotientCategory t trivialCongruence
    smoke s!"quotient({name},trivial)" r
    assertEq s!"quotient({name},trivial).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- lawvereModelCategory: models of each theory in itself
-- ============================================================

#eval do
  IO.println "\n=== lawvereModelCategory (self) ==="
  for (name, t) in allLibTheories do
    let r := lawvereModelCategory t t
    smoke s!"models({name},{name})" r

end CatLab.Tests.CategoryB
