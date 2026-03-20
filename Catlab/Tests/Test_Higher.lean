/-
  CatLab — Higher-Categorical Tests

  Verifies:
  1. Truncation level metadata is set correctly on higher theories
  2. The truncate operator produces valid theories
  3. truncate 1 (∞,2)-Category ≅ Category (structurally)
  4. Strictified flag is set on all higher theories
-/

import Catlab.Tests.TestCore
import Catlab.Core.Validate
import Catlab.Core.Equality
import Catlab.Operators.Truncate

namespace CatLab.Tests.Higher

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- 1. Truncation level metadata
-- ============================================================

#eval do
  IO.println "\n=== higher: truncation level metadata ==="
  let inf2 := TheoryOfInfinityTwoCategory
  check "∞-2-cat truncation = 2" (inf2.doctrine.truncationLevel == some 2)
  let infCat := TheoryOfInfinityCategory
  check "∞-cat truncation = 1" (infCat.doctrine.truncationLevel == some 1)
  -- Non-higher theories should have no truncation level
  let mon := TheoryOfMonoids
  check "Monoid truncation = none" (mon.doctrine.truncationLevel == none)
  let cat := TheoryOfCategories
  check "Category truncation = none" (cat.doctrine.truncationLevel == none)

-- ============================================================
-- 2. Strictified flag on higher theories
-- ============================================================

#eval do
  IO.println "\n=== higher: strictified flag ==="
  let higherTheories := [
    ("Infinity2Category", TheoryOfInfinityTwoCategory),
    ("InfinityCategory", TheoryOfInfinityCategory),
    ("HoTT", TheoryOfHoTT),
    ("InfinityTopos", TheoryOfInfinityTopos),
    ("CubicalTypeTheory", TheoryOfCubicalTypeTheory),
    ("CohesiveHoTT", TheoryOfCohesiveHoTT),
    ("CategoriesWithAttributes", TheoryOfCategoriesWithAttributes)
  ]
  for (name, t) in higherTheories do
    check s!"{name} is strictified" t.doctrine.strictified

-- ============================================================
-- 3. Truncation operator produces valid theories
-- ============================================================

#eval do
  IO.println "\n=== higher: truncate produces valid theories ==="
  let inf2 := TheoryOfInfinityTwoCategory
  let trunc1 := truncate inf2 1
  let errs := CatLab.validate trunc1
  if !errs.isEmpty then
    for e in errs.take 3 do IO.println s!"  {e}"
  check s!"truncate 1 (∞,2)-Cat validates ({errs.length} errors)" errs.isEmpty
  -- Truncated theory should have truncation level 1
  check "truncated level = 1" (trunc1.doctrine.truncationLevel == some 1)

  let trunc0 := truncate inf2 0
  let errs0 := CatLab.validate trunc0
  check s!"truncate 0 (∞,2)-Cat validates ({errs0.length} errors)" errs0.isEmpty
  check "truncated level = 0" (trunc0.doctrine.truncationLevel == some 0)

-- ============================================================
-- 4. Truncation reduces cell counts
-- ============================================================

#eval do
  IO.println "\n=== higher: truncation reduces cell counts ==="
  let inf2 := TheoryOfInfinityTwoCategory
  let trunc1 := truncate inf2 1
  let trunc0 := truncate inf2 0
  -- Original has Cell0, Cell1, Cell2
  assertEq "∞-2-cat objects" inf2.objects.length 3
  -- Truncate at 1: keep Cell0, Cell1 only
  check s!"trunc1 objects ≤ 2 (got {trunc1.objects.length})" (trunc1.objects.length <= 2)
  -- Truncate at 0: keep Cell0 only
  check s!"trunc0 objects ≤ 1 (got {trunc0.objects.length})" (trunc0.objects.length <= 1)
  -- Morphisms should also decrease
  check "trunc1 morphisms < original" (trunc1.morphisms.length < inf2.morphisms.length)
  IO.println s!"  ∞-2-cat: {inf2.objects.length} objs, {inf2.morphisms.length} mors"
  IO.println s!"  trunc1:  {trunc1.objects.length} objs, {trunc1.morphisms.length} mors"
  IO.println s!"  trunc0:  {trunc0.objects.length} objs, {trunc0.morphisms.length} mors"

-- ============================================================
-- 5. Truncation preserves doctrine
-- ============================================================

#eval do
  IO.println "\n=== higher: truncation preserves doctrine ==="
  let inf2 := TheoryOfInfinityTwoCategory
  let trunc1 := truncate inf2 1
  check "doctrine preserved" (trunc1.doctrine.doctrine == inf2.doctrine.doctrine)
  check "still strictified" trunc1.doctrine.strictified

-- ============================================================
-- 6. Higher theories have the isHigherCategorical flag
-- ============================================================

#eval do
  IO.println "\n=== higher: isHigherCategorical flag ==="
  check "InfinityNCategory is higher" (Doctrine.isHigherCategorical .InfinityNCategory)
  check "MartinLofTypeTheory is higher" (Doctrine.isHigherCategorical .MartinLofTypeTheory)
  check "CubicalTypeTheory is higher" (Doctrine.isHigherCategorical .CubicalTypeTheory)
  check "CohesiveHoTT is higher" (Doctrine.isHigherCategorical .CohesiveHomotopyTypeTheory)
  check "Category is NOT higher" (!Doctrine.isHigherCategorical .Category)
  check "MonoidalCategory is NOT higher" (!Doctrine.isHigherCategorical .MonoidalCategory)

end CatLab.Tests.Higher
