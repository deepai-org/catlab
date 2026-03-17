/-
  CatLab — Property Tests (Level 3)

  Semantic/mathematical law tests. These verify that operators satisfy
  the categorical identities they are supposed to implement.
-/

import Catlab.Tests.TestCore
import Catlab.Operators.Mirror
import Catlab.Operators.Decategorify
import Catlab.Operators.DayConvolution
import Catlab.Operators.Morita
import Catlab.Operators.Nerve
import Catlab.Operators.Skolem

namespace CatLab.Tests.Properties

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- mirror is an involution on signature
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: mirror is an involution ==="
  for (name, t) in allLibTheories do
    let mm := mirror (mirror t)
    assertEq s!"mirror²({name}).objects"   mm.objects.length   t.objects.length
    assertEq s!"mirror²({name}).morphisms" mm.morphisms.length t.morphisms.length
    assertEq s!"mirror²({name}).axioms"    mm.axioms.length    t.axioms.length

-- ============================================================
-- decategorify: morphisms collapse to 0 under isoClasses
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: decategorify collapses morphisms ==="
  for (name, t) in allLibTheories do
    let d := decategorify t .isoClasses
    assertEq s!"decat/iso({name}).morphisms = 0" d.morphisms.length 0

-- ============================================================
-- decategorify(grothendieckGroup) always yields exactly 1 object
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: K₀ always has 1 object ==="
  for (name, t) in allLibTheories do
    let k0 := decategorify t .grothendieckGroup
    assertEq s!"K₀({name}).objects = 1" k0.objects.length 1

-- ============================================================
-- tensorTheories is commutative in morphism count
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: tensorTheories morphism count is symmetric ==="
  let pairs := [
    ("Monoid", TheoryOfMonoids, "Group", TheoryOfGroups),
    ("Monoid", TheoryOfMonoids, "Ring",  TheoryOfRings),
    ("Group",  TheoryOfGroups,  "Ring",  TheoryOfRings),
  ]
  for (n1, t1, n2, t2) in pairs do
    let r12 := tensorTheories t1 t2
    let r21 := tensorTheories t2 t1
    assertEq s!"tensor({n1},{n2}) vs tensor({n2},{n1}) morphisms"
      r12.morphisms.length r21.morphisms.length

-- ============================================================
-- verifyCategorification roundtrip:
--   decategorify(t) should recover base counts from t itself
--   (trivial case: any theory is a "categorification" of its own decat)
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: verifyCategorification self-consistency ==="
  for (name, t) in allLibTheories do
    let shadow := decategorify t .isoClasses
    -- verifyCategorification checks that shadow.objects.length == target.objects.length
    -- and that all target axioms appear in the shadow
    let ok := verifyCategorification t shadow .isoClasses
    check s!"verify({name}, decat({name}))" ok

-- ============================================================
-- morleyize adds exactly 1 object and #axioms morphisms
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: morleyize adds Herbrand universe ==="
  for (name, t) in allLibTheories do
    let r := morleyize t
    assertEq s!"morleyize({name}).objects = original + 1" r.objects.length (t.objects.length + 1)
    assertEq s!"morleyize({name}).morphisms = original + axioms"
      r.morphisms.length (t.morphisms.length + t.axioms.length)

-- ============================================================
-- Morita: every theory is Morita-equivalent to itself
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: areMoritaEquivalent is reflexive ==="
  for (name, t) in allLibTheories do
    check s!"morita({name},{name})" (areMoritaEquivalent t t)

-- ============================================================
-- nerve ∘ realize roundtrip: object count preserved
-- ============================================================

#eval do
  IO.println "\n=== PROPERTY: nerve has correct simplex count ==="
  for (name, t) in allLibTheories do
    let n := nerve t 3
    -- nerve should have exactly maxDim+1 simplex objects: N_0 … N_3
    assertEq s!"nerve({name}, 3).simplexLevels" n.objects.length 4

end CatLab.Tests.Properties
