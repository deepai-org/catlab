/-
  CatLab — Category-A Tests

  Every pure Theory → Theory operator applied to every library theory.
  Tests cover:
    Level 1 (smoke): operator terminates and returns a named Theory
    Level 2 (shape): numeric invariants on objects/morphisms/axioms
-/

import Catlab.Tests.TestCore
import Catlab.Operators.Mirror
import Catlab.Operators.Opposite
import Catlab.Operators.Decategorify
import Catlab.Operators.Karoubi
import Catlab.Operators.DrinfeldCenter
import Catlab.Operators.MacNeille
import Catlab.Operators.TwistedArrow
import Catlab.Operators.IndPro
import Catlab.Operators.Center
import Catlab.Operators.Yoneda
import Catlab.Operators.Arrow
import Catlab.Operators.Comma
import Catlab.Operators.Free
import Catlab.Operators.Matrix
import Catlab.Operators.Span
import Catlab.Operators.Family
import Catlab.Operators.Nerve
import Catlab.Operators.Syntactic
import Catlab.Operators.Int
import Catlab.Operators.ExactCompletion
import Catlab.Operators.Morita
import Catlab.Operators.Internal
import Catlab.Operators.Booleanize
import Catlab.Operators.OperadEnvelope
import Catlab.Operators.Freyd
import Catlab.Operators.Stabilize
import Catlab.Operators.Derived
import Catlab.Operators.Isbell
import Catlab.Operators.Lawvere
import Catlab.Operators.Skolem
import Catlab.Operators.FunctorCategory

namespace CatLab.Tests.CategoryA

open CatLab CatLab.Arrow CatLab.Tests CatLab.Library

-- ============================================================
-- mirror: morphism count preserved; involution
-- ============================================================

#eval do
  IO.println "\n=== mirror ==="
  for (name, t) in allLibTheories do
    let r := mirror t
    smoke s!"mirror({name})" r
    assertEq s!"mirror({name}).morphisms" r.morphisms.length t.morphisms.length
    assertEq s!"mirror({name}).axioms"    r.axioms.length    t.axioms.length
    -- involution
    let rr := mirror r
    assertEq s!"mirror(mirror({name})).morphisms" rr.morphisms.length t.morphisms.length

-- ============================================================
-- opposite: same shape as mirror (it is mirror for non-enriched)
-- ============================================================

#eval do
  IO.println "\n=== opposite ==="
  for (name, t) in allLibTheories do
    let r := opposite t
    smoke s!"opposite({name})" r
    assertEq s!"opposite({name}).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- decategorify: three strategies, shape invariants
-- ============================================================

#eval do
  IO.println "\n=== decategorify (.isoClasses) ==="
  for (name, t) in allLibTheories do
    let r := decategorify t .isoClasses
    smoke s!"decategorify/iso({name})" r
    assertEq s!"decategorify/iso({name}).objects"   r.objects.length   t.objects.length
    assertEq s!"decategorify/iso({name}).morphisms" r.morphisms.length 0

#eval do
  IO.println "\n=== decategorify (.grothendieckGroup) ==="
  for (name, t) in allLibTheories do
    let r := decategorify t .grothendieckGroup
    smoke s!"decategorify/K0({name})" r
    assertEq s!"decategorify/K0({name}).objects"   r.objects.length   1
    assertEq s!"decategorify/K0({name}).morphisms" r.morphisms.length t.objects.length

#eval do
  IO.println "\n=== decategorify (.eulerCharacteristic) ==="
  for (name, t) in allLibTheories do
    let r := decategorify t .eulerCharacteristic
    smoke s!"decategorify/chi({name})" r
    assertEq s!"decategorify/chi({name}).objects"   r.objects.length   1
    assertEq s!"decategorify/chi({name}).morphisms" r.morphisms.length 1

-- ============================================================
-- karoubiEnvelope: at least as many objects and morphisms
-- ============================================================

#eval do
  IO.println "\n=== karoubiEnvelope ==="
  for (name, t) in allLibTheories do
    let r := karoubiEnvelope t
    smoke s!"karoubi({name})" r
    assertGe s!"karoubi({name}).objects"   r.objects.length   t.objects.length
    assertGe s!"karoubi({name}).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- drinfeldCenter: one center-object per base object
-- ============================================================

#eval do
  IO.println "\n=== drinfeldCenter ==="
  for (name, t) in allLibTheories do
    let r := drinfeldCenter t
    smoke s!"drinfeldCenter({name})" r
    assertEq s!"drinfeldCenter({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- macneilleCompletion: at least as many objects
-- ============================================================

#eval do
  IO.println "\n=== macneilleCompletion ==="
  for (name, t) in allLibTheories do
    let r := macneilleCompletion t
    smoke s!"macneille({name})" r
    assertGe s!"macneille({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- twistedArrow: objects are original morphisms
-- ============================================================

#eval do
  IO.println "\n=== twistedArrow ==="
  for (name, t) in allLibTheories do
    let r := twistedArrow t
    smoke s!"twistedArrow({name})" r
    assertEq s!"twistedArrow({name}).objects" r.objects.length t.morphisms.length

-- ============================================================
-- indCompletion / proCompletion: at least original objects
-- ============================================================

#eval do
  IO.println "\n=== indCompletion ==="
  for (name, t) in allLibTheories do
    let r := indCompletion t
    smoke s!"ind({name})" r
    assertGe s!"ind({name}).objects" r.objects.length t.objects.length

#eval do
  IO.println "\n=== proCompletion ==="
  for (name, t) in allLibTheories do
    let r := proCompletion t
    smoke s!"pro({name})" r
    assertGe s!"pro({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- center: objects preserved
-- ============================================================

#eval do
  IO.println "\n=== center ==="
  for (name, t) in allLibTheories do
    let r := center t
    smoke s!"center({name})" r

-- ============================================================
-- presheafCategory (Yoneda): representables = one per base object
-- ============================================================

#eval do
  IO.println "\n=== presheafCategory ==="
  for (name, t) in allLibTheories do
    let r := presheafCategory t
    smoke s!"presheaf({name})" r
    assertGe s!"presheaf({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- arrowCat / arrowCategory (from Comma.lean): objects doubled
-- ============================================================

#eval do
  IO.println "\n=== arrowCat ==="
  for (name, t) in allLibTheories do
    let r := arrowCat t
    smoke s!"arrowCat({name})" r

#eval do
  IO.println "\n=== arrowCategory ==="
  for (name, t) in allLibTheories do
    let r := arrowCategory t
    smoke s!"arrowCategory({name})" r

-- ============================================================
-- pathCategory (Free): at least original objects
-- ============================================================

#eval do
  IO.println "\n=== pathCategory ==="
  for (name, t) in allLibTheories do
    let r := pathCategory t
    smoke s!"path({name})" r
    assertGe s!"path({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- matrixCategory: one object (Mat(C) has a single hom-object)
-- ============================================================

#eval do
  IO.println "\n=== matrixCategory ==="
  for (name, t) in allLibTheories do
    let r := matrixCategory t
    smoke s!"matrix({name})" r

-- ============================================================
-- spanCategory / cospanCategory: objects preserved
-- ============================================================

#eval do
  IO.println "\n=== spanCategory ==="
  for (name, t) in allLibTheories do
    let r := spanCategory t
    smoke s!"span({name})" r

#eval do
  IO.println "\n=== cospanCategory ==="
  for (name, t) in allLibTheories do
    let r := cospanCategory t
    smoke s!"cospan({name})" r

-- ============================================================
-- familyCategory: more objects (empty + singletons + pairs)
-- ============================================================

#eval do
  IO.println "\n=== familyCategory ==="
  for (name, t) in allLibTheories do
    let r := familyCategory t
    smoke s!"family({name})" r
    assertGe s!"family({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- nerve: n+1 simplex levels of objects
-- ============================================================

#eval do
  IO.println "\n=== nerve (maxDim=2) ==="
  for (name, t) in allLibTheories do
    let r := nerve t 2
    smoke s!"nerve({name})" r
    assertEq s!"nerve({name}).objects" r.objects.length 3  -- N_0, N_1, N_2

-- ============================================================
-- syntacticCategory: at least original objects
-- ============================================================

#eval do
  IO.println "\n=== syntacticCategory ==="
  for (name, t) in allLibTheories do
    let r := syntacticCategory t
    smoke s!"syntactic({name})" r

-- ============================================================
-- intConstruction
-- ============================================================

#eval do
  IO.println "\n=== intConstruction ==="
  for (name, t) in allLibTheories do
    let r := intConstruction t
    smoke s!"int({name})" r

-- ============================================================
-- regCompletion / exCompletion
-- ============================================================

#eval do
  IO.println "\n=== regCompletion ==="
  for (name, t) in allLibTheories do
    let r := regCompletion t
    smoke s!"reg({name})" r
    assertGe s!"reg({name}).objects" r.objects.length t.objects.length

#eval do
  IO.println "\n=== exCompletion ==="
  for (name, t) in allLibTheories do
    let r := exCompletion t
    smoke s!"ex({name})" r
    assertGe s!"ex({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- moritaEnvelope: non-empty result
-- ============================================================

#eval do
  IO.println "\n=== moritaEnvelope ==="
  for (name, t) in allLibTheories do
    let r := moritaEnvelope t
    smoke s!"morita({name})" r
    assertGe s!"morita({name}).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- internalCategoryCategory
-- ============================================================

#eval do
  IO.println "\n=== internalCategoryCategory ==="
  for (name, t) in allLibTheories do
    let r := internalCategoryCategory t
    smoke s!"internal({name})" r

-- ============================================================
-- booleanize: result has boolean structure
-- ============================================================

#eval do
  IO.println "\n=== booleanize ==="
  for (name, t) in allLibTheories do
    let r := booleanize t
    smoke s!"booleanize({name})" r
    assertGe s!"booleanize({name}).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- operadicEnvelope: unit object added
-- ============================================================

#eval do
  IO.println "\n=== operadicEnvelope ==="
  for (name, t) in allLibTheories do
    let r := operadicEnvelope t
    smoke s!"openv({name})" r
    -- unit + singletons + pairs = 1 + n + n²
    let n := t.objects.length
    assertEq s!"openv({name}).objects" r.objects.length (1 + n + n * n)

-- ============================================================
-- scone (Freyd cover)
-- ============================================================

#eval do
  IO.println "\n=== scone ==="
  for (name, t) in allLibTheories do
    let r := scone t
    smoke s!"scone({name})" r

-- ============================================================
-- stabilize: maxLevel+1 copies of objects
-- ============================================================

#eval do
  IO.println "\n=== stabilize (maxLevel=2) ==="
  for (name, t) in allLibTheories do
    let r := stabilize t 2
    smoke s!"stabilize({name})" r
    assertGe s!"stabilize({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- chainComplexCategory: (maxDeg+1) copies of objects
-- ============================================================

#eval do
  IO.println "\n=== chainComplexCategory (maxDeg=2) ==="
  for (name, t) in allLibTheories do
    let r := chainComplexCategory t 2
    smoke s!"chain({name})" r
    assertEq s!"chain({name}).objects" r.objects.length (t.objects.length * 3)

#eval do
  IO.println "\n=== homotopyCategory ==="
  for (name, t) in allLibTheories do
    let r := homotopyCategory t 2
    smoke s!"homotopy({name})" r

#eval do
  IO.println "\n=== derivedCategory ==="
  for (name, t) in allLibTheories do
    let r := derivedCategory t 2
    smoke s!"derived({name})" r

-- ============================================================
-- isbellSpec / isbellCospec / isbellAdjunction
-- ============================================================

#eval do
  IO.println "\n=== isbellSpec ==="
  for (name, t) in allLibTheories do
    let r := isbellSpec t
    smoke s!"isbellSpec({name})" r

#eval do
  IO.println "\n=== isbellCospec ==="
  for (name, t) in allLibTheories do
    let r := isbellCospec t
    smoke s!"isbellCospec({name})" r

#eval do
  IO.println "\n=== isbellAdjunction ==="
  for (name, t) in allLibTheories do
    let r := isbellAdjunction t
    smoke s!"isbellAdj({name})" r

-- ============================================================
-- algebraCategory (Lawvere models)
-- ============================================================

#eval do
  IO.println "\n=== algebraCategory ==="
  for (name, t) in allLibTheories do
    let r := algebraCategory t
    smoke s!"algebra({name})" r

-- ============================================================
-- morleyize (Skolem): adds one morphism per axiom
-- ============================================================

#eval do
  IO.println "\n=== morleyize ==="
  for (name, t) in allLibTheories do
    let r := morleyize t
    smoke s!"morleyize({name})" r
    -- morleyize adds 1 Herbrand universe object and one Skolem morphism per axiom
    assertEq s!"morleyize({name}).objects"   r.objects.length   (t.objects.length + 1)
    assertEq s!"morleyize({name}).morphisms" r.morphisms.length (t.morphisms.length + t.axioms.length)

-- ============================================================
-- functorCategory: endofunctor category C^C
-- ============================================================

#eval do
  IO.println "\n=== functorCategory (C^C) ==="
  for (name, t) in allLibTheories do
    let r := functorCategory t t
    smoke s!"funCat({name})" r

end CatLab.Tests.CategoryA
