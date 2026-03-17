/-
  CatLab — Category-C Tests

  Operators requiring custom struct arguments.
  Uses canonical fixtures from Fixtures.lean.
-/

import Catlab.Tests.TestCore
import Catlab.Tests.Fixtures
import Catlab.Operators.Monad
import Catlab.Operators.EilenbergMoore
import Catlab.Operators.Kleisli
import Catlab.Operators.Ultrapower
import Catlab.Operators.Fractions
import Catlab.Operators.Skolem
import Catlab.Operators.Grothendieck
import Catlab.Operators.Kan
import Catlab.Operators.Localize
import Catlab.Operators.Sheafify
import Catlab.Operators.Quotient

namespace CatLab.Tests.CategoryC

open CatLab CatLab.Tests CatLab.Tests.Fixtures CatLab.Library

-- ============================================================
-- ultrapower: doubles objects and morphisms, adds diagonals
-- ============================================================

#eval do
  IO.println "\n=== ultrapower ==="
  for (name, t) in allLibTheories do
    let r := ultrapower t ultrafilterN
    smoke s!"ultra({name})" r
    -- originals + ultrapower copies
    assertEq s!"ultra({name}).objects"
      r.objects.length (t.objects.length * 2)
    -- originals + ultra-lifted + diagonals
    assertEq s!"ultra({name}).morphisms"
      r.morphisms.length (t.morphisms.length * 2 + t.objects.length)
    -- originals + transfer + naturality
    assertEq s!"ultra({name}).axioms"
      r.axioms.length (t.axioms.length * 2 + t.morphisms.length)

-- ============================================================
-- calculusOfFractions: trivial (empty fraction class)
-- ============================================================

#eval do
  IO.println "\n=== calculusOfFractions (empty) ==="
  for (name, t) in allLibTheories do
    let r := calculusOfFractions (oreEmpty t)
    smoke s!"fractions({name},∅)" r
    assertEq s!"fractions({name},∅).objects" r.objects.length t.objects.length

#eval do
  IO.println "\n=== calculusOfFractions (all morphisms) ==="
  for (name, t) in allLibTheories do
    let r := calculusOfFractions (oreAll t)
    smoke s!"fractions({name},all)" r
    assertGe s!"fractions({name},all).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- skolemize: trivial (empty existential list)
-- ============================================================

#eval do
  IO.println "\n=== skolemize (empty) ==="
  for (name, t) in allLibTheories do
    let r := skolemize t []
    smoke s!"skolem({name},∅)" r
    -- With no existentials, theory should be unchanged in shape
    assertEq s!"skolem({name},∅).objects"   r.objects.length   t.objects.length
    assertEq s!"skolem({name},∅).morphisms" r.morphisms.length t.morphisms.length

#eval do
  IO.println "\n=== skolemize (one trivial existential) ==="
  for (name, t) in allLibTheories do
    let r := skolemize t [trivialExistential t]
    smoke s!"skolem({name},1)" r
    -- Each existential adds one Skolem function morphism
    assertGe s!"skolem({name},1).morphisms" r.morphisms.length t.morphisms.length

-- ============================================================
-- eilenbergMooreCategory / kleisliCategory (identity monad)
-- ============================================================

#eval do
  IO.println "\n=== eilenbergMooreCategory (identity monad) ==="
  for (name, t) in allLibTheories do
    let m := identityMonad t
    let r := eilenbergMooreCategory m
    smoke s!"EM({name})" r
    -- EM-algebras: one per base object
    assertEq s!"EM({name}).objects" r.objects.length t.objects.length

#eval do
  IO.println "\n=== kleisliCategory (identity monad) ==="
  for (name, t) in allLibTheories do
    let m := identityMonad t
    let r := kleisliCategory m
    smoke s!"Kleisli({name})" r
    assertEq s!"Kleisli({name}).objects" r.objects.length t.objects.length

-- ============================================================
-- eilenbergMoore / coEilenbergMoore (alternative entry points)
-- ============================================================

#eval do
  IO.println "\n=== eilenbergMoore (identity monad) ==="
  for (name, t) in allLibTheories do
    let r := eilenbergMoore (identityMonad t)
    smoke s!"EM2({name})" r

#eval do
  IO.println "\n=== coEilenbergMoore (identity comonad) ==="
  for (name, t) in allLibTheories do
    let r := coEilenbergMoore (identityComonad t)
    smoke s!"coEM({name})" r

-- ============================================================
-- grothendieck: constant fibration (all fibers = same theory)
-- ============================================================

#eval do
  IO.println "\n=== grothendieck (constant fibration) ==="
  for (name, t) in allLibTheories do
    -- Use Monoid as the constant fiber
    let ic := constantIndexed t TheoryOfMonoids
    let r := grothendieck ic
    smoke s!"grothendieck({name},Monoid)" r
    -- Total space has base × fiber objects
    assertGe s!"grothendieck({name},Monoid).objects" r.objects.length
      (t.objects.length * TheoryOfMonoids.objects.length)

  -- Self-indexed: fiber = base
  for (name, t) in allLibTheories do
    let ic := constantIndexed t t
    let r := grothendieck ic
    smoke s!"grothendieck({name},{name})" r

-- ============================================================
-- leftKan / rightKan (identity functor)
-- ============================================================

#eval do
  IO.println "\n=== leftKan (along identity) ==="
  for (name, t) in allLibTheories do
    let idF := identityFunctor t
    let r := leftKan idF idF
    smoke s!"leftKan(Id_{name})" r

#eval do
  IO.println "\n=== rightKan (along identity) ==="
  for (name, t) in allLibTheories do
    let idF := identityFunctor t
    let r := rightKan idF idF
    smoke s!"rightKan(Id_{name})" r

-- ============================================================
-- simplicialLocalize (weak equivalences = empty)
-- ============================================================

#eval do
  IO.println "\n=== simplicialLocalize (no weak equivalences) ==="
  for (name, t) in allLibTheories do
    let r := simplicialLocalize (trivialWeakEquivalences t)
    smoke s!"simplLoc({name},∅)" r
    assertGe s!"simplLoc({name},∅).objects" r.objects.length t.objects.length

-- ============================================================
-- sheafify (trivial topology = no covers)
-- ============================================================

#eval do
  IO.println "\n=== sheafify (trivial topology) ==="
  for (name, t) in allLibTheories do
    let r := sheafify t trivialTopology
    smoke s!"sheafify({name})" r

end CatLab.Tests.CategoryC
