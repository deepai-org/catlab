/-
  CatLab -- Triangulated Categories

  Derived as: stabilize(TheoryOfAbelianCategory)

  The stabilization of an abelian category freely inverts the suspension
  functor Σ, producing the stable category with:
    - Suspension Σ as an autoequivalence (from the stabilization levels)
    - Exact triangles X → Y → Z → ΣX arising from the stable exact sequences
    - Octahedral axiom as a consequence of the 2-of-3 property in stable maps

  This captures the Freyd/Brown-Margolis theorem: stable homotopy categories
  are triangulated, and the triangulation arises from the stabilization.

  The struct extension overrides name and doctrine; the suspension objects and
  morphisms at each level come directly from `stabilize`.
-/

import Catlab.Core.Theory
import Catlab.Operators.Stabilize
import Catlab.Library.AbelianCategory

namespace CatLab.Library

/-- The theory of triangulated categories, derived as the stabilization of the
    theory of abelian categories.  Stabilization inverts Σ and introduces the
    suspension tower; distinguished triangles are the stable exact sequences. -/
def TheoryOfTriangulatedCategory : Theory :=
  { stabilize TheoryOfAbelianCategory with
    name     := "TriangulatedCategory"
    doctrine := { doctrine := .TriangulatedCategory } }

end CatLab.Library
