/-
  CatLab -- Differential Graded Algebras (DGAs)

  Derived as: chainComplexCategory(TheoryOfMonoids)

  A chain complex of monoids is exactly a graded algebra with a differential:
    - The graded components A₀, A₁, …, Aₙ come from copies of the Monoid object
    - The monoid structure (μ, η) provides the graded multiplication at each degree
    - The boundary maps dₙ : Aₙ → Aₙ₋₁ are the differential (d² = 0 by the axioms)
    - The Leibniz rule d(ab) = d(a)·b ± a·d(b) is encoded in the lifted interchange

  The graded commutativity (CDGA case) is an additional symmetry axiom;
  the chain complex category already carries the associativity and d² = 0.

  Examples:
    - de Rham complex: Ω*(M) = chain complex of exterior algebras (differential forms)
    - Singular cochains: C*(X; R) with cup product
    - Bar construction of an algebra
-/

import Catlab.Core.Theory
import Catlab.Operators.Derived
import Catlab.Library.Monoid

namespace CatLab.Library

/-- The theory of differential graded algebras, derived as the chain complex
    category of the theory of monoids.  The graded components are copies of
    the monoid at each degree; the boundary maps are the differential (d² = 0). -/
def TheoryOfDifferentialGradedAlgebra : Theory :=
  { chainComplexCategory TheoryOfMonoids with
    name     := "DifferentialGradedAlgebra"
    doctrine := { doctrine := .DifferentialGraded } }

end CatLab.Library
