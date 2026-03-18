/-
  CatLab — Theory of Lie Algebras

  Derived from AbelianGroup by adding a Lie bracket:

    LieAlgebra = addBracket(AbelianGroup, "μ", "μ_inv", "⟦,⟧")

  The bracket [−,−] : L × L → L satisfies:
    antisymmetry : [x,y] = neg([y,x])
    Jacobi       : [x,[y,z]] = [[x,y],z] + [y,[x,z]]
    bilinearity  : [x, y+z] = [x,y] + [x,z]

  The abelian group provides the additive structure (μ = add, η = zero, μ_inv = neg).
  The bracket is the only genuinely new primitive.
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize
import Catlab.Library.Group

namespace CatLab.Library

/-- The theory of Lie algebras: an abelian group with a Lie bracket.
    Morphisms: μ (add), η (zero), μ_inv (neg), swap, ⟦,⟧ (bracket).
    Axioms: abelian group axioms + antisymmetry + Jacobi + bilinearity. -/
def TheoryOfLieAlgebra : Theory :=
  { addBracket TheoryOfAbelianGroups "μ" "μ_inv" "⟦,⟧" with
    name     := "LieAlgebra"
    doctrine := { doctrine := .LawvereTheory } }

end CatLab.Library
