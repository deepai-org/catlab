/-
  CatLab — Theory of Groups and Abelian Groups

  Derived from Monoid using the algebraic combinators:

    Group        = addInverse(Monoid, "μ", "η")
    AbelianGroup = addCommutativity(Group, "μ")
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize
import Catlab.Library.Monoid

namespace CatLab.Library

/-- The theory of groups: Monoid extended with an inverse for μ.
    Morphisms: μ (multiplication), η (unit), μ_inv (inverse).
    Axioms: associativity, left/right unit, left/right inverse. -/
def TheoryOfGroups : Theory :=
  { addInverse TheoryOfMonoids "μ" "η" with
    name := "Group" }

/-- The theory of abelian groups: Group extended with commutativity of μ.
    Adds swap : M × M → M × M and axiom comm_μ : μ = swap ∘ μ. -/
def TheoryOfAbelianGroups : Theory :=
  { addCommutativity TheoryOfGroups "μ" with
    name := "AbelianGroup" }

end CatLab.Library
