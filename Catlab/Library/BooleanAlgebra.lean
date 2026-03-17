/-
  CatLab — Heyting Algebras and Boolean Algebras

  Full derivation chain from Lattice:

    BoundedLattice  = addUnit(addUnit(Lattice, "∧"), "∨"), rename units to ⊤/⊥
    HeytingAlgebra  = addAdjoint(BoundedLattice, "∧", "→")
    BooleanAlgebra  = booleanize(HeytingAlgebra)

  Every Boolean algebra is a Heyting algebra (→ defined by ¬a ∨ b).
  Stone Duality: Mirror(BooleanAlgebra) ≅ Stone Spaces.
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize
import Catlab.Operators.Booleanize
import Catlab.Library.Lattice

namespace CatLab.Library

-- ── Bounded lattice: Lattice + top ⊤ (unit for ∧) + bottom ⊥ (unit for ∨) ─
private def boundedLattice : Theory :=
  renameGenerator
    (addUnit (addUnit TheoryOfLattices "∧") "∨")
    [("∧_unit", "⊤"), ("∨_unit", "⊥")]

/-- The theory of Heyting algebras: a bounded distributive lattice with
    Heyting implication → as the right adjoint to meet ∧.
    The internal logic of any elementary topos. -/
def TheoryOfHeytingAlgebra : Theory :=
  { addAdjoint boundedLattice "∧" "→" with
    name     := "HeytingAlgebra"
    doctrine := { doctrine := .CartesianClosed } }

/-- The theory of Boolean algebras: booleanize(HeytingAlgebra).
    Adds involutive negation ¬ and double-negation elimination ¬¬a = a
    (equivalent to the law of excluded middle a ∨ ¬a = ⊤). -/
def TheoryOfBooleanAlgebra : Theory :=
  booleanize TheoryOfHeytingAlgebra

end CatLab.Library
