/-
  CatLab — Theory of Hopf Algebras

  Derived by amalgamating Monoid (algebra) with mirror(Monoid) (coalgebra),
  then adding bialgebra compatibility and the antipode:

    algebra   = Monoid renamed  (mul, unit : H)
    coalgebra = mirror(Monoid) renamed  (comul : H→H⊗H, counit : H→1)

    Note: mirror(Monoid) has REVERSED axiom paths, giving proper
    coassociativity and counit laws (the duals of associativity/unit).

    bialgebra = amalgamateOver(algebra, coalgebra) + addBialgebraAxioms
    HopfAlgebra = addAntipode(bialgebra)
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize
import Catlab.Operators.Amalgamate
import Catlab.Operators.Mirror
import Catlab.Library.Monoid

namespace CatLab.Library

-- ── Algebra half: Monoid with carrier H, mul/unit notation ────────────────
private def hopfAlgebra : Theory :=
  renameSort (renameGenerator TheoryOfMonoids [("μ","mul"),("η","unit")]) (.root "M") (.root "H")

-- ── Coalgebra half: mirror(Monoid) with carrier H, comul/counit notation ─
-- mirror reverses axiom paths, giving proper coassociativity and counit laws
private def hopfCoalgebra : Theory :=
  renameSort (renameGenerator (mirror TheoryOfMonoids) [("μ","comul"),("η","counit")]) (.root "M") (.root "H")

-- ── Bialgebra: amalgamate both halves over shared carrier H ───────────────
private def hopfBialgebra : Theory :=
  addBialgebraAxioms
    (amalgamateOver hopfAlgebra hopfCoalgebra [(.root "H", .root "H")])
    "mul" "unit" "comul" "counit"

/-- The theory of Hopf algebras: a bialgebra (algebra + compatible coalgebra)
    with an antipode S : H → H satisfying  μ∘(S⊗id)∘Δ = η∘ε = μ∘(id⊗S)∘Δ. -/
def TheoryOfHopfAlgebra : Theory :=
  { addAntipode hopfBialgebra "mul" "unit" "comul" "counit" with
    name     := "HopfAlgebra"
    doctrine := { doctrine := .SymmetricMonoidal } }

end CatLab.Library
