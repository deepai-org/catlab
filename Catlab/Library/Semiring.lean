/-
  CatLab — Theory of Semirings

  Derived via amalgamation of additive and multiplicative structures:

    Semiring = amalgamateOver(AdditiveCommMonoid, MultiplicativeMonoid)
               + addDistributivity("mul", "add")
               + addAnnihilator("mul", "zero")

  Unlike Ring, the additive structure is a commutative monoid (no inverse).
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize
import Catlab.Operators.Amalgamate
import Catlab.Library.Monoid

namespace CatLab.Library

-- ── Additive commutative monoid: Monoid → rename to additive notation ─────
private def additiveCommMonoid : Theory :=
  renameSort
    (renameGenerator
      (addCommutativity TheoryOfMonoids "μ")
      [("μ", "add"), ("η", "zero")])
    (.root "M") (.root "S")

-- ── Multiplicative monoid: Monoid renamed to mul/one ──────────────────────
private def semMulMonoid : Theory :=
  renameSort
    (renameGenerator TheoryOfMonoids [("μ", "mul"), ("η", "one")])
    (.root "M") (.root "S")

/-- The theory of semirings: additively a commutative monoid, multiplicatively
    a monoid, with distributivity and zero-annihilation (0 · a = 0). -/
def TheoryOfSemirings : Theory :=
  let base := amalgamateOver additiveCommMonoid semMulMonoid
                [(.root "S", .root "S")]
  let withDistrib := addDistributivity base "mul" "add"
  { addAnnihilator withDistrib "mul" "zero" with
    name     := "Semiring"
    doctrine := { doctrine := .LawvereTheory } }

end CatLab.Library
