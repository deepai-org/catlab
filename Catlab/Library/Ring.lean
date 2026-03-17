/-
  CatLab — Theory of Rings and Commutative Rings

  Derived via amalgamation of additive and multiplicative structures:

    Ring  = amalgamateOver(AdditiveAbelianGroup, MultiplicativeMonoid)
            + addDistributivity("mul", "add")

  where AdditiveAbelianGroup = AbelianGroup renamed to additive notation (add/zero/neg)
    and MultiplicativeMonoid = Monoid renamed to multiplicative notation (mul/one).

  CommutativeRing = addCommutativity(Ring, "mul")
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize
import Catlab.Operators.Amalgamate
import Catlab.Library.Monoid

namespace CatLab.Library

-- ── Additive abelian group: Monoid → Group → AbelianGroup → rename ────────
private def additiveAbelianGroup : Theory :=
  renameSort
    (renameGenerator
      (addCommutativity (addInverse TheoryOfMonoids "μ" "η") "μ")
      [ ("μ",     "add")   -- multiplication ↦ addition
      , ("η",     "zero")  -- unit ↦ zero
      , ("μ_inv", "neg")   -- inverse ↦ negation
      ])
    (.root "M") (.root "R")

-- ── Multiplicative monoid: Monoid renamed to mul/one ──────────────────────
private def multiplicativeMonoid : Theory :=
  renameSort
    (renameGenerator TheoryOfMonoids [("μ", "mul"), ("η", "one")])
    (.root "M") (.root "R")

-- ── Ring = amalgamate over carrier R + distributivity ────────────────────

/-- The theory of rings: additively an abelian group, multiplicatively a monoid,
    with left and right distributivity of multiplication over addition. -/
def TheoryOfRings : Theory :=
  let base := amalgamateOver additiveAbelianGroup multiplicativeMonoid
                [(.root "R", .root "R")]  -- identify both carriers as R
  { addDistributivity base "mul" "add" with
    name     := "Ring"
    doctrine := { doctrine := .LawvereTheory } }

/-- The theory of commutative rings: Ring + commutativity of multiplication. -/
def TheoryOfCommutativeRings : Theory :=
  { addCommutativity TheoryOfRings "mul" with
    name := "CommutativeRing" }

end CatLab.Library
