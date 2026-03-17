/-
  CatLab — Theory of Rings (and Commutative Rings)

  A ring is what you get from Tensor(Monoids, AbelianGroups) —
  the tensor product of theories via Eckmann-Hilton.
-/

import Catlab.Core.Theory
import Catlab.Operators.DayConvolution
import Catlab.Library.Monoid
import Catlab.Library.Group

namespace CatLab.Library

private def R : Expr := .atom (gid "R")

/-- The theory of rings, constructed by hand.
    In practice, `tensorTheories TheoryOfMonoids TheoryOfAbelianGroups`
    would generate this (modulo naming). -/
def TheoryOfRings : Theory :=
  { name := "Ring"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := gid "R", description := "The carrier set" }
    ]
    morphisms := [
      -- Multiplicative monoid structure
      { id := gid "mul", domain := .prod R R, codomain := R,
        description := "Multiplication: R × R → R" },
      { id := gid "one", domain := .terminal, codomain := R,
        description := "Multiplicative unit: 1 → R" },
      -- Additive abelian group structure
      { id := gid "add", domain := .prod R R, codomain := R,
        description := "Addition: R × R → R" },
      { id := gid "zero", domain := .terminal, codomain := R,
        description := "Additive unit: 1 → R" },
      { id := gid "neg", domain := R, codomain := R,
        description := "Additive inverse: R → R" },
      { id := gid "swap", domain := .prod R R, codomain := .prod R R,
        description := "Symmetry: R × R → R × R" }
    ]
    axioms := [
      -- Multiplicative monoid axioms
      { id := gid "mul_assoc"
        leftPath := .comp (.prod (.atom (gid "mul")) (.id R)) (.atom (gid "mul"))
        rightPath := .comp (.prod (.id R) (.atom (gid "mul"))) (.atom (gid "mul"))
        description := "Multiplication is associative" },
      { id := gid "mul_left_unit"
        leftPath := .comp (.prod (.atom (gid "one")) (.id R)) (.atom (gid "mul"))
        rightPath := .id R
        description := "1 * a = a" },
      { id := gid "mul_right_unit"
        leftPath := .comp (.prod (.id R) (.atom (gid "one"))) (.atom (gid "mul"))
        rightPath := .id R
        description := "a * 1 = a" },
      -- Additive abelian group axioms
      { id := gid "add_assoc"
        leftPath := .comp (.prod (.atom (gid "add")) (.id R)) (.atom (gid "add"))
        rightPath := .comp (.prod (.id R) (.atom (gid "add"))) (.atom (gid "add"))
        description := "Addition is associative" },
      { id := gid "add_comm"
        leftPath := .atom (gid "add")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "add"))
        description := "Addition is commutative" },
      { id := gid "add_left_unit"
        leftPath := .comp (.prod (.atom (gid "zero")) (.id R)) (.atom (gid "add"))
        rightPath := .id R
        description := "0 + a = a" },
      { id := gid "add_left_inverse"
        leftPath := .comp (.prod (.atom (gid "neg")) (.id R)) (.atom (gid "add"))
        rightPath := .atom (gid "zero")
        description := "(-a) + a = 0" },
      -- Distributivity: the interchange law from the tensor product
      { id := gid "left_distrib"
        leftPath := .comp (.prod (.id R) (.atom (gid "add"))) (.atom (gid "mul"))
        rightPath := .comp (.prod (.atom (gid "mul")) (.atom (gid "mul"))) (.atom (gid "add"))
        description := "Left distributivity: a * (b + c) = a*b + a*c" },
      { id := gid "right_distrib"
        leftPath := .comp (.prod (.atom (gid "add")) (.id R)) (.atom (gid "mul"))
        rightPath := .comp (.prod (.atom (gid "mul")) (.atom (gid "mul"))) (.atom (gid "add"))
        description := "Right distributivity: (a + b) * c = a*c + b*c" }
    ] }

/-- The theory of commutative rings: Ring + commutativity of multiplication -/
def TheoryOfCommutativeRings : Theory :=
  { TheoryOfRings with
    name := "CommutativeRing"
    axioms := TheoryOfRings.axioms ++ [
      { id := gid "mul_comm"
        leftPath := .atom (gid "mul")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "mul"))
        description := "Multiplication is commutative" }
    ] }

end CatLab.Library
