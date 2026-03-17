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

private def R : Expr := .atom ⟨"R", 0⟩

/-- The theory of rings, constructed by hand.
    In practice, `tensorTheories TheoryOfMonoids TheoryOfAbelianGroups`
    would generate this (modulo naming). -/
def TheoryOfRings : Theory :=
  { name := "Ring"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := ⟨"R", 0⟩, description := "The carrier set" }
    ]
    morphisms := [
      -- Multiplicative monoid structure
      { id := ⟨"mul", 0⟩, domain := .prod R R, codomain := R,
        description := "Multiplication: R × R → R" },
      { id := ⟨"one", 0⟩, domain := .terminal, codomain := R,
        description := "Multiplicative unit: 1 → R" },
      -- Additive abelian group structure
      { id := ⟨"add", 0⟩, domain := .prod R R, codomain := R,
        description := "Addition: R × R → R" },
      { id := ⟨"zero", 0⟩, domain := .terminal, codomain := R,
        description := "Additive unit: 1 → R" },
      { id := ⟨"neg", 0⟩, domain := R, codomain := R,
        description := "Additive inverse: R → R" }
    ]
    axioms := [
      -- Multiplicative monoid axioms
      { id := ⟨"mul_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.id R)) (.atom ⟨"mul", 0⟩)
        rightPath := .comp (.prod (.id R) (.atom ⟨"mul", 0⟩)) (.atom ⟨"mul", 0⟩)
        description := "Multiplication is associative" },
      { id := ⟨"mul_left_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"one", 0⟩) (.id R)) (.atom ⟨"mul", 0⟩)
        rightPath := .id R
        description := "1 * a = a" },
      { id := ⟨"mul_right_unit", 0⟩
        leftPath := .comp (.prod (.id R) (.atom ⟨"one", 0⟩)) (.atom ⟨"mul", 0⟩)
        rightPath := .id R
        description := "a * 1 = a" },
      -- Additive abelian group axioms
      { id := ⟨"add_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"add", 0⟩) (.id R)) (.atom ⟨"add", 0⟩)
        rightPath := .comp (.prod (.id R) (.atom ⟨"add", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Addition is associative" },
      { id := ⟨"add_comm", 0⟩
        leftPath := .atom ⟨"add", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"add", 0⟩)
        description := "Addition is commutative" },
      { id := ⟨"add_left_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"zero", 0⟩) (.id R)) (.atom ⟨"add", 0⟩)
        rightPath := .id R
        description := "0 + a = a" },
      { id := ⟨"add_left_inverse", 0⟩
        leftPath := .comp (.prod (.atom ⟨"neg", 0⟩) (.id R)) (.atom ⟨"add", 0⟩)
        rightPath := .atom ⟨"zero", 0⟩
        description := "(-a) + a = 0" },
      -- Distributivity: the interchange law from the tensor product
      { id := ⟨"left_distrib", 0⟩
        leftPath := .comp (.prod (.id R) (.atom ⟨"add", 0⟩)) (.atom ⟨"mul", 0⟩)
        rightPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.atom ⟨"mul", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Left distributivity: a * (b + c) = a*b + a*c" },
      { id := ⟨"right_distrib", 0⟩
        leftPath := .comp (.prod (.atom ⟨"add", 0⟩) (.id R)) (.atom ⟨"mul", 0⟩)
        rightPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.atom ⟨"mul", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Right distributivity: (a + b) * c = a*c + b*c" }
    ] }

/-- The theory of commutative rings: Ring + commutativity of multiplication -/
def TheoryOfCommutativeRings : Theory :=
  { TheoryOfRings with
    name := "CommutativeRing"
    axioms := TheoryOfRings.axioms ++ [
      { id := ⟨"mul_comm", 0⟩
        leftPath := .atom ⟨"mul", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"mul", 0⟩)
        description := "Multiplication is commutative" }
    ] }

end CatLab.Library
