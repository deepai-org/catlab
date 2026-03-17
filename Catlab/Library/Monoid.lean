/-
  CatLab — Theory of Monoids

  The Lawvere theory of monoids: one sort M, a binary operation μ : M × M → M,
  a unit η : 1 → M, satisfying associativity and unit laws.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def M : Expr := .atom ⟨"M", 0⟩

def TheoryOfMonoids : Theory :=
  { name := "Monoid"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := ⟨"M", 0⟩, description := "The carrier set" }
    ]
    morphisms := [
      { id := ⟨"μ", 0⟩
        domain := .prod M M
        codomain := M
        description := "Multiplication: M × M → M" },
      { id := ⟨"η", 0⟩
        domain := .terminal
        codomain := M
        description := "Unit: 1 → M" }
    ]
    axioms := [
      { id := ⟨"assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"μ", 0⟩) (.id M)) (.atom ⟨"μ", 0⟩)
        rightPath := .comp (.prod (.id M) (.atom ⟨"μ", 0⟩)) (.atom ⟨"μ", 0⟩)
        description := "Associativity: μ(μ(a,b),c) = μ(a,μ(b,c))" },
      { id := ⟨"left_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"η", 0⟩) (.id M)) (.atom ⟨"μ", 0⟩)
        rightPath := .id M
        description := "Left unit: μ(η,a) = a" },
      { id := ⟨"right_unit", 0⟩
        leftPath := .comp (.prod (.id M) (.atom ⟨"η", 0⟩)) (.atom ⟨"μ", 0⟩)
        rightPath := .id M
        description := "Right unit: μ(a,η) = a" }
    ] }

end CatLab.Library
