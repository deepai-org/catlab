/-
  CatLab -- Theory of Semirings
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def S : Expr := .atom ⟨"S", 0⟩

def TheoryOfSemirings : Theory :=
  { name := "Semiring"
    doctrine := { doctrine := .LawvereTheory }
    objects := [{ id := ⟨"S", 0⟩, description := "The carrier set" }]
    morphisms := [
      { id := ⟨"add", 0⟩, domain := .prod S S, codomain := S,
        description := "Addition: S × S → S" },
      { id := ⟨"zero", 0⟩, domain := .terminal, codomain := S,
        description := "Additive unit: 1 → S" },
      { id := ⟨"mul", 0⟩, domain := .prod S S, codomain := S,
        description := "Multiplication: S × S → S" },
      { id := ⟨"one", 0⟩, domain := .terminal, codomain := S,
        description := "Multiplicative unit: 1 → S" },
      { id := ⟨"swap", 0⟩, domain := .prod S S, codomain := .prod S S,
        description := "Symmetry: S × S → S × S" }
    ]
    axioms := [
      { id := ⟨"add_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"add", 0⟩) (.id S)) (.atom ⟨"add", 0⟩)
        rightPath := .comp (.prod (.id S) (.atom ⟨"add", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Addition is associative" },
      { id := ⟨"add_comm", 0⟩
        leftPath := .atom ⟨"add", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"add", 0⟩)
        description := "Addition is commutative" },
      { id := ⟨"add_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"zero", 0⟩) (.id S)) (.atom ⟨"add", 0⟩)
        rightPath := .id S
        description := "0 + a = a" },
      { id := ⟨"mul_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.id S)) (.atom ⟨"mul", 0⟩)
        rightPath := .comp (.prod (.id S) (.atom ⟨"mul", 0⟩)) (.atom ⟨"mul", 0⟩)
        description := "Multiplication is associative" },
      { id := ⟨"mul_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"one", 0⟩) (.id S)) (.atom ⟨"mul", 0⟩)
        rightPath := .id S
        description := "1 * a = a" },
      { id := ⟨"left_distrib", 0⟩
        leftPath := .comp (.prod (.id S) (.atom ⟨"add", 0⟩)) (.atom ⟨"mul", 0⟩)
        rightPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.atom ⟨"mul", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Left distributivity" },
      { id := ⟨"left_annihilate", 0⟩
        leftPath := .comp (.prod (.atom ⟨"zero", 0⟩) (.id S)) (.atom ⟨"mul", 0⟩)
        rightPath := .atom ⟨"zero", 0⟩
        description := "0 * a = 0" }
    ] }

end CatLab.Library
