/-
  CatLab -- Theory of Semirings
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def S : Expr := .atom (gid "S")

def TheoryOfSemirings : Theory :=
  { name := "Semiring"
    doctrine := { doctrine := .LawvereTheory }
    objects := [{ id := gid "S", description := "The carrier set" }]
    morphisms := [
      { id := gid "add", domain := .prod S S, codomain := S,
        description := "Addition: S × S → S" },
      { id := gid "zero", domain := .terminal, codomain := S,
        description := "Additive unit: 1 → S" },
      { id := gid "mul", domain := .prod S S, codomain := S,
        description := "Multiplication: S × S → S" },
      { id := gid "one", domain := .terminal, codomain := S,
        description := "Multiplicative unit: 1 → S" },
      { id := gid "swap", domain := .prod S S, codomain := .prod S S,
        description := "Symmetry: S × S → S × S" }
    ]
    axioms := [
      { id := gid "add_assoc"
        leftPath := .comp (.prod (.atom (gid "add")) (.id S)) (.atom (gid "add"))
        rightPath := .comp (.prod (.id S) (.atom (gid "add"))) (.atom (gid "add"))
        description := "Addition is associative" },
      { id := gid "add_comm"
        leftPath := .atom (gid "add")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "add"))
        description := "Addition is commutative" },
      { id := gid "add_unit"
        leftPath := .comp (.prod (.atom (gid "zero")) (.id S)) (.atom (gid "add"))
        rightPath := .id S
        description := "0 + a = a" },
      { id := gid "mul_assoc"
        leftPath := .comp (.prod (.atom (gid "mul")) (.id S)) (.atom (gid "mul"))
        rightPath := .comp (.prod (.id S) (.atom (gid "mul"))) (.atom (gid "mul"))
        description := "Multiplication is associative" },
      { id := gid "mul_unit"
        leftPath := .comp (.prod (.atom (gid "one")) (.id S)) (.atom (gid "mul"))
        rightPath := .id S
        description := "1 * a = a" },
      { id := gid "left_distrib"
        leftPath := .comp (.prod (.id S) (.atom (gid "add"))) (.atom (gid "mul"))
        rightPath := .comp (.prod (.atom (gid "mul")) (.atom (gid "mul"))) (.atom (gid "add"))
        description := "Left distributivity" },
      { id := gid "left_annihilate"
        leftPath := .comp (.prod (.atom (gid "zero")) (.id S)) (.atom (gid "mul"))
        rightPath := .atom (gid "zero")
        description := "0 * a = 0" }
    ] }

end CatLab.Library
