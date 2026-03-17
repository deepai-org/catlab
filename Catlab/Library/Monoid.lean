/-
  CatLab — Theory of Monoids

  The Lawvere theory of monoids: one sort M, a binary operation μ : M × M → M,
  a unit η : 1 → M, satisfying associativity and unit laws.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def M : Expr := .atom (gid "M")

def TheoryOfMonoids : Theory :=
  { name := "Monoid"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := gid "M", description := "The carrier set" }
    ]
    morphisms := [
      { id := gid "μ"
        domain := .prod M M
        codomain := M
        description := "Multiplication: M × M → M" },
      { id := gid "η"
        domain := .terminal
        codomain := M
        description := "Unit: 1 → M" }
    ]
    axioms := [
      { id := gid "assoc"
        leftPath := .comp (.prod (.atom (gid "μ")) (.id M)) (.atom (gid "μ"))
        rightPath := .comp (.prod (.id M) (.atom (gid "μ"))) (.atom (gid "μ"))
        description := "Associativity: μ(μ(a,b),c) = μ(a,μ(b,c))" },
      { id := gid "left_unit"
        leftPath := .comp (.prod (.atom (gid "η")) (.id M)) (.atom (gid "μ"))
        rightPath := .id M
        description := "Left unit: μ(η,a) = a" },
      { id := gid "right_unit"
        leftPath := .comp (.prod (.id M) (.atom (gid "η"))) (.atom (gid "μ"))
        rightPath := .id M
        description := "Right unit: μ(a,η) = a" }
    ] }

end CatLab.Library
