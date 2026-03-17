/-
  CatLab — Theory of Groups and Abelian Groups
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def G : Expr := .atom (gid "G")

def TheoryOfGroups : Theory :=
  { name := "Group"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := gid "G", description := "The carrier set" }
    ]
    morphisms := [
      { id := gid "μ", domain := .prod G G, codomain := G,
        description := "Multiplication: G × G → G" },
      { id := gid "η", domain := .terminal, codomain := G,
        description := "Unit: 1 → G" },
      { id := gid "ι", domain := G, codomain := G,
        description := "Inverse: G → G" },
      { id := gid "swap", domain := .prod G G, codomain := .prod G G,
        description := "Symmetry: G × G → G × G" }
    ]
    axioms := [
      { id := gid "assoc"
        leftPath := .comp (.prod (.atom (gid "μ")) (.id G)) (.atom (gid "μ"))
        rightPath := .comp (.prod (.id G) (.atom (gid "μ"))) (.atom (gid "μ"))
        description := "Associativity" },
      { id := gid "left_unit"
        leftPath := .comp (.prod (.atom (gid "η")) (.id G)) (.atom (gid "μ"))
        rightPath := .id G
        description := "Left unit" },
      { id := gid "right_unit"
        leftPath := .comp (.prod (.id G) (.atom (gid "η"))) (.atom (gid "μ"))
        rightPath := .id G
        description := "Right unit" },
      { id := gid "left_inverse"
        leftPath := .comp (.prod (.atom (gid "ι")) (.id G)) (.atom (gid "μ"))
        rightPath := .atom (gid "η")
        description := "Left inverse: μ(ι(a), a) = η" },
      { id := gid "right_inverse"
        leftPath := .comp (.prod (.id G) (.atom (gid "ι"))) (.atom (gid "μ"))
        rightPath := .atom (gid "η")
        description := "Right inverse: μ(a, ι(a)) = η" }
    ] }

def TheoryOfAbelianGroups : Theory :=
  { TheoryOfGroups with
    name := "AbelianGroup"
    axioms := TheoryOfGroups.axioms ++ [
      { id := gid "comm"
        leftPath := .atom (gid "μ")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "μ"))
        description := "Commutativity: μ(a,b) = μ(b,a)" }
    ] }

end CatLab.Library
