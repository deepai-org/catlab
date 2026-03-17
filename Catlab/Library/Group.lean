/-
  CatLab — Theory of Groups and Abelian Groups
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def G : Expr := .atom ⟨"G", 0⟩

def TheoryOfGroups : Theory :=
  { name := "Group"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := ⟨"G", 0⟩, description := "The carrier set" }
    ]
    morphisms := [
      { id := ⟨"μ", 0⟩, domain := .prod G G, codomain := G,
        description := "Multiplication: G × G → G" },
      { id := ⟨"η", 0⟩, domain := .terminal, codomain := G,
        description := "Unit: 1 → G" },
      { id := ⟨"ι", 0⟩, domain := G, codomain := G,
        description := "Inverse: G → G" },
      { id := ⟨"swap", 0⟩, domain := .prod G G, codomain := .prod G G,
        description := "Symmetry: G × G → G × G" }
    ]
    axioms := [
      { id := ⟨"assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"μ", 0⟩) (.id G)) (.atom ⟨"μ", 0⟩)
        rightPath := .comp (.prod (.id G) (.atom ⟨"μ", 0⟩)) (.atom ⟨"μ", 0⟩)
        description := "Associativity" },
      { id := ⟨"left_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"η", 0⟩) (.id G)) (.atom ⟨"μ", 0⟩)
        rightPath := .id G
        description := "Left unit" },
      { id := ⟨"right_unit", 0⟩
        leftPath := .comp (.prod (.id G) (.atom ⟨"η", 0⟩)) (.atom ⟨"μ", 0⟩)
        rightPath := .id G
        description := "Right unit" },
      { id := ⟨"left_inverse", 0⟩
        leftPath := .comp (.prod (.atom ⟨"ι", 0⟩) (.id G)) (.atom ⟨"μ", 0⟩)
        rightPath := .atom ⟨"η", 0⟩
        description := "Left inverse: μ(ι(a), a) = η" },
      { id := ⟨"right_inverse", 0⟩
        leftPath := .comp (.prod (.id G) (.atom ⟨"ι", 0⟩)) (.atom ⟨"μ", 0⟩)
        rightPath := .atom ⟨"η", 0⟩
        description := "Right inverse: μ(a, ι(a)) = η" }
    ] }

def TheoryOfAbelianGroups : Theory :=
  { TheoryOfGroups with
    name := "AbelianGroup"
    axioms := TheoryOfGroups.axioms ++ [
      { id := ⟨"comm", 0⟩
        leftPath := .atom ⟨"μ", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"μ", 0⟩)
        description := "Commutativity: μ(a,b) = μ(b,a)" }
    ] }

end CatLab.Library
