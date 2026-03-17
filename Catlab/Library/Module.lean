/-
  CatLab -- Theory of Modules
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfModules (ringName : String := "R") : Theory :=
  let R := Expr.atom ⟨ringName, 0⟩
  let MO := Expr.atom ⟨"M", 0⟩
  { name := s!"{ringName}-Module"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := ⟨ringName, 0⟩, description := "The scalar ring" },
      { id := ⟨"M", 0⟩, description := "The module" }
    ]
    morphisms := [
      { id := ⟨"add", 0⟩, domain := .prod MO MO, codomain := MO,
        description := "Module addition: M × M → M" },
      { id := ⟨"zero", 0⟩, domain := .terminal, codomain := MO,
        description := "Zero vector: 1 → M" },
      { id := ⟨"neg", 0⟩, domain := MO, codomain := MO,
        description := "Negation: M → M" },
      { id := ⟨"smul", 0⟩, domain := .prod R MO, codomain := MO,
        description := s!"Scalar multiplication: {ringName} × M → M" },
      { id := ⟨"swap", 0⟩, domain := .prod MO MO, codomain := .prod MO MO,
        description := "Symmetry: M × M → M × M" }
    ]
    axioms := [
      { id := ⟨"add_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"add", 0⟩) (.id MO)) (.atom ⟨"add", 0⟩)
        rightPath := .comp (.prod (.id MO) (.atom ⟨"add", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Addition is associative" },
      { id := ⟨"add_comm", 0⟩
        leftPath := .atom ⟨"add", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"add", 0⟩)
        description := "Addition is commutative" },
      { id := ⟨"smul_distrib", 0⟩
        leftPath := .comp (.prod (.id R) (.atom ⟨"add", 0⟩)) (.atom ⟨"smul", 0⟩)
        rightPath := .comp (.prod (.atom ⟨"smul", 0⟩) (.atom ⟨"smul", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Scalar distributes over addition: r(a+b) = ra + rb" },
      { id := ⟨"smul_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.id MO)) (.atom ⟨"smul", 0⟩)
        rightPath := .comp (.prod (.id R) (.atom ⟨"smul", 0⟩)) (.atom ⟨"smul", 0⟩)
        description := "Scalar associativity: (rs)m = r(sm)" }
    ] }

end CatLab.Library
