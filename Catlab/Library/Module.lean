/-
  CatLab -- Theory of Modules
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfModules (ringName : String := "R") : Theory :=
  let R := Expr.atom (gid ringName)
  let MO := Expr.atom (gid "M")
  { name := s!"{ringName}-Module"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := gid ringName, description := "The scalar ring" },
      { id := gid "M", description := "The module" }
    ]
    morphisms := [
      { id := gid "add", domain := .prod MO MO, codomain := MO,
        description := "Module addition: M × M → M" },
      { id := gid "zero", domain := .terminal, codomain := MO,
        description := "Zero vector: 1 → M" },
      { id := gid "neg", domain := MO, codomain := MO,
        description := "Negation: M → M" },
      { id := gid "smul", domain := .prod R MO, codomain := MO,
        description := s!"Scalar multiplication: {ringName} × M → M" },
      { id := gid "swap", domain := .prod MO MO, codomain := .prod MO MO,
        description := "Symmetry: M × M → M × M" }
    ]
    axioms := [
      { id := gid "add_assoc"
        leftPath := .comp (.prod (.atom (gid "add")) (.id MO)) (.atom (gid "add"))
        rightPath := .comp (.prod (.id MO) (.atom (gid "add"))) (.atom (gid "add"))
        description := "Addition is associative" },
      { id := gid "add_comm"
        leftPath := .atom (gid "add")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "add"))
        description := "Addition is commutative" },
      { id := gid "smul_distrib"
        leftPath := .comp (.prod (.id R) (.atom (gid "add"))) (.atom (gid "smul"))
        rightPath := .comp (.prod (.atom (gid "smul")) (.atom (gid "smul"))) (.atom (gid "add"))
        description := "Scalar distributes over addition: r(a+b) = ra + rb" },
      { id := gid "smul_assoc"
        leftPath := .comp (.prod (.atom (gid "mul")) (.id MO)) (.atom (gid "smul"))
        rightPath := .comp (.prod (.id R) (.atom (gid "smul"))) (.atom (gid "smul"))
        description := "Scalar associativity: (rs)m = r(sm)" }
    ] }

end CatLab.Library
