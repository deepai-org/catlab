/-
  CatLab -- Theory of Lattices
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def L : Expr := .atom ⟨"L", 0⟩

def TheoryOfLattices : Theory :=
  { name := "Lattice"
    doctrine := { doctrine := .CartesianCategory }
    objects := [{ id := ⟨"L", 0⟩, description := "The carrier lattice" }]
    morphisms := [
      { id := ⟨"∧", 0⟩, domain := .prod L L, codomain := L,
        description := "Meet: L × L → L" },
      { id := ⟨"∨", 0⟩, domain := .prod L L, codomain := L,
        description := "Join: L × L → L" },
      { id := ⟨"swap", 0⟩, domain := .prod L L, codomain := .prod L L,
        description := "Symmetry: L × L → L × L" }
    ]
    axioms := [
      { id := ⟨"meet_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∧", 0⟩) (.id L)) (.atom ⟨"∧", 0⟩)
        rightPath := .comp (.prod (.id L) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∧", 0⟩)
        description := "Meet is associative" },
      { id := ⟨"meet_comm", 0⟩
        leftPath := .atom ⟨"∧", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∧", 0⟩)
        description := "Meet is commutative" },
      { id := ⟨"meet_idem", 0⟩
        leftPath := .comp (.prod (.id L) (.id L)) (.atom ⟨"∧", 0⟩)
        rightPath := .id L
        description := "Meet is idempotent: a ∧ a = a" },
      { id := ⟨"join_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∨", 0⟩) (.id L)) (.atom ⟨"∨", 0⟩)
        rightPath := .comp (.prod (.id L) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∨", 0⟩)
        description := "Join is associative" },
      { id := ⟨"join_comm", 0⟩
        leftPath := .atom ⟨"∨", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∨", 0⟩)
        description := "Join is commutative" },
      { id := ⟨"join_idem", 0⟩
        leftPath := .comp (.prod (.id L) (.id L)) (.atom ⟨"∨", 0⟩)
        rightPath := .id L
        description := "Join is idempotent: a ∨ a = a" },
      { id := ⟨"absorption_1", 0⟩
        leftPath := .comp (.prod (.id L) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∧", 0⟩)
        rightPath := .id L
        description := "Absorption: a ∧ (a ∨ b) = a" },
      { id := ⟨"absorption_2", 0⟩
        leftPath := .comp (.prod (.id L) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∨", 0⟩)
        rightPath := .id L
        description := "Absorption: a ∨ (a ∧ b) = a" }
    ] }

end CatLab.Library
