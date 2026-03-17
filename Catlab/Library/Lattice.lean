/-
  CatLab -- Theory of Lattices
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def L : Expr := .atom (gid "L")

def TheoryOfLattices : Theory :=
  { name := "Lattice"
    doctrine := { doctrine := .CartesianCategory }
    objects := [{ id := gid "L", description := "The carrier lattice" }]
    morphisms := [
      { id := gid "∧", domain := .prod L L, codomain := L,
        description := "Meet: L × L → L" },
      { id := gid "∨", domain := .prod L L, codomain := L,
        description := "Join: L × L → L" },
      { id := gid "swap", domain := .prod L L, codomain := .prod L L,
        description := "Symmetry: L × L → L × L" }
    ]
    axioms := [
      { id := gid "meet_assoc"
        leftPath := .comp (.prod (.atom (gid "∧")) (.id L)) (.atom (gid "∧"))
        rightPath := .comp (.prod (.id L) (.atom (gid "∧"))) (.atom (gid "∧"))
        description := "Meet is associative" },
      { id := gid "meet_comm"
        leftPath := .atom (gid "∧")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "∧"))
        description := "Meet is commutative" },
      { id := gid "meet_idem"
        leftPath := .comp (.prod (.id L) (.id L)) (.atom (gid "∧"))
        rightPath := .id L
        description := "Meet is idempotent: a ∧ a = a" },
      { id := gid "join_assoc"
        leftPath := .comp (.prod (.atom (gid "∨")) (.id L)) (.atom (gid "∨"))
        rightPath := .comp (.prod (.id L) (.atom (gid "∨"))) (.atom (gid "∨"))
        description := "Join is associative" },
      { id := gid "join_comm"
        leftPath := .atom (gid "∨")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "∨"))
        description := "Join is commutative" },
      { id := gid "join_idem"
        leftPath := .comp (.prod (.id L) (.id L)) (.atom (gid "∨"))
        rightPath := .id L
        description := "Join is idempotent: a ∨ a = a" },
      { id := gid "absorption_1"
        leftPath := .comp (.prod (.id L) (.atom (gid "∨"))) (.atom (gid "∧"))
        rightPath := .id L
        description := "Absorption: a ∧ (a ∨ b) = a" },
      { id := gid "absorption_2"
        leftPath := .comp (.prod (.id L) (.atom (gid "∧"))) (.atom (gid "∨"))
        rightPath := .id L
        description := "Absorption: a ∨ (a ∧ b) = a" }
    ] }

end CatLab.Library
