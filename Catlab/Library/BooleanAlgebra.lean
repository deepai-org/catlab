/-
  CatLab -- Theory of Boolean Algebras

  The theory of Boolean algebras: a complemented distributive lattice.
  Mirror(BooleanAlgebra) ≅ Stone Spaces (Stone Duality).
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def B : Expr := .atom (gid "B")

def TheoryOfBooleanAlgebra : Theory :=
  { name := "BooleanAlgebra"
    doctrine := { doctrine := .CartesianClosed }
    objects := [
      { id := gid "B", description := "The carrier lattice" }
    ]
    morphisms := [
      { id := gid "∧", domain := .prod B B, codomain := B,
        description := "Meet (AND): B × B → B" },
      { id := gid "∨", domain := .prod B B, codomain := B,
        description := "Join (OR): B × B → B" },
      { id := gid "¬", domain := B, codomain := B,
        description := "Complement (NOT): B → B" },
      { id := gid "⊤", domain := .terminal, codomain := B,
        description := "Top (TRUE): 1 → B" },
      { id := gid "⊥", domain := .terminal, codomain := B,
        description := "Bottom (FALSE): 1 → B" },
      { id := gid "swap", domain := .prod B B, codomain := .prod B B,
        description := "Symmetry: B × B → B × B" }
    ]
    axioms := [
      { id := gid "meet_assoc"
        leftPath := .comp (.prod (.atom (gid "∧")) (.id B)) (.atom (gid "∧"))
        rightPath := .comp (.prod (.id B) (.atom (gid "∧"))) (.atom (gid "∧"))
        description := "Meet is associative" },
      { id := gid "meet_comm"
        leftPath := .atom (gid "∧")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "∧"))
        description := "Meet is commutative" },
      { id := gid "join_assoc"
        leftPath := .comp (.prod (.atom (gid "∨")) (.id B)) (.atom (gid "∨"))
        rightPath := .comp (.prod (.id B) (.atom (gid "∨"))) (.atom (gid "∨"))
        description := "Join is associative" },
      { id := gid "join_comm"
        leftPath := .atom (gid "∨")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "∨"))
        description := "Join is commutative" },
      { id := gid "absorption_1"
        leftPath := .comp (.prod (.id B) (.atom (gid "∨"))) (.atom (gid "∧"))
        rightPath := .id B
        description := "Absorption: a ∧ (a ∨ b) = a" },
      { id := gid "absorption_2"
        leftPath := .comp (.prod (.id B) (.atom (gid "∧"))) (.atom (gid "∨"))
        rightPath := .id B
        description := "Absorption: a ∨ (a ∧ b) = a" },
      { id := gid "distribute"
        leftPath := .comp (.prod (.id B) (.atom (gid "∨"))) (.atom (gid "∧"))
        rightPath := .comp (.prod (.atom (gid "∧")) (.atom (gid "∧"))) (.atom (gid "∨"))
        description := "Distributivity: a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)" },
      { id := gid "complement"
        leftPath := .comp (.prod (.id B) (.atom (gid "¬"))) (.atom (gid "∧"))
        rightPath := .atom (gid "⊥")
        description := "Complement: a ∧ ¬a = ⊥" },
      { id := gid "excluded_middle"
        leftPath := .comp (.prod (.id B) (.atom (gid "¬"))) (.atom (gid "∨"))
        rightPath := .atom (gid "⊤")
        description := "Excluded middle: a ∨ ¬a = ⊤" }
    ] }

/-- The theory of Heyting algebras: like Boolean but without excluded middle.
    This is the internal logic of any topos. -/
def TheoryOfHeytingAlgebra : Theory :=
  { TheoryOfBooleanAlgebra with
    name := "HeytingAlgebra"
    -- Replace complement with implication; drop excluded middle
    morphisms := TheoryOfBooleanAlgebra.morphisms.filter (fun m => m.id.name != .root "¬") ++ [
      { id := gid "→", domain := .prod B B, codomain := B,
        description := "Implication (right adjoint to meet): B × B → B" }
    ]
    axioms := TheoryOfBooleanAlgebra.axioms.filter (fun a =>
      a.id.name != .root "complement" && a.id.name != .root "excluded_middle") ++ [
      { id := gid "adjunction"
        leftPath := .comp (.prod (.atom (gid "∧")) (.id B)) (.atom (gid "→"))
        rightPath := .atom (gid "→")
        description := "Heyting adjunction: a ∧ b ≤ c iff a ≤ b → c" }
    ] }

end CatLab.Library
