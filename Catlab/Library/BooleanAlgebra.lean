/-
  CatLab -- Theory of Boolean Algebras

  The theory of Boolean algebras: a complemented distributive lattice.
  Mirror(BooleanAlgebra) ≅ Stone Spaces (Stone Duality).
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def B : Expr := .atom ⟨"B", 0⟩

def TheoryOfBooleanAlgebra : Theory :=
  { name := "BooleanAlgebra"
    doctrine := { doctrine := .CartesianClosed }
    objects := [
      { id := ⟨"B", 0⟩, description := "The carrier lattice" }
    ]
    morphisms := [
      { id := ⟨"∧", 0⟩, domain := .prod B B, codomain := B,
        description := "Meet (AND): B × B → B" },
      { id := ⟨"∨", 0⟩, domain := .prod B B, codomain := B,
        description := "Join (OR): B × B → B" },
      { id := ⟨"¬", 0⟩, domain := B, codomain := B,
        description := "Complement (NOT): B → B" },
      { id := ⟨"⊤", 0⟩, domain := .terminal, codomain := B,
        description := "Top (TRUE): 1 → B" },
      { id := ⟨"⊥", 0⟩, domain := .terminal, codomain := B,
        description := "Bottom (FALSE): 1 → B" }
    ]
    axioms := [
      { id := ⟨"meet_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∧", 0⟩) (.id B)) (.atom ⟨"∧", 0⟩)
        rightPath := .comp (.prod (.id B) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∧", 0⟩)
        description := "Meet is associative" },
      { id := ⟨"meet_comm", 0⟩
        leftPath := .atom ⟨"∧", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∧", 0⟩)
        description := "Meet is commutative" },
      { id := ⟨"join_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∨", 0⟩) (.id B)) (.atom ⟨"∨", 0⟩)
        rightPath := .comp (.prod (.id B) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∨", 0⟩)
        description := "Join is associative" },
      { id := ⟨"join_comm", 0⟩
        leftPath := .atom ⟨"∨", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∨", 0⟩)
        description := "Join is commutative" },
      { id := ⟨"absorption_1", 0⟩
        leftPath := .comp (.prod (.id B) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∧", 0⟩)
        rightPath := .id B
        description := "Absorption: a ∧ (a ∨ b) = a" },
      { id := ⟨"absorption_2", 0⟩
        leftPath := .comp (.prod (.id B) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∨", 0⟩)
        rightPath := .id B
        description := "Absorption: a ∨ (a ∧ b) = a" },
      { id := ⟨"distribute", 0⟩
        leftPath := .comp (.prod (.id B) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∧", 0⟩)
        rightPath := .comp (.prod (.atom ⟨"∧", 0⟩) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∨", 0⟩)
        description := "Distributivity: a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)" },
      { id := ⟨"complement", 0⟩
        leftPath := .comp (.prod (.id B) (.atom ⟨"¬", 0⟩)) (.atom ⟨"∧", 0⟩)
        rightPath := .atom ⟨"⊥", 0⟩
        description := "Complement: a ∧ ¬a = ⊥" },
      { id := ⟨"excluded_middle", 0⟩
        leftPath := .comp (.prod (.id B) (.atom ⟨"¬", 0⟩)) (.atom ⟨"∨", 0⟩)
        rightPath := .atom ⟨"⊤", 0⟩
        description := "Excluded middle: a ∨ ¬a = ⊤" }
    ] }

/-- The theory of Heyting algebras: like Boolean but without excluded middle.
    This is the internal logic of any topos. -/
def TheoryOfHeytingAlgebra : Theory :=
  { TheoryOfBooleanAlgebra with
    name := "HeytingAlgebra"
    -- Replace complement with implication; drop excluded middle
    morphisms := TheoryOfBooleanAlgebra.morphisms.filter (fun m => m.id.name != "¬") ++ [
      { id := ⟨"→", 0⟩, domain := .prod B B, codomain := B,
        description := "Implication (right adjoint to meet): B × B → B" }
    ]
    axioms := TheoryOfBooleanAlgebra.axioms.filter (fun a =>
      a.id.name != "complement" && a.id.name != "excluded_middle") ++ [
      { id := ⟨"adjunction", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∧", 0⟩) (.id B)) (.atom ⟨"→", 0⟩)
        rightPath := .atom ⟨"→", 0⟩
        description := "Heyting adjunction: a ∧ b ≤ c iff a ≤ b → c" }
    ] }

end CatLab.Library
