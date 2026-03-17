/-
  CatLab -- Theory of Posets
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def P : Expr := .atom ⟨"P", 0⟩

def TheoryOfPosets : Theory :=
  { name := "Poset"
    doctrine := { doctrine := .Category }
    objects := [{ id := ⟨"P", 0⟩, description := "The carrier set" }]
    morphisms := [
      { id := ⟨"≤", 0⟩, domain := .prod P P, codomain := P,
        description := "Partial order: P × P → Prop (represented as P)" }
    ]
    axioms := [
      { id := ⟨"refl", 0⟩
        leftPath := .comp (.prod (.id P) (.id P)) (.atom ⟨"≤", 0⟩)
        rightPath := .id P
        description := "Reflexivity: a ≤ a" },
      { id := ⟨"antisym", 0⟩
        leftPath := .comp (.prod (.atom ⟨"≤", 0⟩) (.atom ⟨"≤", 0⟩)) (.atom ⟨"eq", 0⟩)
        rightPath := .id P
        description := "Antisymmetry: a ≤ b ∧ b ≤ a → a = b" },
      { id := ⟨"trans", 0⟩
        leftPath := .comp (.prod (.atom ⟨"≤", 0⟩) (.atom ⟨"≤", 0⟩)) (.atom ⟨"≤", 0⟩)
        rightPath := .atom ⟨"≤", 0⟩
        description := "Transitivity: a ≤ b ∧ b ≤ c → a ≤ c" }
    ] }

end CatLab.Library
