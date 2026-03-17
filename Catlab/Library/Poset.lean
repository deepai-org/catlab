/-
  CatLab -- Theory of Posets
-/

import Catlab.Core.Theory

namespace CatLab.Library

private def P : Expr := .atom (gid "P")

def TheoryOfPosets : Theory :=
  { name := "Poset"
    doctrine := { doctrine := .Category }
    objects := [{ id := gid "P", description := "The carrier set" }]
    morphisms := [
      { id := gid "≤", domain := .prod P P, codomain := P,
        description := "Partial order: P × P → Prop (represented as P)" }
    ]
    axioms := [
      { id := gid "refl"
        leftPath := .comp (.prod (.id P) (.id P)) (.atom (gid "≤"))
        rightPath := .id P
        description := "Reflexivity: a ≤ a" },
      { id := gid "antisym"
        leftPath := .comp (.prod (.atom (gid "≤")) (.atom (gid "≤"))) (.atom (gid "eq"))
        rightPath := .id P
        description := "Antisymmetry: a ≤ b ∧ b ≤ a → a = b" },
      { id := gid "trans"
        leftPath := .comp (.prod (.atom (gid "≤")) (.atom (gid "≤"))) (.atom (gid "≤"))
        rightPath := .atom (gid "≤")
        description := "Transitivity: a ≤ b ∧ b ≤ c → a ≤ c" }
    ] }

end CatLab.Library
