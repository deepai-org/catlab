/-
  CatLab -- Theory of Heyting Algebras and Boolean Algebras

  Derivation order (mathematically correct):
    HeytingAlgebra  — primitive: bounded distributive lattice with → (implication)
    BooleanAlgebra  — derived:   booleanize(HeytingAlgebra)
                                 (adds involutive ¬ and ¬¬A = A / excluded middle)

  Every Boolean algebra is a Heyting algebra (with a → b := ¬a ∨ b).
  Stone Duality: Mirror(BooleanAlgebra) ≅ Stone Spaces.
-/

import Catlab.Core.Theory
import Catlab.Operators.Booleanize

namespace CatLab.Library

private def B : Expr := .atom (gid "B")

/-- The theory of Heyting algebras: a bounded distributive lattice with
    Heyting implication (right adjoint to meet).
    This is the internal logic of any elementary topos. -/
def TheoryOfHeytingAlgebra : Theory :=
  { name := "HeytingAlgebra"
    doctrine := { doctrine := .CartesianClosed }
    objects := [
      { id := gid "B", description := "The carrier lattice" }
    ]
    morphisms := [
      { id := gid "∧",    domain := .prod B B, codomain := B,
        description := "Meet (AND)" },
      { id := gid "∨",    domain := .prod B B, codomain := B,
        description := "Join (OR)" },
      { id := gid "→",    domain := .prod B B, codomain := B,
        description := "Heyting implication (right adjoint to meet)" },
      { id := gid "⊤",    domain := .terminal, codomain := B,
        description := "Top: 1 → B" },
      { id := gid "⊥",    domain := .terminal, codomain := B,
        description := "Bottom: 1 → B" },
      { id := gid "swap", domain := .prod B B, codomain := .prod B B,
        description := "Symmetry: B × B → B × B" }
    ]
    axioms := [
      { id := gid "meet_assoc"
        leftPath  := .comp (.prod (.atom (gid "∧")) (.id B)) (.atom (gid "∧"))
        rightPath := .comp (.prod (.id B) (.atom (gid "∧"))) (.atom (gid "∧"))
        description := "Meet is associative" },
      { id := gid "meet_comm"
        leftPath  := .atom (gid "∧")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "∧"))
        description := "Meet is commutative" },
      { id := gid "join_assoc"
        leftPath  := .comp (.prod (.atom (gid "∨")) (.id B)) (.atom (gid "∨"))
        rightPath := .comp (.prod (.id B) (.atom (gid "∨"))) (.atom (gid "∨"))
        description := "Join is associative" },
      { id := gid "join_comm"
        leftPath  := .atom (gid "∨")
        rightPath := .comp (.atom (gid "swap")) (.atom (gid "∨"))
        description := "Join is commutative" },
      { id := gid "absorption_meet"
        leftPath  := .comp (.prod (.id B) (.atom (gid "∨"))) (.atom (gid "∧"))
        rightPath := .id B
        description := "Absorption: a ∧ (a ∨ b) = a" },
      { id := gid "absorption_join"
        leftPath  := .comp (.prod (.id B) (.atom (gid "∧"))) (.atom (gid "∨"))
        rightPath := .id B
        description := "Absorption: a ∨ (a ∧ b) = a" },
      { id := gid "distribute"
        leftPath  := .comp (.prod (.id B) (.atom (gid "∨"))) (.atom (gid "∧"))
        rightPath := .comp (.prod (.atom (gid "∧")) (.atom (gid "∧"))) (.atom (gid "∨"))
        description := "Distributivity: a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)" },
      { id := gid "heyting_adjunction"
        leftPath  := .comp (.prod (.atom (gid "∧")) (.id B)) (.atom (gid "→"))
        rightPath := .atom (gid "→")
        description := "Heyting adjunction: (a ∧ b ≤ c) ↔ (a ≤ b → c)" },
      { id := gid "top_unit"
        leftPath  := .comp (.prod (.atom (gid "⊤")) (.id B)) (.atom (gid "∧"))
        rightPath := .id B
        description := "⊤ is unit for ∧" },
      { id := gid "bot_unit"
        leftPath  := .comp (.prod (.atom (gid "⊥")) (.id B)) (.atom (gid "∨"))
        rightPath := .id B
        description := "⊥ is unit for ∨" }
    ] }

/-- The theory of Boolean algebras, derived by booleanizing the Heyting algebra.
    `booleanize` adds involutive negation ¬ and double-negation elimination ¬¬a = a,
    equivalent to the law of excluded middle. -/
def TheoryOfBooleanAlgebra : Theory :=
  booleanize TheoryOfHeytingAlgebra

end CatLab.Library
