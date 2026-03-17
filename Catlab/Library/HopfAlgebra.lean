/-
  CatLab -- Hopf Algebras

  A Hopf algebra H over a field k is simultaneously:
    - An algebra    (H, μ, η)   : associative k-algebra with unit
    - A coalgebra   (H, Δ, ε)  : coassociative k-coalgebra with counit
    - A bialgebra              : Δ and ε are algebra morphisms (equivalently,
                                 μ and η are coalgebra morphisms)
    - An antipode  S : H → H   : satisfying  μ ∘ (S ⊗ id) ∘ Δ = η ∘ ε = μ ∘ (id ⊗ S) ∘ Δ

  Examples:
    - Group algebras k[G]          (S(g) = g⁻¹)
    - Universal enveloping algebras U(g)  (Δ(x) = x⊗1 + 1⊗x)
    - Function algebras O(G)       (coordinate rings of algebraic groups)
    - Quantum groups U_q(g)

  The bialgebra compatibility is: Δ(ab) = Δ(a)Δ(b) and Δ(1) = 1⊗1.
  We represent H as a single-sorted theory with two monoidal structures.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfHopfAlgebra : Theory :=
  let H := Expr.atom (gid "H")   -- underlying k-module
  { name     := "HopfAlgebra"
    doctrine := { doctrine := .HopfAlgebra }
    objects  := [
      { id := gid "H", description := "Underlying k-module of the Hopf algebra" }
    ]
    morphisms := [
      -- ── Algebra structure ─────────────────────────────────────────────
      { id := gid "mul",   domain := .prod H H, codomain := H,
        description := "Multiplication μ : H ⊗ H → H" },
      { id := gid "unit",  domain := .terminal, codomain := H,
        description := "Unit η : k → H  (η(1) = 1_H)" },

      -- ── Coalgebra structure ───────────────────────────────────────────
      { id := gid "comul",  domain := H, codomain := .prod H H,
        description := "Comultiplication Δ : H → H ⊗ H" },
      { id := gid "counit", domain := H, codomain := .terminal,
        description := "Counit ε : H → k" },

      -- ── Antipode ─────────────────────────────────────────────────────
      { id := gid "antipode", domain := H, codomain := H,
        description := "Antipode S : H → H" },

      -- ── Scalar action (k-linearity) ───────────────────────────────────
      { id := gid "scalar_mul", domain := .prod H H, codomain := H,
        description := "Scalar multiplication k ⊗ H → H" },

      -- ── Tensor product on H (Sweedler's notation helpers) ─────────────
      { id := gid "swap", domain := .prod H H, codomain := .prod H H,
        description := "Swap map: H⊗H → H⊗H  (for commutative Hopf algebras)" }
    ]
    axioms := [
      -- ── Algebra: associativity μ ∘ (μ ⊗ id) = μ ∘ (id ⊗ μ) ──────────
      { id := gid "mul_assoc"
        leftPath  := .comp (.prod (.atom (gid "mul")) (.id H)) (.atom (gid "mul"))
        rightPath := .comp (.prod (.id H) (.atom (gid "mul"))) (.atom (gid "mul"))
        description := "(ab)c = a(bc)" },

      -- ── Algebra: left unit μ ∘ (η ⊗ id) = id ────────────────────────
      { id := gid "mul_unit_left"
        leftPath  := .comp (.prod (.atom (gid "unit")) (.id H)) (.atom (gid "mul"))
        rightPath := .id H
        description := "1 · a = a" },

      -- ── Algebra: right unit μ ∘ (id ⊗ η) = id ───────────────────────
      { id := gid "mul_unit_right"
        leftPath  := .comp (.prod (.id H) (.atom (gid "unit"))) (.atom (gid "mul"))
        rightPath := .id H
        description := "a · 1 = a" },

      -- ── Coalgebra: coassociativity (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ ────
      { id := gid "comul_coassoc"
        leftPath  := .comp (.atom (gid "comul"))
                           (.prod (.atom (gid "comul")) (.id H))
        rightPath := .comp (.atom (gid "comul"))
                           (.prod (.id H) (.atom (gid "comul")))
        description := "(Δ⊗id)∘Δ = (id⊗Δ)∘Δ  (coassociativity)" },

      -- ── Coalgebra: left counit (ε ⊗ id) ∘ Δ = id ───────────────────
      { id := gid "counit_left"
        leftPath  := .comp (.atom (gid "comul"))
                           (.prod (.atom (gid "counit")) (.id H))
        rightPath := .id H
        description := "(ε⊗id) ∘ Δ = id" },

      -- ── Coalgebra: right counit (id ⊗ ε) ∘ Δ = id ──────────────────
      { id := gid "counit_right"
        leftPath  := .comp (.atom (gid "comul"))
                           (.prod (.id H) (.atom (gid "counit")))
        rightPath := .id H
        description := "(id⊗ε) ∘ Δ = id" },

      -- ── Bialgebra: Δ ∘ μ = (μ⊗μ) ∘ (id⊗τ⊗id) ∘ (Δ⊗Δ) (Δ is alg. morph.) ─
      { id := gid "bialgebra_comul"
        leftPath  := .comp (.atom (gid "mul")) (.atom (gid "comul"))
        rightPath := .comp (.atom (gid "comul"))
                           (.comp (.prod (.atom (gid "comul")) (.atom (gid "comul")))
                                  (.atom (gid "mul")))
        description := "Δ(ab) = Δ(a)·Δ(b)  (Δ is an algebra morphism)" },

      -- ── Bialgebra: ε(ab) = ε(a)ε(b) ─────────────────────────────────
      { id := gid "bialgebra_counit"
        leftPath  := .comp (.atom (gid "mul")) (.atom (gid "counit"))
        rightPath := .comp (.prod (.atom (gid "counit")) (.atom (gid "counit")))
                           (.atom (gid "mul"))
        description := "ε(ab) = ε(a)·ε(b)  (ε is an algebra morphism)" },

      -- ── Antipode: μ ∘ (S⊗id) ∘ Δ = η ∘ ε ───────────────────────────
      { id := gid "antipode_left"
        leftPath  := .comp (.atom (gid "comul"))
                           (.comp (.prod (.atom (gid "antipode")) (.id H))
                                  (.atom (gid "mul")))
        rightPath := .comp (.atom (gid "counit")) (.atom (gid "unit"))
        description := "μ ∘ (S⊗id) ∘ Δ = η ∘ ε  (left antipode axiom)" },

      -- ── Antipode: μ ∘ (id⊗S) ∘ Δ = η ∘ ε ───────────────────────────
      { id := gid "antipode_right"
        leftPath  := .comp (.atom (gid "comul"))
                           (.comp (.prod (.id H) (.atom (gid "antipode")))
                                  (.atom (gid "mul")))
        rightPath := .comp (.atom (gid "counit")) (.atom (gid "unit"))
        description := "μ ∘ (id⊗S) ∘ Δ = η ∘ ε  (right antipode axiom)" }
    ] }

end CatLab.Library
