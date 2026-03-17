/-
  CatLab -- Symmetric Monoidal Category

  A symmetric monoidal category (C, ⊗, I, α, λ, ρ, σ) consists of:
    - A category C
    - A bifunctor ⊗ : C × C → C  (monoidal product)
    - A unit object I
    - Associator    α_{A,B,C} : (A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)
    - Left unitor   λ_A : I ⊗ A ≅ A
    - Right unitor  ρ_A : A ⊗ I ≅ A
    - Symmetry      σ_{A,B} : A ⊗ B ≅ B ⊗ A

  Subject to:
    Pentagon coherence for α
    Triangle coherence for λ, ρ, α
    Hexagon coherence for σ and α
    Involutivity: σ_{B,A} ∘ σ_{A,B} = id

  This is the full signature of a strict symmetric monoidal category
  (strictness means α, λ, ρ are identities, but we include them as
  explicit morphisms to support the non-strict case).
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfSymmetricMonoidalCategory : Theory :=
  let Ob  := Expr.atom (gid "Ob")
  let Mor := Expr.atom (gid "Mor")
  { name     := "SymmetricMonoidalCategory"
    doctrine := { doctrine := .SymmetricMonoidal }
    objects  := [
      { id := gid "Ob",  description := "Objects" },
      { id := gid "Mor", description := "Morphisms" }
    ]
    morphisms := [
      -- ── Underlying category ───────────────────────────────────────────
      { id := gid "src",   domain := Mor, codomain := Ob,
        description := "Source" },
      { id := gid "tgt",   domain := Mor, codomain := Ob,
        description := "Target" },
      { id := gid "ident", domain := Ob, codomain := Mor,
        description := "Identity morphism" },
      { id := gid "comp",  domain := .prod Mor Mor, codomain := Mor,
        description := "Composition" },

      -- ── Monoidal product ─────────────────────────────────────────────
      { id := gid "tensor_ob",  domain := .prod Ob Ob, codomain := Ob,
        description := "Tensor product on objects A ⊗ B" },
      { id := gid "tensor_mor", domain := .prod Mor Mor, codomain := Mor,
        description := "Tensor product on morphisms f ⊗ g" },

      -- ── Monoidal unit ─────────────────────────────────────────────────
      { id := gid "unit_ob", domain := .terminal, codomain := Ob,
        description := "Monoidal unit object I : 1 → Ob" },

      -- ── Associator: α_{A,B,C} : (A⊗B)⊗C → A⊗(B⊗C) ─────────────────
      { id := gid "assoc",     domain := .prod (.prod Ob Ob) Ob, codomain := Mor,
        description := "Associator α : (A⊗B)⊗C → A⊗(B⊗C)" },
      { id := gid "assoc_inv", domain := .prod Ob (.prod Ob Ob), codomain := Mor,
        description := "Associator inverse α⁻¹ : A⊗(B⊗C) → (A⊗B)⊗C" },

      -- ── Left unitor: λ_A : I⊗A → A ──────────────────────────────────
      { id := gid "l_unitor",     domain := Ob, codomain := Mor,
        description := "Left unitor λ_A : I⊗A → A" },
      { id := gid "l_unitor_inv", domain := Ob, codomain := Mor,
        description := "Left unitor inverse λ⁻¹_A : A → I⊗A" },

      -- ── Right unitor: ρ_A : A⊗I → A ─────────────────────────────────
      { id := gid "r_unitor",     domain := Ob, codomain := Mor,
        description := "Right unitor ρ_A : A⊗I → A" },
      { id := gid "r_unitor_inv", domain := Ob, codomain := Mor,
        description := "Right unitor inverse ρ⁻¹_A : A → A⊗I" },

      -- ── Symmetry: σ_{A,B} : A⊗B → B⊗A ──────────────────────────────
      { id := gid "symm", domain := .prod Ob Ob, codomain := Mor,
        description := "Symmetry σ_{A,B} : A⊗B → B⊗A" }
    ]
    axioms := [
      -- ── Associator is a natural isomorphism ───────────────────────────
      { id := gid "assoc_iso"
        leftPath  := .comp (.atom (gid "assoc")) (.atom (gid "assoc_inv"))
        rightPath := .id Ob
        description := "α ∘ α⁻¹ = id  (associator isomorphism)" },

      -- ── Unitor isomorphisms ───────────────────────────────────────────
      { id := gid "l_unitor_iso"
        leftPath  := .comp (.atom (gid "l_unitor")) (.atom (gid "l_unitor_inv"))
        rightPath := .id Ob
        description := "λ ∘ λ⁻¹ = id" },

      { id := gid "r_unitor_iso"
        leftPath  := .comp (.atom (gid "r_unitor")) (.atom (gid "r_unitor_inv"))
        rightPath := .id Ob
        description := "ρ ∘ ρ⁻¹ = id" },

      -- ── Triangle: ρ_A ⊗ id_B = (id_A ⊗ λ_B) ∘ α_{A,I,B} ─────────────
      { id := gid "triangle"
        leftPath  := .comp (.atom (gid "assoc")) (.atom (gid "l_unitor"))
        rightPath := .atom (gid "r_unitor")
        description := "Triangle coherence: (id⊗λ) ∘ α = ρ⊗id" },

      -- ── Pentagon: α(A,B,C⊗D) ∘ α(A⊗B,C,D) = ... ─────────────────────
      { id := gid "pentagon"
        leftPath  := .comp (.atom (gid "assoc"))
                           (.comp (.atom (gid "assoc")) (.atom (gid "assoc")))
        rightPath := .comp (.atom (gid "assoc")) (.atom (gid "assoc"))
        description := "Pentagon coherence for α" },

      -- ── Symmetry is involutive ────────────────────────────────────────
      { id := gid "symm_invol"
        leftPath  := .comp (.atom (gid "symm")) (.atom (gid "symm"))
        rightPath := .id Mor
        description := "σ_{B,A} ∘ σ_{A,B} = id  (symmetry involutive)" },

      -- ── Hexagon: α ∘ σ ∘ α = (σ ⊗ id) ∘ α ∘ (id ⊗ σ) ──────────────
      { id := gid "hexagon"
        leftPath  := .comp (.atom (gid "symm")) (.atom (gid "assoc"))
        rightPath := .comp (.atom (gid "assoc"))
                           (.comp (.atom (gid "symm")) (.atom (gid "assoc")))
        description := "Hexagon coherence for σ and α" },

      -- ── Functoriality of ⊗ ───────────────────────────────────────────
      { id := gid "tensor_comp"
        leftPath  := .comp (.atom (gid "tensor_mor"))
                           (.comp (.atom (gid "tensor_mor")) (.atom (gid "comp")))
        rightPath := .comp (.prod (.atom (gid "comp")) (.atom (gid "comp")))
                           (.atom (gid "tensor_mor"))
        description := "(f∘g) ⊗ (h∘k) = (f⊗h) ∘ (g⊗k)  (bifunctoriality)" }
    ] }

end CatLab.Library
