/-
  CatLab -- Enriched Categories (V-enriched categories)

  A category enriched over a monoidal category (V, ⊗, I) consists of:
    - A set of objects  Ob
    - For each pair (A, B): a hom-object  C(A, B) ∈ V
    - Composition:  ∘_{A,B,C} : C(B,C) ⊗ C(A,B) → C(A,C)  in V
    - Unit:         j_A : I → C(A,A)  in V

  Subject to associativity and unit axioms in V.

  Special cases:
    V = Set       → ordinary category
    V = Ab        → preadditive category
    V = Chain(Ab) → DG-category
    V = (0,1)-Cat → 2-poset (ordered category)
    V = sSet      → simplicially enriched category (∞-categorical model)
    V = Top       → topological category

  We represent this as a two-sorted theory with sorts Ob (C-objects)
  and VOb (V-objects for hom-sets) plus morphisms for the V-structure.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfEnrichedCategory : Theory :=
  let Ob  := Expr.atom (gid "Ob")    -- objects of the enriched category C
  let VOb := Expr.atom (gid "VOb")   -- objects of the enriching category V
  let VMor := Expr.atom (gid "VMor") -- morphisms of V  (internal to V)
  { name     := "EnrichedCategory"
    doctrine := { doctrine := .MonoidalCategory }
    objects  := [
      { id := gid "Ob",   description := "Objects of the enriched category C" },
      { id := gid "VOb",  description := "Objects of the enriching category V" },
      { id := gid "VMor", description := "Morphisms in V (for hom-objects)" }
    ]
    morphisms := [
      -- ── Hom-object functor: C(A,B) ∈ V for each pair A,B ─────────────
      { id := gid "hom",  domain := .prod Ob Ob, codomain := VOb,
        description := "Hom-object C(A,B) : Ob × Ob → VOb" },

      -- ── V-morphisms (morphisms of the enriching category V) ───────────
      { id := gid "v_src",  domain := VMor, codomain := VOb,
        description := "Source of a V-morphism" },
      { id := gid "v_tgt",  domain := VMor, codomain := VOb,
        description := "Target of a V-morphism" },
      { id := gid "v_id",   domain := VOb, codomain := VMor,
        description := "Identity in V" },
      { id := gid "v_comp", domain := .prod VMor VMor, codomain := VMor,
        description := "Composition in V" },

      -- ── Monoidal structure of V ───────────────────────────────────────
      { id := gid "v_tensor",  domain := .prod VOb VOb, codomain := VOb,
        description := "Monoidal product ⊗ in V" },
      { id := gid "v_unit",    domain := .terminal, codomain := VOb,
        description := "Monoidal unit I ∈ V" },
      { id := gid "v_tens_mor", domain := .prod VMor VMor, codomain := VMor,
        description := "Monoidal product on V-morphisms: f ⊗ g" },

      -- ── Enriched composition: ∘_{A,B,C} : C(B,C) ⊗ C(A,B) → C(A,C) ─
      { id := gid "comp_v", domain := .prod Ob (.prod Ob Ob), codomain := VMor,
        description := "Enriched composition ∘_{A,B,C} in V" },

      -- ── Enriched unit: j_A : I → C(A,A) ─────────────────────────────
      { id := gid "unit_v", domain := Ob, codomain := VMor,
        description := "Enriched unit j_A : I → C(A,A)" },

      -- ── Ordinary underlying morphisms (image under V(I,-)) ───────────
      { id := gid "und_mor",  domain := VMor, codomain := Ob,
        description := "Underlying morphism (elements of hom-objects)" },

      -- ── Underlying composition ────────────────────────────────────────
      { id := gid "und_comp", domain := .prod VMor VMor, codomain := VMor,
        description := "Composition of underlying morphisms" }
    ]
    axioms := [
      -- ── Enriched associativity: ∘ ∘ (∘ ⊗ id) = ∘ ∘ (id ⊗ ∘) ────────
      { id := gid "enr_assoc"
        leftPath  := .comp (.atom (gid "comp_v"))
                           (.comp (.prod (.atom (gid "comp_v")) (.id VOb))
                                  (.atom (gid "v_tensor")))
        rightPath := .comp (.atom (gid "comp_v"))
                           (.comp (.prod (.id VOb) (.atom (gid "comp_v")))
                                  (.atom (gid "v_tensor")))
        description := "Enriched associativity of composition" },

      -- ── Left enriched unit: ∘ ∘ (j ⊗ id) = λ ────────────────────────
      { id := gid "enr_left_unit"
        leftPath  := .comp (.atom (gid "unit_v"))
                           (.comp (.prod (.id VMor) (.id VMor))
                                  (.atom (gid "comp_v")))
        rightPath := .id VMor
        description := "Left unit: j ∘ id = id in V" },

      -- ── Right enriched unit: ∘ ∘ (id ⊗ j) = ρ ───────────────────────
      { id := gid "enr_right_unit"
        leftPath  := .comp (.atom (gid "unit_v"))
                           (.comp (.prod (.id VMor) (.id VMor))
                                  (.atom (gid "comp_v")))
        rightPath := .id VMor
        description := "Right unit: id ∘ j = id in V" },

      -- ── Hom-object source: C(A,B) is a V-object ─────────────────────
      { id := gid "hom_v_obj"
        leftPath  := .comp (.atom (gid "comp_v")) (.atom (gid "v_tgt"))
        rightPath := .comp (.atom (gid "hom")) (.atom (gid "v_tensor"))
        description := "tgt(∘_{A,B,C}) = C(B,C) ⊗ C(A,B)" },

      -- ── V is itself a category ────────────────────────────────────────
      { id := gid "v_left_id"
        leftPath  := .comp (.prod (.atom (gid "v_id")) (.id VMor))
                           (.atom (gid "v_comp"))
        rightPath := .id VMor
        description := "id ∘ f = f in V" },

      { id := gid "v_assoc"
        leftPath  := .comp (.prod (.atom (gid "v_comp")) (.id VMor))
                           (.atom (gid "v_comp"))
        rightPath := .comp (.prod (.id VMor) (.atom (gid "v_comp")))
                           (.atom (gid "v_comp"))
        description := "Associativity of V-composition" }
    ] }

end CatLab.Library
