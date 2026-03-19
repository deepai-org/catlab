/-
  CatLab -- Theory of an Elementary Topos

  An elementary topos is a category with:
    - Finite limits (terminal object, binary products, equalizers)
    - Cartesian closure (exponentials B^A with evaluation and currying)
    - A subobject classifier Ω with a truth morphism ⊤ : 1 → Ω

  The signature extends TheoryOfCategories with the additional structure.
  Objects Ob and Mor are inherited; new morphisms give the topos structure.
-/

import Catlab.Core.Theory
import Catlab.Library.Category

namespace CatLab.Library

def TheoryOfElementaryTopos : Theory :=
  let Ob  := Expr.atom (gid "Ob")
  let Mor := Expr.atom (gid "Mor")
  { name     := "ElementaryTopos"
    doctrine := { doctrine := .ElementaryTopos }
    objects  := TheoryOfCategories.objects  -- Ob, Mor
    morphisms := TheoryOfCategories.morphisms ++ [

      -- ── Finite Limits ──────────────────────────────────────────────
      -- Terminal object: a distinguished element 1 : Ob
      { id := gid "terminal_obj", domain := .terminal, codomain := Ob,
        description := "Terminal object: 1 → Ob" },

      -- Binary product on objects: prod : Ob × Ob → Ob
      { id := gid "prod_obj", domain := .prod Ob Ob, codomain := Ob,
        description := "Binary product on objects: Ob × Ob → Ob" },

      -- Projection morphisms out of the product
      { id := gid "π₁", domain := .prod Ob Ob, codomain := Mor,
        description := "First projection: A × B → A" },
      { id := gid "π₂", domain := .prod Ob Ob, codomain := Mor,
        description := "Second projection: A × B → B" },

      -- Pairing: given f : C → A and g : C → B, produce ⟨f,g⟩ : C → A×B
      { id := gid "pair_mor", domain := .prod Mor Mor, codomain := Mor,
        description := "Pairing of morphisms: ⟨f, g⟩" },

      -- ── Cartesian Closure ───────────────────────────────────────────
      -- Exponential object: exp : Ob × Ob → Ob  (B^A for pair (A, B))
      { id := gid "exp_obj", domain := .prod Ob Ob, codomain := Ob,
        description := "Exponential object B^A: Ob × Ob → Ob" },

      -- Evaluation morphism: eval : B^A × A → B  (encoded as Mor × Ob → Mor)
      { id := gid "eval", domain := .prod Mor Ob, codomain := Mor,
        description := "Evaluation: eval_{A,B} : B^A × A → B" },

      -- Currying: given f : C × A → B, produce curry(f) : C → B^A
      { id := gid "curry", domain := Mor, codomain := Mor,
        description := "Currying: (C × A → B) ↦ (C → B^A)" },

      -- ── Subobject Classifier ────────────────────────────────────────
      -- Ω: the subobject classifier, a distinguished object
      { id := gid "Omega_obj", domain := .terminal, codomain := Ob,
        description := "Subobject classifier Ω: 1 → Ob" },

      -- ⊤ : 1 → Ω  (the universal subobject)
      { id := gid "truth", domain := .terminal, codomain := Mor,
        description := "Truth morphism ⊤ : 1 → Ω" },

      -- Characteristic map: given a monomorphism m : A → B,
      -- the classifying map χ_m : B → Ω
      { id := gid "char_map", domain := Mor, codomain := Mor,
        description := "Characteristic map: mono ↦ classifying map to Ω" }
    ]
    axioms := TheoryOfCategories.axioms ++ [

      -- ⊤ has source the terminal object (src(⊤) = 1)
      { id := gid "truth_src"
        leftPath  := .comp (.atom (gid "truth")) (.atom (gid "src"))
        rightPath := .atom (gid "terminal_obj")
        description := "src(⊤) = terminal_obj" },

      -- ⊤ has target Ω (tgt(⊤) = Ω)
      { id := gid "truth_tgt"
        leftPath  := .comp (.atom (gid "truth")) (.atom (gid "tgt"))
        rightPath := .atom (gid "Omega_obj")
        description := "tgt(⊤) = Ω" },

      -- Projections source: src(π₁(A,B)) = prod_obj(A,B)
      { id := gid "pi1_src"
        leftPath  := .comp (.atom (gid "π₁")) (.atom (gid "src"))
        rightPath := .atom (gid "prod_obj")
        description := "src(π₁) = A × B" },

      -- eval ∘ ⟨curry(f), id⟩ = f  (the counit of the Cartesian closed adjunction)
      { id := gid "curry_eval"
        leftPath  := .comp (.prod (.atom (gid "curry")) (.id Ob)) (.atom (gid "eval"))
        rightPath := .id Mor
        description := "eval ∘ (curry(f) × id) = f" },

      -- Characteristic map target: tgt(χ_m) = Ω
      { id := gid "char_tgt"
        leftPath  := .comp (.atom (gid "char_map")) (.atom (gid "tgt"))
        rightPath := .atom (gid "Omega_obj")
        description := "tgt(χ_m) = Ω" }
    ] }

end CatLab.Library
