/-
  CatLab -- Abelian Categories

  An abelian category is an additive category in which:
    1. Every morphism has a kernel and a cokernel.
    2. Every monomorphism is a kernel (of its cokernel).
    3. Every epimorphism is a cokernel (of its kernel).

  These conditions imply every morphism factors as an epi followed by a mono,
  and the category is both exact and has all finite limits and colimits.

  Key structure:
    - Zero object  0  (both initial and terminal)
    - Biproduct  A ⊕ B  (simultaneously product and coproduct)
    - Ab-enrichment: each hom-set is an abelian group
    - Kernels and cokernels
    - Short exact sequences  0 → A → B → C → 0

  Classical examples: R-Mod, Sh(X, Ab), Coh(X).
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfAbelianCategory : Theory :=
  let Ob  := Expr.atom (gid "Ob")
  let Mor := Expr.atom (gid "Mor")
  { name     := "AbelianCategory"
    doctrine := { doctrine := .Abelian }
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
        description := "Identity" },
      { id := gid "comp",  domain := .prod Mor Mor, codomain := Mor,
        description := "Composition" },

      -- ── Zero object ───────────────────────────────────────────────────
      { id := gid "zero_ob", domain := .terminal, codomain := Ob,
        description := "Zero object 0 (initial and terminal)" },
      { id := gid "zero_mor", domain := .prod Ob Ob, codomain := Mor,
        description := "Zero morphism 0_{A,B} : A → B  (factors through 0)" },

      -- ── Addition of morphisms (Ab-enrichment) ─────────────────────────
      { id := gid "add_mor", domain := .prod Mor Mor, codomain := Mor,
        description := "Addition of morphisms: f + g" },
      { id := gid "neg_mor", domain := Mor, codomain := Mor,
        description := "Negation of a morphism: −f" },

      -- ── Biproduct  A ⊕ B ─────────────────────────────────────────────
      { id := gid "biproduct", domain := .prod Ob Ob, codomain := Ob,
        description := "Biproduct (direct sum) A ⊕ B" },
      { id := gid "inl",  domain := Ob, codomain := Mor,
        description := "Left inclusion  ι₁ : A → A ⊕ B" },
      { id := gid "inr",  domain := Ob, codomain := Mor,
        description := "Right inclusion ι₂ : B → A ⊕ B" },
      { id := gid "outl", domain := Ob, codomain := Mor,
        description := "Left projection  π₁ : A ⊕ B → A" },
      { id := gid "outr", domain := Ob, codomain := Mor,
        description := "Right projection π₂ : A ⊕ B → B" },

      -- ── Kernel ────────────────────────────────────────────────────────
      { id := gid "ker_ob",  domain := Mor, codomain := Ob,
        description := "Kernel object ker(f)" },
      { id := gid "ker_inc", domain := Mor, codomain := Mor,
        description := "Kernel inclusion  ker(f) ↪ A  (monic)" },

      -- ── Cokernel ─────────────────────────────────────────────────────
      { id := gid "coker_ob",  domain := Mor, codomain := Ob,
        description := "Cokernel object coker(f)" },
      { id := gid "coker_proj", domain := Mor, codomain := Mor,
        description := "Cokernel projection  B ↠ coker(f)  (epic)" },

      -- ── Image (epi-mono factorization) ───────────────────────────────
      { id := gid "image",     domain := Mor, codomain := Ob,
        description := "Image object im(f)" },
      { id := gid "image_inc", domain := Mor, codomain := Mor,
        description := "Image inclusion  im(f) ↪ B  (monic)" },
      { id := gid "image_epi", domain := Mor, codomain := Mor,
        description := "Epi part  A ↠ im(f)  of epi-mono factorization" }
    ]
    axioms := [
      -- ── Ab-enrichment: addition is commutative ────────────────────────
      { id := gid "add_comm"
        leftPath  := .comp (.prod (.id Mor) (.id Mor)) (.atom (gid "add_mor"))
        rightPath := .comp (.prod (.id Mor) (.id Mor)) (.atom (gid "add_mor"))
        description := "f + g = g + f" },

      -- ── Zero morphism is additive identity ────────────────────────────
      { id := gid "zero_add"
        leftPath  := .comp (.prod (.atom (gid "zero_mor")) (.id Mor))
                           (.atom (gid "add_mor"))
        rightPath := .id Mor
        description := "0 + f = f" },

      -- ── Negation: f + (−f) = 0 ────────────────────────────────────────
      { id := gid "add_neg"
        leftPath  := .comp (.prod (.id Mor) (.atom (gid "neg_mor")))
                           (.atom (gid "add_mor"))
        rightPath := .atom (gid "zero_mor")
        description := "f + (−f) = 0" },

      -- ── Bilinear composition: (f+g) ∘ h = f∘h + g∘h ──────────────────
      { id := gid "bilinear_right"
        leftPath  := .comp (.prod (.atom (gid "add_mor")) (.id Mor)) (.atom (gid "comp"))
        rightPath := .comp (.prod (.atom (gid "comp")) (.atom (gid "comp")))
                           (.atom (gid "add_mor"))
        description := "(f+g) ∘ h = f∘h + g∘h  (right bilinearity)" },

      -- ── Kernel: ker_inc ∘ f = 0 ──────────────────────────────────────
      { id := gid "ker_zero"
        leftPath  := .comp (.prod (.atom (gid "ker_inc")) (.id Mor)) (.atom (gid "comp"))
        rightPath := .atom (gid "zero_mor")
        description := "ker(f) ↪ A →^f B  has ker_inc ∘ f = 0" },

      -- ── Cokernel: f ∘ coker_proj = 0 ─────────────────────────────────
      { id := gid "coker_zero"
        leftPath  := .comp (.atom (gid "comp")) (.atom (gid "coker_proj"))
        rightPath := .atom (gid "zero_mor")
        description := "A →^f B ↠ coker(f)  has f ∘ coker = 0" },

      -- ── Biproduct projections: π₁ ∘ ι₁ = id ──────────────────────────
      { id := gid "biproduct_left"
        leftPath  := .comp (.prod (.atom (gid "inl")) (.atom (gid "outl")))
                           (.atom (gid "comp"))
        rightPath := .atom (gid "ident")
        description := "π₁ ∘ ι₁ = id_A" },

      { id := gid "biproduct_right"
        leftPath  := .comp (.prod (.atom (gid "inr")) (.atom (gid "outr")))
                           (.atom (gid "comp"))
        rightPath := .atom (gid "ident")
        description := "π₂ ∘ ι₂ = id_B" },

      -- ── Biproduct mixed: π₁ ∘ ι₂ = 0 ────────────────────────────────
      { id := gid "biproduct_mixed"
        leftPath  := .comp (.prod (.atom (gid "inr")) (.atom (gid "outl")))
                           (.atom (gid "comp"))
        rightPath := .atom (gid "zero_mor")
        description := "π₁ ∘ ι₂ = 0  (mixed biproduct)" },

      -- ── Epi-mono factorization: image_epi ∘ image_inc = f ────────────
      { id := gid "factorization"
        leftPath  := .comp (.atom (gid "image_epi")) (.atom (gid "image_inc"))
        rightPath := .id Mor
        description := "A ↠ im(f) ↪ B = f  (epi-mono factorization)" }
    ] }

end CatLab.Library
