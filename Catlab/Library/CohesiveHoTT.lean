/-
  CatLab -- Cohesive Homotopy Type Theory (Schreiber / Shulman)

  Cohesive HoTT extends HoTT with four modal operators that capture the
  "cohesive" structure relating abstract homotopy types to geometric spaces:

    ∫  (shape / homotopy)   : sharp → colocal   (left adjoint to ♭)
    ♭  (flat / discrete)    : identifies all paths  (right adjoint to ∫)
    ♯  (sharp / codiscrete) : makes everything a higher groupoid (right adjoint to ♭)
    ʃ  (shape, alternative) : = ∫

  Adjoint triple:   ∫ ⊣ ♭ ⊣ ♯
  Cohesion axioms:
    - ♭ is a comonad (flat has a counit ε: ♭A → A)
    - ♯ is a monad  (sharp has a unit  η: A → ♯A)
    - ∫ is a monad  (shape has a unit  η: A → ∫A)
    - ♭ preserves products

  Modalities are represented as endomorphisms on Ty (types) with
  unit / counit natural transformations as morphisms on Tm.
-/

import Catlab.Core.Theory
import Catlab.Library.HoTT

namespace CatLab.Library

def TheoryOfCohesiveHoTT : Theory :=
  let Ctx := Expr.atom (gid "Ctx")
  let Ty  := Expr.atom (gid "Ty")
  let Tm  := Expr.atom (gid "Tm")
  { name     := "CohesiveHomotopyTypeTheory"
    doctrine := { doctrine := .CohesiveHomotopyTypeTheory }
    objects  := TheoryOfHoTT.objects   -- Ctx, Ty, Tm
    morphisms := TheoryOfHoTT.morphisms ++ [

      -- ── Shape modality ∫ (= ʃ): A ↦ ∫A ──────────────────────────────
      { id := gid "shape_ty", domain := Ty, codomain := Ty,
        description := "Shape modality ∫A: Ty → Ty" },
      { id := gid "shape_unit", domain := Tm, codomain := Tm,
        description := "Shape unit η_A : A → ∫A  (unit of ∫ monad)" },
      { id := gid "shape_map", domain := Tm, codomain := Tm,
        description := "Functorial action of ∫ on terms" },

      -- ── Flat modality ♭: A ↦ ♭A ─────────────────────────────────────
      { id := gid "flat_ty", domain := Ty, codomain := Ty,
        description := "Flat modality ♭A: Ty → Ty" },
      { id := gid "flat_counit", domain := Tm, codomain := Tm,
        description := "Flat counit ε_A : ♭A → A  (counit of ♭ comonad)" },
      { id := gid "flat_comult", domain := Tm, codomain := Tm,
        description := "Flat comultiplication δ_A : ♭A → ♭(♭A)" },

      -- ── Sharp modality ♯: A ↦ ♯A ────────────────────────────────────
      { id := gid "sharp_ty", domain := Ty, codomain := Ty,
        description := "Sharp modality ♯A: Ty → Ty" },
      { id := gid "sharp_unit", domain := Tm, codomain := Tm,
        description := "Sharp unit η_A : A → ♯A  (unit of ♯ monad)" },
      { id := gid "sharp_mult", domain := Tm, codomain := Tm,
        description := "Sharp multiplication μ_A : ♯(♯A) → ♯A" },

      -- ── Adjunction data: ∫ ⊣ ♭ ──────────────────────────────────────
      { id := gid "shape_flat_unit", domain := Ty, codomain := Tm,
        description := "Unit of ∫ ⊣ ♭: A → ♭(∫A)" },
      { id := gid "shape_flat_counit", domain := Ty, codomain := Tm,
        description := "Counit of ∫ ⊣ ♭: ∫(♭A) → A" },

      -- ── Adjunction data: ♭ ⊣ ♯ ──────────────────────────────────────
      { id := gid "flat_sharp_unit", domain := Ty, codomain := Tm,
        description := "Unit of ♭ ⊣ ♯: A → ♯(♭A)" },
      { id := gid "flat_sharp_counit", domain := Ty, codomain := Tm,
        description := "Counit of ♭ ⊣ ♯: ♭(♯A) → A" },

      -- ── Pieces-have-points: ∫(♭A) = ∫A ─────────────────────────────
      { id := gid "pieces_points", domain := Ty, codomain := Ty,
        description := "Pieces-have-points: ∫(♭A) ≃ ∫A" },

      -- ── Discrete objects: ♭A ≃ A when A is discrete ──────────────────
      { id := gid "disc_refl", domain := Tm, codomain := Tm,
        description := "Discrete reflection: canonical ♭A → A for discrete A" }
    ]
    axioms := TheoryOfHoTT.axioms ++ [

      -- ── ♭ is a comonad: counit ∘ comult = id ─────────────────────────
      { id := gid "flat_comonad_left"
        leftPath  := .comp (.atom (gid "flat_comult")) (.atom (gid "flat_counit"))
        rightPath := .id Tm
        description := "ε ∘ δ = id  (left comonad law for ♭)" },

      { id := gid "flat_comonad_right"
        leftPath  := .comp (.atom (gid "flat_comult"))
                           (.comp (.atom (gid "flat_ty")) (.atom (gid "flat_counit")))
        rightPath := .id Tm
        description := "♭ε ∘ δ = id  (right comonad law for ♭)" },

      -- ── ♯ is a monad: mult ∘ unit = id ───────────────────────────────
      { id := gid "sharp_monad_left"
        leftPath  := .comp (.atom (gid "sharp_unit")) (.atom (gid "sharp_mult"))
        rightPath := .id Tm
        description := "μ ∘ η = id  (left monad law for ♯)" },

      { id := gid "sharp_monad_right"
        leftPath  := .comp (.comp (.atom (gid "sharp_ty")) (.atom (gid "sharp_unit")))
                           (.atom (gid "sharp_mult"))
        rightPath := .id Tm
        description := "μ ∘ ♯η = id  (right monad law for ♯)" },

      -- ── ∫ ⊣ ♭ adjunction triangle: unit ∘ counit = id ───────────────
      { id := gid "shape_flat_triangle"
        leftPath  := .comp (.atom (gid "shape_flat_unit"))
                           (.atom (gid "shape_flat_counit"))
        rightPath := .id Ty
        description := "∫ ⊣ ♭ triangle identity" },

      -- ── ♭ ⊣ ♯ adjunction triangle ────────────────────────────────────
      { id := gid "flat_sharp_triangle"
        leftPath  := .comp (.atom (gid "flat_sharp_unit"))
                           (.atom (gid "flat_sharp_counit"))
        rightPath := .id Ty
        description := "♭ ⊣ ♯ triangle identity" },

      -- ── ♭ preserves products ─────────────────────────────────────────
      { id := gid "flat_product"
        leftPath  := .comp (.prod (.atom (gid "flat_ty")) (.atom (gid "flat_ty")))
                           (.atom (gid "flat_ty"))
        rightPath := .comp (.atom (gid "flat_ty"))
                           (.prod (.atom (gid "flat_ty")) (.atom (gid "flat_ty")))
        description := "♭(A × B) ≃ ♭A × ♭B  (♭ preserves products)" }
    ] }

end CatLab.Library
