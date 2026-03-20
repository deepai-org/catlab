/-
  CatLab -- (∞,n)-Categories

  An (∞,n)-category has k-morphisms for all k ≥ 0, where:
    - k-morphisms for k ≤ n may be non-invertible (the "n-categorical" levels)
    - k-morphisms for k > n are required to be invertible (the "∞" levels)

  Special cases:
    n=0: ∞-groupoid (all morphisms invertible)
    n=1: ∞-category (Lurie's quasi-categories / complete Segal spaces)
    n=2: (∞,2)-category (used in higher representation theory)
    n=∞: strict ω-category

  We represent the (∞,2)-case explicitly with sorts:
    Cell0, Cell1, Cell2 and face/degeneracy maps satisfying the globularity
    conditions, plus composition at each level.

  For the full (∞,n) signature the pattern extends to n+1 sorts.
-/

import Catlab.Core.Theory
import Catlab.Operators.Nerve
import Catlab.Library.Category

namespace CatLab.Library

-- (∞,2)-category as a representative case
def TheoryOfInfinityTwoCategory : Theory :=
  let C0 := Expr.atom (gid "Cell0")  -- objects
  let C1 := Expr.atom (gid "Cell1")  -- 1-morphisms
  let C2 := Expr.atom (gid "Cell2")  -- 2-morphisms
  { name     := "Infinity2Category"
    doctrine := { doctrine := .InfinityNCategory, strictified := true }
    objects  := [
      { id := gid "Cell0", description := "0-cells (objects)" },
      { id := gid "Cell1", description := "1-cells (morphisms)" },
      { id := gid "Cell2", description := "2-cells (homotopies)" }
    ]
    morphisms := [
      -- ── Globular source/target maps ───────────────────────────────────
      { id := gid "s0", domain := C1, codomain := C0,
        description := "Source of a 1-cell: s : C1 → C0" },
      { id := gid "t0", domain := C1, codomain := C0,
        description := "Target of a 1-cell: t : C1 → C0" },
      { id := gid "s1", domain := C2, codomain := C1,
        description := "Source of a 2-cell: s : C2 → C1" },
      { id := gid "t1", domain := C2, codomain := C1,
        description := "Target of a 2-cell: t : C2 → C1" },

      -- ── Identity cells ────────────────────────────────────────────────
      { id := gid "id0", domain := C0, codomain := C1,
        description := "Identity 1-cell: id : C0 → C1" },
      { id := gid "id1", domain := C1, codomain := C2,
        description := "Identity 2-cell: id : C1 → C2" },

      -- ── Horizontal composition of 1-cells: f ∘ g ─────────────────────
      { id := gid "comp0", domain := .prod C1 C1, codomain := C1,
        description := "Horizontal composition of 1-cells" },

      -- ── Vertical composition of 2-cells (same 1-cell boundary) ───────
      { id := gid "comp1v", domain := .prod C2 C2, codomain := C2,
        description := "Vertical composition of 2-cells" },

      -- ── Horizontal composition of 2-cells (whiskering) ───────────────
      { id := gid "comp1h", domain := .prod C2 C2, codomain := C2,
        description := "Horizontal composition of 2-cells (whiskering)" },

      -- ── Inverses for 2-cells (∞-groupoid structure at level 2) ────────
      { id := gid "inv2", domain := C2, codomain := C2,
        description := "Inverse of a 2-cell (2-cells are invertible)" }
    ]
    axioms := [
      -- ── Globularity conditions ────────────────────────────────────────
      { id := gid "glob_s"
        leftPath  := .comp (.atom (gid "s1")) (.atom (gid "s0"))
        rightPath := .comp (.atom (gid "t1")) (.atom (gid "s0"))
        description := "s(s(α)) = s(t(α))  (globularity)" },

      { id := gid "glob_t"
        leftPath  := .comp (.atom (gid "s1")) (.atom (gid "t0"))
        rightPath := .comp (.atom (gid "t1")) (.atom (gid "t0"))
        description := "t(s(α)) = t(t(α))  (globularity)" },

      -- ── Source/target of identities ───────────────────────────────────
      { id := gid "id0_s"
        leftPath  := .comp (.atom (gid "id0")) (.atom (gid "s0"))
        rightPath := .id C0
        description := "s(id_x) = x" },

      { id := gid "id0_t"
        leftPath  := .comp (.atom (gid "id0")) (.atom (gid "t0"))
        rightPath := .id C0
        description := "t(id_x) = x" },

      { id := gid "id1_s"
        leftPath  := .comp (.atom (gid "id1")) (.atom (gid "s1"))
        rightPath := .id C1
        description := "s(id_f) = f" },

      { id := gid "id1_t"
        leftPath  := .comp (.atom (gid "id1")) (.atom (gid "t1"))
        rightPath := .id C1
        description := "t(id_f) = f" },

      -- ── Unit laws for horizontal composition ──────────────────────────
      { id := gid "left_unit0"
        leftPath  := .comp (.prod (.atom (gid "id0")) (.id C1)) (.atom (gid "comp0"))
        rightPath := .id C1
        description := "id ∘ f = f  (left unit, 1-cells)" },

      { id := gid "right_unit0"
        leftPath  := .comp (.prod (.id C1) (.atom (gid "id0"))) (.atom (gid "comp0"))
        rightPath := .id C1
        description := "f ∘ id = f  (right unit, 1-cells)" },

      -- ── Associativity of horizontal composition ────────────────────
      { id := gid "assoc0"
        leftPath  := .comp (.prod (.atom (gid "comp0")) (.id C1)) (.atom (gid "comp0"))
        rightPath := .comp (.prod (.id C1) (.atom (gid "comp0"))) (.atom (gid "comp0"))
        description := "Associativity of horizontal composition" },

      -- ── Vertical unit and associativity (2-cells) ────────────────────
      { id := gid "vert_unit"
        leftPath  := .comp (.prod (.atom (gid "id1")) (.id C2)) (.atom (gid "comp1v"))
        rightPath := .id C2
        description := "id ∙ α = α  (vertical unit)" },

      { id := gid "vert_assoc"
        leftPath  := .comp (.prod (.atom (gid "comp1v")) (.id C2)) (.atom (gid "comp1v"))
        rightPath := .comp (.prod (.id C2) (.atom (gid "comp1v"))) (.atom (gid "comp1v"))
        description := "Associativity of vertical composition" },

      -- ── 2-cells invertible: α ∙ α⁻¹ = id ────────────────────────────
      { id := gid "inv2_right"
        leftPath  := .comp (.prod (.id C2) (.atom (gid "inv2"))) (.atom (gid "comp1v"))
        rightPath := .comp (.atom (gid "s1")) (.atom (gid "id1"))
        description := "α ∙ α⁻¹ = id_{s(α)}  (2-cells invertible)" },

      -- ── Interchange law ───────────────────────────────────────────────
      { id := gid "interchange"
        leftPath  := .comp (.prod (.atom (gid "comp1h")) (.atom (gid "comp1h")))
                           (.atom (gid "comp1v"))
        rightPath := .comp (.prod (.atom (gid "comp1v")) (.atom (gid "comp1v")))
                           (.atom (gid "comp1h"))
        description := "(α ∙ β) ∘ (γ ∙ δ) = (α ∘ γ) ∙ (β ∘ δ)" }
    ] }

-- (∞,1)-categories derived as the nerve of the theory of categories.
-- The nerve N(C) is the canonical (∞,1)-category presentation: its n-simplices
-- are composable n-tuples, face maps compose, degeneracies insert identities,
-- and the simplicial identities encode the full coherence of composition.
def TheoryOfInfinityCategory : Theory :=
  { nerve TheoryOfCategories with
    name     := "InfinityCategory"
    doctrine := { doctrine := .InfinityNCategory, strictified := true } }

end CatLab.Library
