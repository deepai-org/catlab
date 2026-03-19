/-
  CatLab -- Operads and Multicategories

  An operad (non-symmetric) is a sequence of sets P(n) (n-ary operations)
  with:
    - A unit element  id ∈ P(1)
    - Composition  γ : P(k) × P(n₁) × ⋯ × P(nₖ) → P(n₁+⋯+nₖ)
    - Associativity and unit axioms

  A symmetric operad additionally has Σₙ-actions on P(n) compatible with γ.

  A coloured operad (= multicategory) has a set of colours/objects and
  multi-morphisms  f : (A₁, …, Aₙ) → B.

  We represent the coloured (multicategory) version as it subsumes the
  monochromatic (operad) case:
    Ob   — colours / object-sorts
    Op   — operations (multi-morphisms)
    The arity functor is modelled by source-list and target projections.
-/

import Catlab.Core.Theory
import Catlab.Operators.Algebraize

namespace CatLab.Library

-- ── Non-symmetric coloured operad (= multicategory) ──────────────────────

def TheoryOfMulticategory : Theory :=
  let Ob := Expr.atom (gid "Ob")   -- colours
  let Op := Expr.atom (gid "Op")   -- operations / multi-morphisms
  { name     := "Multicategory"
    doctrine := { doctrine := .Operad }
    objects  := [
      { id := gid "Ob", description := "Colours / object-sorts" },
      { id := gid "Op", description := "Multi-morphisms (operations)" }
    ]
    morphisms := [
      -- ── Target colour: each operation has a single output ─────────────
      { id := gid "out_col", domain := Op, codomain := Ob,
        description := "Output colour: Op → Ob" },

      -- ── Arity: each operation has a list of input colours.
      --    We approximate by a single (representative) input colour
      --    and a natural-number arity morphism. ──────────────────────────
      { id := gid "arity", domain := Op, codomain := .terminal,
        description := "Arity of an operation (number of inputs)" },

      -- ── Unit operation  id_A : (A) → A  for each colour A ────────────
      { id := gid "unit_op", domain := Ob, codomain := Op,
        description := "Unit operation id_A : (A) → A" },

      -- ── Sequential composition: plug output of g into i-th input of f
      --    f ∘ᵢ g : (A₁,…,Aᵢ₋₁, B₁,…,Bₘ, Aᵢ₊₁,…,Aₙ) → C ──────────────
      { id := gid "comp_op", domain := .prod Op Op, codomain := Op,
        description := "Composition: f ∘ᵢ g (plug g into i-th slot of f)" },

      -- ── Full substitution (operadic composition / corolla grafting) ───
      { id := gid "subst", domain := .prod Op Op, codomain := Op,
        description := "Simultaneous substitution (full operadic composition)" },

      -- ── The terminal (empty) input list ──────────────────────────────
      { id := gid "const_op", domain := Ob, codomain := Op,
        description := "Constant (0-ary) operation: nullary op of colour A" }
    ]
    axioms := [
      -- ── Unit laws: id_B ∘ f = f and f ∘ id_Aᵢ = f ──────────────────
      { id := gid "left_unit"
        leftPath  := .comp (.atom (gid "out_col")) (.atom (gid "unit_op"))
        rightPath := .comp (.atom (gid "comp_op")) (.id Op)
        description := "id_B ∘ f = f  (left unit)" },

      { id := gid "right_unit"
        leftPath  := .comp (.prod (.id Op) (.atom (gid "unit_op"))) (.atom (gid "comp_op"))
        rightPath := .id Op
        description := "f ∘ᵢ id_{Aᵢ} = f  (right unit)" },

      -- ── Associativity of sequential composition ───────────────────────
      { id := gid "assoc_comp"
        leftPath  := .comp (.prod (.atom (gid "comp_op")) (.id Op)) (.atom (gid "comp_op"))
        rightPath := .comp (.prod (.id Op) (.atom (gid "comp_op"))) (.atom (gid "comp_op"))
        description := "(f ∘ᵢ g) ∘ⱼ h = f ∘ᵢ (g ∘ⱼ' h)  (operadic associativity)" },

      -- ── Output colour preserved by composition ────────────────────────
      { id := gid "comp_out"
        leftPath  := .comp (.atom (gid "comp_op")) (.atom (gid "out_col"))
        rightPath := .comp (.prod (.id Op) (.atom (gid "out_col"))) (.atom (gid "out_col"))
        description := "out(f ∘ g) = out(f)" }
    ] }

-- ── Symmetric operad (monochromatic) ─────────────────────────────────────
-- Derived from the plain (non-symmetric) operad by adding the Σₙ-action.
-- The plain operad is a single-sorted version of Multicategory: just the
-- operations Op with composition and unit, ignoring colours.

private def plainOperad : Theory :=
  let Op := Expr.atom (gid "Op")
  { name     := "PlainOperad"
    doctrine := { doctrine := .Operad }
    objects  := [{ id := gid "Op", description := "Operations" }]
    morphisms := [
      { id := gid "arity",   domain := Op, codomain := .terminal,
        description := "Arity" },
      { id := gid "unit1",   domain := .terminal, codomain := Op,
        description := "Unit operation (arity 1)" },
      { id := gid "comp_op", domain := .prod Op Op, codomain := Op,
        description := "Operadic composition" }
    ]
    axioms := [
      { id := gid "unit_left"
        leftPath  := .comp (.prod (.atom (gid "unit1")) (.id Op)) (.atom (gid "comp_op"))
        rightPath := .id Op
        description := "id ∘ f = f" },
      { id := gid "assoc_op"
        leftPath  := .comp (.prod (.atom (gid "comp_op")) (.id Op)) (.atom (gid "comp_op"))
        rightPath := .comp (.prod (.id Op) (.atom (gid "comp_op"))) (.atom (gid "comp_op"))
        description := "Operadic associativity" }
    ] }

/-- Symmetric operad: plain operad + symmetric group action on operations.
    Derived as  addSymmetryAction(PlainOperad, "comp_op"). -/
def TheoryOfSymmetricOperad : Theory :=
  { addSymmetryAction plainOperad "comp_op" with
    name := "SymmetricOperad" }

end CatLab.Library
