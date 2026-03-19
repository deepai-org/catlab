/-
  CatLab -- Derivators (Grothendieck / Heller)

  A derivator is a strict 2-functor  D : Dia^op → CAT  where Dia is a
  suitable 2-category of small categories ("diagram shapes").  It axiomatises
  homotopy-coherent Kan extensions without choosing a specific model.

  Key structure:
    - D(J) : the "coherent J-diagram category"  for each shape J ∈ Dia
    - Restriction  u* : D(K) → D(J)  for each functor  u : J → K
    - Left Kan extension   u_! ⊣ u*  (homotopy left Kan extension)
    - Right Kan extension  u* ⊣ u_*  (homotopy right Kan extension)
    - Underlying diagram functor  dia_J : D(J) → ∏_{j ∈ J} D(1)
    - The point  D(1) plays the role of the "underlying category"

  We represent the 2-categorical structure one level up: objects are
  "diagram shapes", morphisms are "functors between shapes" and also
  "objects/morphisms of D(J) for a fixed shape".  This is a two-sorted
  presentation.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfDerivator : Theory :=
  let Sh  := Expr.atom (gid "Sh")   -- diagram shapes (small categories)
  let Obj := Expr.atom (gid "Obj")  -- objects of D(J)  (for each shape)
  let Mor := Expr.atom (gid "Mor")  -- morphisms in D(J)
  { name     := "Derivator"
    doctrine := { doctrine := .Derivator }
    objects  := [
      { id := gid "Sh",  description := "Diagram shapes (small categories)" },
      { id := gid "Obj", description := "Objects of the derivator value D(J)" },
      { id := gid "Mor", description := "Morphisms inside D(J)" }
    ]
    morphisms := [
      -- ── Shape morphisms (functors between diagram shapes) ─────────────
      { id := gid "shape_src", domain := Sh, codomain := Sh,
        description := "Source shape of a shape-morphism" },
      { id := gid "shape_tgt", domain := Sh, codomain := Sh,
        description := "Target shape of a shape-morphism" },
      { id := gid "shape_comp", domain := .prod Sh Sh, codomain := Sh,
        description := "Composition of shape-morphisms (functor composition)" },

      -- ── Evaluation: each object lives over a shape ────────────────────
      { id := gid "shape_of", domain := Obj, codomain := Sh,
        description := "The shape J such that this object is in D(J)" },

      -- ── Internal category structure of D(J) ──────────────────────────
      { id := gid "src", domain := Mor, codomain := Obj,
        description := "Source object in D(J)" },
      { id := gid "tgt", domain := Mor, codomain := Obj,
        description := "Target object in D(J)" },
      { id := gid "ident", domain := Obj, codomain := Mor,
        description := "Identity morphism in D(J)" },
      { id := gid "comp", domain := .prod Mor Mor, codomain := Mor,
        description := "Composition in D(J)" },

      -- ── Restriction functor u* : D(K) → D(J) ─────────────────────────
      { id := gid "restr", domain := .prod Obj Sh, codomain := Obj,
        description := "Restriction u*(X) : D(K) → D(J) for u : J → K" },

      -- ── Homotopy left Kan extension u_! ⊣ u* ─────────────────────────
      { id := gid "left_kan", domain := .prod Obj Sh, codomain := Obj,
        description := "Left Kan extension u_!(X) ∈ D(K) for u : J → K" },

      -- ── Homotopy right Kan extension u* ⊣ u_* ────────────────────────
      { id := gid "right_kan", domain := .prod Obj Sh, codomain := Obj,
        description := "Right Kan extension u_*(X) ∈ D(K)" },

      -- ── Counit of  u_! ⊣ u* : u*(u_!(X)) → X ────────────────────────
      { id := gid "left_counit", domain := Obj, codomain := Mor,
        description := "Counit of left Kan adjunction: u*(u_! X) → X" },

      -- ── Unit of  u* ⊣ u_* : X → u*(u_*(X)) ──────────────────────────
      { id := gid "right_unit", domain := Obj, codomain := Mor,
        description := "Unit of right Kan adjunction: X → u*(u_* X)" },

      -- ── Underlying diagram functor: dia : D(J) → D(1)^{Ob J} ─────────
      { id := gid "dia", domain := Obj, codomain := Obj,
        description := "Underlying diagram: dia_J(X) collapses J to D(1)" },

      -- ── Terminal shape (the point 1 ∈ Dia) ───────────────────────────
      { id := gid "point_shape", domain := .terminal, codomain := Sh,
        description := "The point (terminal shape) 1 ∈ Dia" },

      -- ── Colimit and limit as Kan extensions along J → 1 ──────────────
      { id := gid "colim", domain := Obj, codomain := Obj,
        description := "Homotopy colimit: left Kan along J → 1" },
      { id := gid "lim", domain := Obj, codomain := Obj,
        description := "Homotopy limit: right Kan along J → 1" }
    ]
    axioms := [
      -- ── Restriction preserves identity ───────────────────────────────
      { id := gid "restr_id"
        leftPath  := .comp (.prod (.atom (gid "ident")) (.id Sh)) (.atom (gid "restr"))
        rightPath := .comp (.atom (gid "restr")) (.atom (gid "ident"))
        description := "u*(id_X) = id_{u*(X)}" },

      -- ── Restriction preserves composition ────────────────────────────
      { id := gid "restr_comp"
        leftPath  := .comp (.prod (.atom (gid "comp")) (.id Sh)) (.atom (gid "restr"))
        rightPath := .comp (.prod (.atom (gid "restr")) (.atom (gid "restr")))
                           (.atom (gid "comp"))
        description := "u*(f ∘ g) = u*(f) ∘ u*(g)" },

      -- ── Left Kan ∘ restriction = id (counit-unit triangle) ───────────
      { id := gid "left_kan_triangle"
        leftPath  := .comp (.atom (gid "left_kan")) (.atom (gid "left_counit"))
        rightPath := .id Obj
        description := "Left Kan triangle: u_! ∘ u* → id" },

      -- ── Right Kan ∘ restriction = id (unit-counit triangle) ──────────
      { id := gid "right_kan_triangle"
        leftPath  := .comp (.prod (.atom (gid "right_unit")) (.id Sh)) (.atom (gid "right_kan"))
        rightPath := .id Obj
        description := "Right Kan triangle: id → u* ∘ u_*" },

      -- ── Colimit = left Kan along terminal shape ────────────────────
      { id := gid "colim_is_left_kan"
        leftPath  := .comp (.atom (gid "colim")) (.atom (gid "shape_of"))
        rightPath := .atom (gid "point_shape")
        description := "colim(X) lives in D(1) (the point shape)" }
    ] }

end CatLab.Library
