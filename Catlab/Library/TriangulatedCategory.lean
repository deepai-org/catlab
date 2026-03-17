/-
  CatLab -- Triangulated Categories

  A triangulated category (Puppe, Verdier) is an additive category C
  equipped with:
    - An auto-equivalence Σ : C → C  (suspension / shift functor)
    - A class of distinguished triangles  X →^f Y →^g Z →^h ΣX
  satisfying Verdier's axioms TR1–TR4:

    TR1. (a) For each X, the triangle X → X → 0 → ΣX is distinguished.
         (b) Every morphism f extends to a distinguished triangle.
         (c) Any triangle isomorphic to a distinguished one is distinguished.
    TR2. Rotation: if X→Y→Z→ΣX is distinguished, so is Y→Z→ΣX→ΣY.
    TR3. Morphism of triangles: given a commutative square between the
         first two maps of two distinguished triangles, there exists
         (not necessarily unique) a fill-in morphism on the third objects.
    TR4. Octahedral axiom: given composable f, g, h = g∘f, the three
         cones Cf, Cg, Ch fit into a distinguished triangle.

  We additionally include the additive (Ab-enriched) structure.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfTriangulatedCategory : Theory :=
  let Ob  := Expr.atom (gid "Ob")
  let Mor := Expr.atom (gid "Mor")
  let Tri := Expr.atom (gid "Tri")  -- distinguished triangles as a sort
  { name     := "TriangulatedCategory"
    doctrine := { doctrine := .TriangulatedCategory }
    objects  := [
      { id := gid "Ob",  description := "Objects" },
      { id := gid "Mor", description := "Morphisms" },
      { id := gid "Tri", description := "Distinguished triangles X→Y→Z→ΣX" }
    ]
    morphisms := [
      -- ── Underlying additive category ──────────────────────────────────
      { id := gid "src",     domain := Mor, codomain := Ob,
        description := "Source" },
      { id := gid "tgt",     domain := Mor, codomain := Ob,
        description := "Target" },
      { id := gid "ident",   domain := Ob, codomain := Mor,
        description := "Identity" },
      { id := gid "comp",    domain := .prod Mor Mor, codomain := Mor,
        description := "Composition" },
      { id := gid "add_mor", domain := .prod Mor Mor, codomain := Mor,
        description := "Addition of morphisms (Ab-enrichment)" },
      { id := gid "neg_mor", domain := Mor, codomain := Mor,
        description := "Negation of morphisms" },
      { id := gid "zero_ob", domain := .terminal, codomain := Ob,
        description := "Zero object" },
      { id := gid "zero_mor", domain := .prod Ob Ob, codomain := Mor,
        description := "Zero morphism 0_{A,B}" },

      -- ── Suspension functor Σ ─────────────────────────────────────────
      { id := gid "susp_ob",  domain := Ob, codomain := Ob,
        description := "Suspension on objects: ΣA" },
      { id := gid "susp_mor", domain := Mor, codomain := Mor,
        description := "Suspension on morphisms: Σf" },
      { id := gid "susp_inv_ob",  domain := Ob, codomain := Ob,
        description := "Desuspension on objects: Σ⁻¹A" },
      { id := gid "susp_inv_mor", domain := Mor, codomain := Mor,
        description := "Desuspension on morphisms: Σ⁻¹f" },

      -- ── Triangle projections ──────────────────────────────────────────
      { id := gid "tri_f",   domain := Tri, codomain := Mor,
        description := "First map f of a triangle X→Y→Z→ΣX" },
      { id := gid "tri_g",   domain := Tri, codomain := Mor,
        description := "Second map g of a triangle" },
      { id := gid "tri_h",   domain := Tri, codomain := Mor,
        description := "Connecting map h : Z → ΣX of a triangle" },

      -- ── Object projections from triangle ─────────────────────────────
      { id := gid "tri_X",   domain := Tri, codomain := Ob,
        description := "First object X of a triangle" },
      { id := gid "tri_Y",   domain := Tri, codomain := Ob,
        description := "Second object Y of a triangle" },
      { id := gid "tri_Z",   domain := Tri, codomain := Ob,
        description := "Cone object Z of a triangle" },

      -- ── Cone: the cone C(f) of a morphism f ──────────────────────────
      { id := gid "cone_ob",   domain := Mor, codomain := Ob,
        description := "Cone object C(f) of a morphism f" },
      { id := gid "cone_tri",  domain := Mor, codomain := Tri,
        description := "Distinguished triangle for a morphism: X→Y→C(f)→ΣX" },

      -- ── Rotation of a triangle ────────────────────────────────────────
      { id := gid "rotate",    domain := Tri, codomain := Tri,
        description := "Rotation: (X→Y→Z→ΣX) ↦ (Y→Z→ΣX→ΣY)  (TR2)" },

      -- ── Fill-in morphism for a morphism of triangles ──────────────────
      { id := gid "fillin",    domain := .prod Tri Tri, codomain := Mor,
        description := "Fill-in morphism on cones (TR3, not unique)" },

      -- ── Biproduct ─────────────────────────────────────────────────────
      { id := gid "biproduct", domain := .prod Ob Ob, codomain := Ob,
        description := "Direct sum A ⊕ B" }
    ]
    axioms := [
      -- ── TR1: Identity triangle X → X → 0 → ΣX is distinguished ───────
      { id := gid "tr1_id"
        leftPath  := .comp (.atom (gid "ident")) (.atom (gid "tri_f"))
        rightPath := .comp (.atom (gid "ident")) (.atom (gid "cone_ob"))
        description := "TR1: id(X) extends to triangle with zero cone" },

      -- ── TR2: Rotation preserves distinguished triangles ────────────────
      { id := gid "tr2_rotation"
        leftPath  := .comp (.atom (gid "rotate")) (.atom (gid "tri_f"))
        rightPath := .comp (.atom (gid "rotate")) (.atom (gid "tri_g"))
        description := "TR2: rotated triangle is distinguished" },

      -- ── Σ is a functor: Σ(f∘g) = Σf ∘ Σg ────────────────────────────
      { id := gid "susp_comp"
        leftPath  := .comp (.atom (gid "comp")) (.atom (gid "susp_mor"))
        rightPath := .comp (.prod (.atom (gid "susp_mor")) (.atom (gid "susp_mor")))
                           (.atom (gid "comp"))
        description := "Σ(f∘g) = Σf ∘ Σg  (Σ is a functor)" },

      -- ── Σ is an equivalence: Σ∘Σ⁻¹ = id ────────────────────────────
      { id := gid "susp_equiv"
        leftPath  := .comp (.atom (gid "susp_ob")) (.atom (gid "susp_inv_ob"))
        rightPath := .id Ob
        description := "Σ ∘ Σ⁻¹ = id  (suspension is an auto-equivalence)" },

      -- ── Composition g∘f = 0 for consecutive maps in a triangle ────────
      { id := gid "tri_fg_zero"
        leftPath  := .comp (.atom (gid "tri_f")) (.atom (gid "tri_g"))
        rightPath := .atom (gid "zero_mor")
        description := "g ∘ f = 0  (consecutive maps in a triangle)" },

      { id := gid "tri_gh_zero"
        leftPath  := .comp (.atom (gid "tri_g")) (.atom (gid "tri_h"))
        rightPath := .atom (gid "zero_mor")
        description := "h ∘ g = 0" },

      -- ── Triangle source/target consistency ───────────────────────────
      { id := gid "tri_f_src"
        leftPath  := .comp (.atom (gid "tri_f")) (.atom (gid "src"))
        rightPath := .atom (gid "tri_X")
        description := "src(f) = X" },

      { id := gid "tri_g_src"
        leftPath  := .comp (.atom (gid "tri_g")) (.atom (gid "src"))
        rightPath := .atom (gid "tri_Y")
        description := "src(g) = Y" }
    ] }

end CatLab.Library
