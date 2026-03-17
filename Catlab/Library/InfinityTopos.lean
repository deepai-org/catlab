/-
  CatLab -- Theory of an ∞-Topos (Lurie)

  An ∞-topos is a presentable ∞-category satisfying higher Giraud axioms:
    1. All small ∞-colimits exist (and are universal / stable under pullback)
    2. All small ∞-limits exist
    3. Object classifier: a map p : Ũ → U such that every small left
       fibration is a pullback of p  (the analog of the subobject classifier)

  The hom-spaces are ∞-groupoids (spaces), represented here as a third sort Spc.
  We encode the 1-truncation of the structure: objects, morphisms (1-simplices),
  and the mapping-space functor Ob × Ob → Spc.

  The colimit and limit structure is specified by the Giraud axioms encoded as
  morphisms (colim, lim) and a descent axiom.  The object classifier gives the
  universal fibration univ_fib : Ũ → U whose base-changes classify small maps.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfInfinityTopos : Theory :=
  let Ob  := Expr.atom (gid "Ob")
  let Map := Expr.atom (gid "Map")
  let Spc := Expr.atom (gid "Spc")
  { name     := "InfinityTopos"
    doctrine := { doctrine := .PresentableInfinityCategory }
    objects  := [
      { id := gid "Ob",  description := "Objects of the ∞-topos" },
      { id := gid "Map", description := "Morphisms (1-simplices of the ∞-category)" },
      { id := gid "Spc", description := "∞-groupoids (mapping spaces, 'Spaces')" }
    ]
    morphisms := [

      -- ── Basic ∞-categorical structure ───────────────────────────────
      { id := gid "src", domain := Map, codomain := Ob,
        description := "Source: Map → Ob" },
      { id := gid "tgt", domain := Map, codomain := Ob,
        description := "Target: Map → Ob" },
      { id := gid "id_map", domain := Ob, codomain := Map,
        description := "Identity 1-cell: Ob → Map" },

      -- Composition (homotopy-coherent; here 1-truncated)
      { id := gid "comp_map", domain := .prod Map Map, codomain := Map,
        description := "Composition of 1-morphisms" },

      -- Mapping space functor: Map(X, Y) ∈ Spc for each pair of objects
      { id := gid "hom_space", domain := .prod Ob Ob, codomain := Spc,
        description := "Mapping space Hom(X,Y) : Ob × Ob → Spc" },

      -- ── Small limits and colimits ────────────────────────────────────
      -- Terminal object (limit over the empty diagram)
      { id := gid "terminal_obj", domain := .terminal, codomain := Ob,
        description := "Terminal object 1 : 1 → Ob" },

      -- Pullback (limit over the cospan diagram)
      { id := gid "pullback_obj", domain := .prod Map Map, codomain := Ob,
        description := "Pullback object: Map ×_Ob Map → Ob" },

      -- Colimit functor: takes a diagram shape and returns a colimiting object
      { id := gid "colim", domain := Spc, codomain := Ob,
        description := "Colimit: Spc (diagram) → Ob" },

      -- Limit functor: dual
      { id := gid "lim", domain := Spc, codomain := Ob,
        description := "Limit: Spc (diagram) → Ob" },

      -- ── Object classifier (Lurie's ∞-topos axiom) ───────────────────
      -- The universe object U ∈ Ob (classifies small ∞-groupoids)
      { id := gid "U_obj", domain := .terminal, codomain := Ob,
        description := "Universe object U : 1 → Ob" },

      -- The pointed universe Ũ ∈ Ob (total space of the universal fibration)
      { id := gid "U_tilde", domain := .terminal, codomain := Ob,
        description := "Pointed universe Ũ : 1 → Ob" },

      -- Universal fibration p : Ũ → U (every small left fibration is a pullback of p)
      { id := gid "univ_fib", domain := .terminal, codomain := Map,
        description := "Universal fibration p : Ũ → U" },

      -- Classifying map: for each small map f, its classifying map to U
      { id := gid "classify", domain := Map, codomain := Map,
        description := "Classifying map: small Map → Map (into U)" },

      -- ── Descent / universality of colimits ──────────────────────────
      -- The descent map: colimits are stable under pullback
      { id := gid "descent", domain := .prod Map Spc, codomain := Spc,
        description := "Descent: pullback commutes with colimits" }
    ]
    axioms := [

      -- ── Source/target of the universal fibration ─────────────────────
      { id := gid "univ_fib_src"
        leftPath  := .comp (.atom (gid "univ_fib")) (.atom (gid "src"))
        rightPath := .atom (gid "U_tilde")
        description := "src(univ_fib) = Ũ" },

      { id := gid "univ_fib_tgt"
        leftPath  := .comp (.atom (gid "univ_fib")) (.atom (gid "tgt"))
        rightPath := .atom (gid "U_obj")
        description := "tgt(univ_fib) = U" },

      -- ── Identity laws ────────────────────────────────────────────────
      { id := gid "src_id"
        leftPath  := .comp (.atom (gid "id_map")) (.atom (gid "src"))
        rightPath := .id Ob
        description := "src(id_X) = X" },

      { id := gid "tgt_id"
        leftPath  := .comp (.atom (gid "id_map")) (.atom (gid "tgt"))
        rightPath := .id Ob
        description := "tgt(id_X) = X" },

      -- ── Classification pullback ──────────────────────────────────────
      -- classify(f) is a map into U, and pulling back univ_fib along it gives f
      { id := gid "classify_tgt"
        leftPath  := .comp (.atom (gid "classify")) (.atom (gid "tgt"))
        rightPath := .atom (gid "U_obj")
        description := "tgt(classify(f)) = U  (classifying maps land in U)" },

      -- ── Universal colimits (Giraud axiom, 1-truncated form) ──────────
      -- colim is left adjoint to the constant-diagram functor (encoded by
      -- the counit: colim ∘ const = id on Ob up to homotopy)
      { id := gid "colim_const"
        leftPath  := .comp (.atom (gid "colim")) (.atom (gid "lim"))
        rightPath := .id Ob
        description := "Colimits are left adjoint to limits (counit)" },

      -- ── Descent axiom ───────────────────────────────────────────────
      -- Pullback of a colimit diagram = colimit of the pulled-back diagram
      { id := gid "descent_axiom"
        leftPath  := .comp (.atom (gid "descent")) (.atom (gid "colim"))
        rightPath := .comp (.atom (gid "pullback_obj")) (.atom (gid "colim"))
        description := "Descent: f*(colim D) ≅ colim(f* ∘ D)" }
    ] }

end CatLab.Library
