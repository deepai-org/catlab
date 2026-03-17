/-
  CatLab -- Theory of (small) Categories
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfCategories : Theory :=
  let Ob := Expr.atom (gid "Ob")
  let Mor := Expr.atom (gid "Mor")
  { name := "Category"
    doctrine := { doctrine := .Category }
    objects := [
      { id := gid "Ob", description := "Objects" },
      { id := gid "Mor", description := "Morphisms" }
    ]
    morphisms := [
      { id := gid "src", domain := Mor, codomain := Ob,
        description := "Source: Mor → Ob" },
      { id := gid "tgt", domain := Mor, codomain := Ob,
        description := "Target: Mor → Ob" },
      { id := gid "ident", domain := Ob, codomain := Mor,
        description := "Identity: Ob → Mor" },
      { id := gid "comp", domain := .prod Mor Mor, codomain := Mor,
        description := "Composition: Mor ×_{Ob} Mor → Mor" }
    ]
    axioms := [
      { id := gid "src_id"
        leftPath := .comp (.atom (gid "ident")) (.atom (gid "src"))
        rightPath := .id Ob
        description := "src(id_a) = a" },
      { id := gid "tgt_id"
        leftPath := .comp (.atom (gid "ident")) (.atom (gid "tgt"))
        rightPath := .id Ob
        description := "tgt(id_a) = a" },
      { id := gid "comp_assoc"
        leftPath := .comp (.prod (.atom (gid "comp")) (.id Mor)) (.atom (gid "comp"))
        rightPath := .comp (.prod (.id Mor) (.atom (gid "comp"))) (.atom (gid "comp"))
        description := "(f ∘ g) ∘ h = f ∘ (g ∘ h)" },
      { id := gid "left_id"
        leftPath := .comp (.prod (.atom (gid "ident")) (.id Mor)) (.atom (gid "comp"))
        rightPath := .id Mor
        description := "id ∘ f = f" },
      { id := gid "right_id"
        leftPath := .comp (.prod (.id Mor) (.atom (gid "ident"))) (.atom (gid "comp"))
        rightPath := .id Mor
        description := "f ∘ id = f" }
    ] }

end CatLab.Library
