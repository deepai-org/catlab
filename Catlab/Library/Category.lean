/-
  CatLab -- Theory of (small) Categories
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfCategories : Theory :=
  let Ob := Expr.atom ⟨"Ob", 0⟩
  let Mor := Expr.atom ⟨"Mor", 0⟩
  { name := "Category"
    doctrine := { doctrine := .Category }
    objects := [
      { id := ⟨"Ob", 0⟩, description := "Objects" },
      { id := ⟨"Mor", 0⟩, description := "Morphisms" }
    ]
    morphisms := [
      { id := ⟨"src", 0⟩, domain := Mor, codomain := Ob,
        description := "Source: Mor → Ob" },
      { id := ⟨"tgt", 0⟩, domain := Mor, codomain := Ob,
        description := "Target: Mor → Ob" },
      { id := ⟨"ident", 0⟩, domain := Ob, codomain := Mor,
        description := "Identity: Ob → Mor" },
      { id := ⟨"comp", 0⟩, domain := .prod Mor Mor, codomain := Mor,
        description := "Composition: Mor ×_{Ob} Mor → Mor" }
    ]
    axioms := [
      { id := ⟨"src_id", 0⟩
        leftPath := .comp (.atom ⟨"ident", 0⟩) (.atom ⟨"src", 0⟩)
        rightPath := .id Ob
        description := "src(id_a) = a" },
      { id := ⟨"tgt_id", 0⟩
        leftPath := .comp (.atom ⟨"ident", 0⟩) (.atom ⟨"tgt", 0⟩)
        rightPath := .id Ob
        description := "tgt(id_a) = a" },
      { id := ⟨"comp_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"comp", 0⟩) (.id Mor)) (.atom ⟨"comp", 0⟩)
        rightPath := .comp (.prod (.id Mor) (.atom ⟨"comp", 0⟩)) (.atom ⟨"comp", 0⟩)
        description := "(f ∘ g) ∘ h = f ∘ (g ∘ h)" },
      { id := ⟨"left_id", 0⟩
        leftPath := .comp (.prod (.atom ⟨"ident", 0⟩) (.id Mor)) (.atom ⟨"comp", 0⟩)
        rightPath := .id Mor
        description := "id ∘ f = f" },
      { id := ⟨"right_id", 0⟩
        leftPath := .comp (.prod (.id Mor) (.atom ⟨"ident", 0⟩)) (.atom ⟨"comp", 0⟩)
        rightPath := .id Mor
        description := "f ∘ id = f" }
    ] }

end CatLab.Library
