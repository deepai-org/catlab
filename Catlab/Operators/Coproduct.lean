/-
  CatLab — Coproduct Category (C ⊔ D)

  Disjoint union of two categories. Objects and morphisms are tagged
  with inl/inr. No cross-component morphisms exist. Dual to Product.lean.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute C ⊔ D, the coproduct (disjoint union) category.

    Objects: tagged union using Name.inl / Name.inr.
    Morphisms: tagged union, no cross-morphisms.
    Axioms: from each component, renamed with inl/inr. -/
def coproductCategory (c d : Theory) : Theory :=
  let leftObjects := c.objects.map fun o =>
    { id := { o.id with name := .inl o.id.name }
      description := s!"inl({o.description})" : Generator0 }

  let rightObjects := d.objects.map fun o =>
    { id := { o.id with name := .inr o.id.name }
      description := s!"inr({o.description})" : Generator0 }

  let tagExpr (tag : Name → Name) (e : Expr) : Expr :=
    e.mapNames tag

  let leftMorphisms := c.morphisms.map fun m =>
    { id := { m.id with name := .inl m.id.name }
      domain := tagExpr .inl m.domain
      codomain := tagExpr .inl m.codomain
      description := s!"inl({m.description})" : Generator1 }

  let rightMorphisms := d.morphisms.map fun m =>
    { id := { m.id with name := .inr m.id.name }
      domain := tagExpr .inr m.domain
      codomain := tagExpr .inr m.codomain
      description := s!"inr({m.description})" : Generator1 }

  let leftAxioms := c.axioms.map fun a =>
    { id := { a.id with name := .inl a.id.name }
      leftPath := tagExpr .inl a.leftPath
      rightPath := tagExpr .inl a.rightPath
      description := s!"inl({a.description})" : Generator2 }

  let rightAxioms := d.axioms.map fun a =>
    { id := { a.id with name := .inr a.id.name }
      leftPath := tagExpr .inr a.leftPath
      rightPath := tagExpr .inr a.rightPath
      description := s!"inr({a.description})" : Generator2 }

  { name := s!"{c.name} ⊔ {d.name}"
    doctrine := c.doctrine
    objects := leftObjects ++ rightObjects
    morphisms := leftMorphisms ++ rightMorphisms
    axioms := leftAxioms ++ rightAxioms }

end CatLab
