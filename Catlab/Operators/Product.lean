/-
  CatLab — Product Category (C × D)

  Objects are pairs (c, d). Morphisms are pairs (f, g).
  Composition and identities are componentwise.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute C × D, the product category.

    Objects: pairs (c, d) for c ∈ Ob(C), d ∈ Ob(D).
    Morphisms: pairs (f, g) for f ∈ Mor(C), g ∈ Mor(D).
    Domain/codomain are componentwise. -/
def productCategory (c d : Theory) : Theory :=
  let prodObjects := c.objects.flatMap fun co =>
    d.objects.map fun do_ =>
      { id := { name := Name.pair co.id.name do_.id.name, index := 0, kind := .sort }
        description := s!"({co.id.name}, {do_.id.name})" : Generator0 }

  -- Tag original generators to avoid name collisions (e.g., both theories having μ)
  let tagExprL (e : Expr) : Expr := e.mapNames .inl
  let tagExprR (e : Expr) : Expr := e.mapNames .inr

  let prodMorphisms := c.morphisms.flatMap fun cf =>
    d.morphisms.map fun df =>
      { id := { name := Name.pair cf.id.name df.id.name, index := 0, kind := .morphism }
        domain := .prod (tagExprL cf.domain) (tagExprR df.domain)
        codomain := .prod (tagExprL cf.codomain) (tagExprR df.codomain)
        description := s!"({cf.id.name}, {df.id.name})" : Generator1 }

  let cObjects := c.objects.map fun o =>
    { id := { o.id with name := .inl o.id.name }
      description := s!"fst({o.description})" : Generator0 }
  let dObjects := d.objects.map fun o =>
    { id := { o.id with name := .inr o.id.name }
      description := s!"snd({o.description})" : Generator0 }

  let cMorphisms := c.morphisms.map fun m =>
    { id := { m.id with name := .inl m.id.name }
      domain := tagExprL m.domain
      codomain := tagExprL m.codomain
      description := s!"fst({m.description})" : Generator1 }
  let dMorphisms := d.morphisms.map fun m =>
    { id := { m.id with name := .inr m.id.name }
      domain := tagExprR m.domain
      codomain := tagExprR m.codomain
      description := s!"snd({m.description})" : Generator1 }

  -- Axioms: pair up axioms from each factor, tagging atom references
  let prodAxioms := c.axioms.flatMap fun ca =>
    d.axioms.map fun da =>
      { id := { name := Name.pair ca.id.name da.id.name, index := 0, kind := .twoCell }
        leftPath := .prod (tagExprL ca.leftPath) (tagExprR da.leftPath)
        rightPath := .prod (tagExprL ca.rightPath) (tagExprR da.rightPath)
        description := s!"({ca.id.name}, {da.id.name})" : Generator2 }

  (Theory.mk' s!"{c.name} × {d.name}" c.doctrine
    (cObjects ++ dObjects ++ prodObjects)
    (cMorphisms ++ dMorphisms ++ prodMorphisms)
    prodAxioms).dedup

end CatLab
