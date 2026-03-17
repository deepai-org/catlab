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

  -- Helper to extract Name from domain/codomain Expr
  let domName (e : Expr) : Name := match e with | .atom g => g.name | _ => .root "?"
  let codName (e : Expr) : Name := match e with | .atom g => g.name | _ => .root "?"

  let prodMorphisms := c.morphisms.flatMap fun cf =>
    d.morphisms.map fun df =>
      { id := { name := Name.pair cf.id.name df.id.name, index := 0, kind := .morphism }
        domain := .atom { name := Name.pair (domName cf.domain) (domName df.domain),
                          index := 0, kind := .sort }
        codomain := .atom { name := Name.pair (codName cf.codomain) (codName df.codomain),
                            index := 0, kind := .sort }
        description := s!"({cf.id.name}, {df.id.name})" : Generator1 }

  -- Axioms: pair up axioms from each factor
  let prodAxioms := c.axioms.flatMap fun ca =>
    d.axioms.map fun da =>
      { id := { name := Name.pair ca.id.name da.id.name, index := 0, kind := .twoCell }
        leftPath := .prod ca.leftPath da.leftPath
        rightPath := .prod ca.rightPath da.rightPath
        description := s!"({ca.id.name}, {da.id.name})" : Generator2 }

  { name := s!"{c.name} × {d.name}"
    doctrine := c.doctrine
    objects := prodObjects
    morphisms := prodMorphisms
    axioms := prodAxioms }

end CatLab
