/-
  CatLab — Arrow Category (C^→)

  Objects are morphisms of C. Morphisms are commutative squares.
  This is a direct, optimized construction (vs the general Comma category
  in Comma.lean which already defines `arrowCategory`).
-/

import Catlab.Core.Theory

namespace CatLab

namespace Arrow

/-- Compute C^→, the arrow category.

    Objects: morphisms f : A → B of C, named with `.arrow`.
    Morphisms: commutative squares — for each pair of morphisms f, g in C
    and each pair of morphisms u : dom(f) → dom(g), v : cod(f) → cod(g)
    such that g ∘ u = v ∘ f, we get a morphism f → g in C^→.

    This generates the structural data; commutativity axioms assert
    that the squares commute. -/
def arrowCat (t : Theory) : Theory :=
  let exprName (e : Expr) : Name := match e with | .atom g => g.name | _ => .root "?"

  let arrObjName (f : Generator1) : Name :=
    .arrow (exprName f.domain) (exprName f.codomain) f.id.name

  -- Objects: one for each morphism f of C
  let arrObjects := t.morphisms.map fun f =>
    { id := { name := arrObjName f, index := 0, kind := .sort }
      description := s!"Arrow object for {f.id.name}" : Generator0 }

  -- Morphisms: for each pair (f, g), a "square" morphism with domain and codomain
  -- components. We generate the source and target projections.
  let sourceProj := t.morphisms.map fun f =>
    { id := { name := .nested (arrObjName f) "src", index := 0, kind := .morphism }
      domain := .atom { name := arrObjName f, index := 0, kind := .sort }
      codomain := f.domain
      description := s!"Source projection of {f.id.name}" : Generator1 }

  let targetProj := t.morphisms.map fun f =>
    { id := { name := .nested (arrObjName f) "tgt", index := 0, kind := .morphism }
      domain := .atom { name := arrObjName f, index := 0, kind := .sort }
      codomain := f.codomain
      description := s!"Target projection of {f.id.name}" : Generator1 }

  -- Square morphisms: for each pair (f, g) of morphisms in C, a morphism f → g in Arr(C)
  let squares := t.morphisms.flatMap fun f =>
    t.morphisms.map fun g =>
      { id := { name := .pair (arrObjName f) (arrObjName g), index := 0, kind := .morphism }
        domain := .atom { name := arrObjName f, index := 0, kind := .sort }
        codomain := .atom { name := arrObjName g, index := 0, kind := .sort }
        description := s!"Square {f.id.name} → {g.id.name}" : Generator1 }

  -- Commutativity axioms: g ∘ u = v ∘ f for each square (u, v) : f → g
  let commuteAxioms := t.morphisms.flatMap fun f =>
    t.morphisms.map fun g =>
      let sqName := Name.pair (arrObjName f) (arrObjName g)
      let u := Expr.comp (.atom { name := .nested (arrObjName f) "src", index := 0, kind := .morphism })
                         (.atom { name := sqName, index := 0, kind := .morphism })
      let v := Expr.comp (.atom { name := .nested (arrObjName g) "tgt", index := 0, kind := .morphism })
                         (.atom { name := sqName, index := 0, kind := .morphism })
      { id := { name := .nested sqName "comm", index := 0, kind := .twoCell }
        leftPath := .comp (.atom { name := g.id.name, index := g.id.index, kind := .morphism }) u
        rightPath := .comp v (.atom { name := f.id.name, index := f.id.index, kind := .morphism })
        description := s!"Commutativity: {g.id.name} ∘ u = v ∘ {f.id.name}" : Generator2 }

  { name := s!"{t.name}^→"
    doctrine := t.doctrine
    objects := arrObjects
    morphisms := sourceProj ++ targetProj ++ squares
    axioms := commuteAxioms }

end Arrow

end CatLab
