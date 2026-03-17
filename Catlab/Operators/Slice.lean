/-
  CatLab — Slice Category (C/X)

  Given a theory C and an object X in C, the slice category C/X has:
  - Objects: morphisms f : A → X in C
  - Morphisms: commuting triangles over X
  - Axioms: inherited from C, relativized to the slice

  This is the "local context" operator.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

/-- Compute the slice theory C/X.

    Objects of C/X are morphisms into X.
    Morphisms of C/X are commuting triangles. -/
def slice (t : Theory) (x : Expr) : Theory :=
  -- Objects of C/X: each morphism f : A → X whose codomain matches x
  let morphismsIntoX := t.morphisms.filter fun g => g.codomain == x
  let sliceObjects := morphismsIntoX.map fun g =>
    { id := { name := .arrow g.domain.toName x.toName g.id.name, index := 0 }
      description := s!"Slice object: {g.id.name} over X" : Generator0 }

  -- Morphisms of C/X: for each pair (f : A → X, g : B → X),
  -- look for h : A → B in C such that g ∘ h could equal f (commuting triangle)
  let sliceMorphisms := morphismsIntoX.flatMap fun f =>
    morphismsIntoX.filterMap fun g =>
      -- Find h : dom(f) → dom(g) in C
      t.morphisms.find? (fun h => h.domain == f.domain && h.codomain == g.domain)
      |>.map fun h =>
        let fSlice : GeneratorId := { name := .arrow f.domain.toName x.toName f.id.name }
        let gSlice : GeneratorId := { name := .arrow g.domain.toName x.toName g.id.name }
        { id := { name := .nested (.pair fSlice.name gSlice.name) h.id.name.toString,
                  index := 0, kind := .morphism }
          domain := .atom fSlice
          codomain := .atom gSlice
          description := s!"Slice morphism {h.id.name}: {f.id.name} → {g.id.name} over X" : Generator1 }

  -- Commutativity axioms: g ∘ h = f for each slice morphism
  let commuteAxioms := morphismsIntoX.flatMap fun f =>
    morphismsIntoX.filterMap fun g =>
      t.morphisms.find? (fun h => h.domain == f.domain && h.codomain == g.domain)
      |>.map fun h =>
        let sliceMorphName := Name.nested (.pair (.arrow f.domain.toName x.toName f.id.name)
                                                  (.arrow g.domain.toName x.toName g.id.name))
                                          h.id.name.toString
        { id := { name := .nested sliceMorphName "comm", index := 0, kind := .twoCell }
          leftPath := .comp (.atom h.id) (.atom g.id)
          rightPath := .atom f.id
          description := s!"Commutativity: {g.id.name} ∘ {h.id.name} = {f.id.name}" : Generator2 }

  { name := s!"{t.name}/X"
    doctrine := t.doctrine
    objects := sliceObjects
    morphisms := sliceMorphisms
    axioms := commuteAxioms }

/-- The forgetful functor C/X → C: sends (f : A → X) ↦ A -/
def sliceForgetful (t : Theory) (x : Expr) : List Generator1 :=
  t.morphisms.filterMap fun g =>
    some { id := { name := .root s!"forget_{g.id.name}", index := 0 }
           domain := .atom { name := .root s!"({g.id.name} → X)", index := 0 }
           codomain := g.domain
           description := s!"Forgetful: slice object to domain" }

end CatLab
