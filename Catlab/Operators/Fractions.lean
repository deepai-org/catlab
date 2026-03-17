/-
  CatLab — Calculus of Fractions

  Given a theory C with a class of morphisms S satisfying the right Ore
  condition, constructs the localization C[S⁻¹] using formal roofs.

  Objects: same as the base theory.
  Morphisms: roofs (spans) A ← C → B where A ← C is in S.
  Composition: via the Ore condition, pulling back roofs.
  Equivalence: two roofs are equivalent if they have a common refinement.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Data for a calculus of right fractions: a theory together with a
    distinguished class of morphisms satisfying the right Ore condition. -/
structure OreData where
  theory : Theory
  rightFractions : List GeneratorId  -- morphisms satisfying right Ore condition

/-- Construct the localization via the calculus of right fractions.

    A morphism A → B in the localized category is a roof:
        C
       / \
      s   f
     ↓     ↓
     A     B
    where s : C → A is in the fraction class S. -/
def calculusOfFractions (od : OreData) : Theory :=
  let t := od.theory

  -- Objects: same as the base theory
  let objects := t.objects

  -- Roof morphisms: for each base morphism f : A → B and fraction s : C → A,
  -- create a roof [s, f] : A → B
  let roofMorphisms : List Generator1 := od.rightFractions.flatMap fun sId =>
    match t.findMorphism sId.name with
    | none => []
    | some s =>
      t.morphisms.filterMap fun f =>
        if f.domain.toName == s.domain.toName then
          let roofName := Name.arrow sId.name f.id.name (.root "roof")
          some { id := { name := roofName, index := 0, kind := .morphism }
                 domain := s.codomain
                 codomain := f.codomain
                 description := s!"Roof [{sId.name}, {f.id.name}]" }
        else none

  -- Equivalence axiom: roof compatibility
  let equivAxioms : List Generator2 := od.rightFractions.flatMap fun sId =>
    match t.findMorphism sId.name with
    | none => []
    | some s =>
      t.morphisms.filterMap fun f =>
        if f.domain.toName == s.domain.toName then
          let roofName := Name.arrow sId.name f.id.name (.root "roof")
          some { id := gid s!"roof_compat_{sId.name}_{f.id.name}" (k := .twoCell)
                 leftPath := .comp (.atom f.id) (.atom sId)
                 rightPath := .comp (.atom { name := roofName, index := 0, kind := .morphism })
                                    (.atom sId)
                 description := s!"Roof compatibility for [{sId.name}, {f.id.name}]" }
        else none

  -- Ore apex objects
  let oreApexObjects : List Generator0 := od.rightFractions.flatMap fun sId =>
    match t.findMorphism sId.name with
    | none => []
    | some s =>
      t.morphisms.filterMap fun f =>
        if f.codomain.toName == s.codomain.toName && f.id.name != sId.name then
          let apexName := Name.pair (.root s!"ore_apex_{f.id.name}") (.root s!"{sId.name}")
          some { id := { name := apexName, index := 0, kind := .sort }
                 description := s!"Ore pullback apex for ({f.id.name}, {sId.name})" }
        else none

  -- Ore witness t : apex → A
  let oreWitnesses : List Generator1 := od.rightFractions.flatMap fun sId =>
    match t.findMorphism sId.name with
    | none => []
    | some s =>
      t.morphisms.filterMap fun f =>
        if f.codomain.toName == s.codomain.toName && f.id.name != sId.name then
          let oreName := Name.nested (.root "ore") s!"{f.id.name}_{sId.name}"
          let apexName := Name.pair (.root s!"ore_apex_{f.id.name}") (.root s!"{sId.name}")
          some { id := { name := .nested oreName "t", index := 0, kind := .morphism }
                 domain := .atom { name := apexName, index := 0, kind := .sort }
                 codomain := f.domain
                 description := s!"Ore witness t for ({f.id.name}, {sId.name})" }
        else none

  -- Ore witness g : apex → D
  let oreGMorphisms : List Generator1 := od.rightFractions.flatMap fun sId =>
    match t.findMorphism sId.name with
    | none => []
    | some s =>
      t.morphisms.filterMap fun f =>
        if f.codomain.toName == s.codomain.toName && f.id.name != sId.name then
          let oreName := Name.nested (.root "ore") s!"{f.id.name}_{sId.name}"
          let apexName := Name.pair (.root s!"ore_apex_{f.id.name}") (.root s!"{sId.name}")
          some { id := { name := .nested oreName "g", index := 0, kind := .morphism }
                 domain := .atom { name := apexName, index := 0, kind := .sort }
                 codomain := s.domain
                 description := s!"Ore witness g for ({f.id.name}, {sId.name})" }
        else none

  -- Ore commutativity: f ∘ t = s ∘ g
  let oreAxioms : List Generator2 := od.rightFractions.flatMap fun sId =>
    match t.findMorphism sId.name with
    | none => []
    | some s =>
      t.morphisms.filterMap fun f =>
        if f.codomain.toName == s.codomain.toName && f.id.name != sId.name then
          let oreName := Name.nested (.root "ore") s!"{f.id.name}_{sId.name}"
          some { id := gid s!"ore_sq_{f.id.name}_{sId.name}" (k := .twoCell)
                 leftPath := .comp (.atom f.id)
                                   (.atom { name := .nested oreName "t", index := 0, kind := .morphism })
                 rightPath := .comp (.atom sId)
                                    (.atom { name := .nested oreName "g", index := 0, kind := .morphism })
                 description := s!"Ore condition: {f.id.name} ∘ t = {sId.name} ∘ g" }
        else none

  { name := s!"{t.name}[S⁻¹]"
    doctrine := t.doctrine
    objects := objects ++ oreApexObjects
    morphisms := t.morphisms ++ roofMorphisms ++ oreWitnesses ++ oreGMorphisms
    axioms := t.axioms ++ equivAxioms ++ oreAxioms }

end CatLab
