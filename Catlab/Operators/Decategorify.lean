/-
  CatLab -- Decategorification

  The deterministic "shadow" operator: collapses a higher-dimensional theory
  down by one categorical level.

  - Objects (vector spaces) ↦ numbers (their dimensions / Euler characteristics)
  - Morphisms (linear maps) ↦ equalities (between numbers)
  - Isomorphism classes replace objects; equations replace 2-cells

  This is the verification engine for Tier 3 categorification:
  if Decategorify(candidate) = original, the categorification is valid.
-/

import Catlab.Core.Theory
import Catlab.Core.Validate
import Catlab.Core.Equality
import Batteries.Data.HashMap

namespace CatLab

/-- Strategy for decategorification -/
inductive DecatStrategy where
  /-- Take isomorphism classes of objects, cardinality of hom-sets -/
  | isoClasses
  /-- Take the Grothendieck group K₀ (formal differences of iso classes) -/
  | grothendieckGroup
  /-- Take Euler characteristic χ (alternating sum of dimensions) -/
  | eulerCharacteristic
  deriving Repr, Inhabited, BEq

/-- Decategorify a theory: collapse it by one categorical dimension.

    Objects become generators of an algebra (their iso classes).
    Morphisms become equations between those generators.
    2-cells are forgotten (they become trivial). -/
def decategorify (t : Theory) (strategy : DecatStrategy := .isoClasses) : Theory :=
  match strategy with
  | .isoClasses =>
    -- Objects become elements of a set (0-generators of the decategorified theory)
    let objNameSet := t.objects.map (·.id.name)
    let morNameSet := t.morphisms.map (·.id.name)
    let decat0 := t.objects.map fun a =>
      { id := gid s!"[{a.id.name}]"
        description := s!"Isomorphism class of {a.id.name}" }
    -- Build renaming: object atoms X ↦ [X]
    let objRenaming : List (Name × Name) := t.objects.map fun a =>
      (a.id.name, .root s!"[{a.id.name}]")
    -- Keep axioms that only reference objects (not morphisms).
    -- Translate object references through the renaming.
    let genIdx := t.generatorIndex
    let decatAxioms := t.axioms.filterMap fun ax =>
      let allAtomNames := ax.leftPath.atoms ++ ax.rightPath.atoms
      -- Check that every atom is either an object or not a known generator
      -- (variables, structural exprs like .unit/.terminal are fine)
      let refsMorphism := allAtomNames.any fun n => morNameSet.any (· == n)
      if refsMorphism then none
      else
        some { id := gid s!"decat_{ax.id.name}"
               leftPath := ax.leftPath.applyNameMap objRenaming
               rightPath := ax.rightPath.applyNameMap objRenaming
               description := s!"Decategorified: {ax.description}" }
    { name := s!"Decat({t.name})"
      doctrine := { doctrine := .Category }
      objects := decat0
      morphisms := []  -- morphisms collapse to equalities
      axioms := decatAxioms }

  | .grothendieckGroup =>
    -- K₀: free abelian group on iso classes, with [A ⊕ B] = [A] + [B]
    let k0obj := { id := gid s!"K₀({t.name})"
                   description := s!"Grothendieck group of {t.name}" }
    -- Each original object gives a generator of K₀
    let generators := t.objects.map fun a =>
      { id := gid s!"[{a.id.name}]"
        domain := .terminal
        codomain := .atom (gid s!"K₀({t.name})")
        description := s!"K₀ class of {a.id.name}" }
    -- Additivity: [A ⊕ B] = [A] + [B] for coproduct-typed morphisms
    -- Scan morphisms for those with coproduct domains/codomains
    let additivityAxioms := t.morphisms.filterMap fun m =>
      match m.domain with
      | .coprod a b =>
        let aName := a.toName.toString
        let bName := b.toName.toString
        let coprodName := s!"{aName}⊔{bName}"
        some { id := gid s!"K₀_add_{m.id.name}"
               leftPath := .atom (gid s!"[{coprodName}]")
               rightPath := .coprod (.atom (gid s!"[{aName}]")) (.atom (gid s!"[{bName}]"))
               description := s!"Additivity: [{coprodName}] = [{aName}] + [{bName}]" : Generator2 }
      | _ => match m.codomain with
        | .coprod a b =>
          let aName := a.toName.toString
          let bName := b.toName.toString
          let coprodName := s!"{aName}⊔{bName}"
          some { id := gid s!"K₀_add_{m.id.name}"
                 leftPath := .atom (gid s!"[{coprodName}]")
                 rightPath := .coprod (.atom (gid s!"[{aName}]")) (.atom (gid s!"[{bName}]"))
                 description := s!"Additivity: [{coprodName}] = [{aName}] + [{bName}]" : Generator2 }
        | _ => none
    { name := s!"K₀({t.name})"
      doctrine := { doctrine := .LawvereTheory }
      objects := [k0obj]
      morphisms := generators
      axioms := additivityAxioms }

  | .eulerCharacteristic =>
    -- χ: alternating sum of dimensions in a chain complex
    let chiObj := { id := gid s!"χ({t.name})"
                    description := s!"Euler characteristic target" }
    let chiMap := { id := gid "χ"
                    domain := .atom (gid t.name)
                    codomain := .atom (gid s!"χ({t.name})")
                    description := "Euler characteristic map" }
    -- Additivity: χ(A ⊕ B) = χ(A) + χ(B)
    let chiAdditivity := t.morphisms.filterMap fun m =>
      match m.domain with
      | .coprod a b =>
        some { id := gid s!"χ_add_{m.id.name}"
               leftPath := .app (.atom (gid "χ")) (.coprod a b)
               rightPath := .coprod (.app (.atom (gid "χ")) a) (.app (.atom (gid "χ")) b)
               description := s!"Additivity: χ(A ⊕ B) = χ(A) + χ(B)" : Generator2 }
      | _ => none
    { name := s!"χ({t.name})"
      doctrine := { doctrine := .Category }
      objects := [chiObj]
      morphisms := [chiMap]
      axioms := chiAdditivity }

/-- Check if a proposed categorification is valid:
    does its decategorification match the target?
    Uses structural comparison (alpha-equivalence on axioms) rather than
    just counting generators. -/
def verifyCategorification (candidate : Theory) (target : Theory)
    (strategy : DecatStrategy := .isoClasses) : Bool :=
  let shadow := decategorify candidate strategy
  -- Check generator counts match
  shadow.objects.length == target.objects.length &&
  shadow.axioms.length >= target.axioms.length &&
  -- Also verify that every target axiom has a corresponding shadow axiom
  -- (using alpha-equivalence for structural comparison)
  target.axioms.all fun tAx =>
    shadow.axioms.any fun sAx =>
      sAx.leftPath.alphaEquiv tAx.leftPath && sAx.rightPath.alphaEquiv tAx.rightPath

end CatLab
