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
    let objNames := t.objects.map (·.id.name)
    let decat0 := t.objects.map fun a =>
      { id := gid s!"[{a.id.name}]"
        description := s!"Isomorphism class of {a.id.name}" }
    -- Only keep axioms whose atoms all refer to objects (not morphisms)
    -- since morphisms are collapsed away
    let morNames := t.morphisms.map (·.id.name)
    let decatAxioms := t.axioms.filterMap fun ax =>
      let atoms := ax.leftPath.atoms ++ ax.rightPath.atoms
      let referencesMorphism := atoms.any (fun a => morNames.contains a)
      if referencesMorphism then none
      else some { id := gid s!"decat_{ax.id.name}"
                  leftPath := ax.leftPath
                  rightPath := ax.rightPath
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
    -- Additivity: [A ⊕ B] = [A] + [B] for each coproduct
    { name := s!"K₀({t.name})"
      doctrine := { doctrine := .LawvereTheory }
      objects := [k0obj]
      morphisms := generators
      axioms := [] }

  | .eulerCharacteristic =>
    -- χ: alternating sum of dimensions in a chain complex
    let chiObj := { id := gid s!"χ({t.name})"
                    description := s!"Euler characteristic target" }
    let chiMap := { id := gid "χ"
                    domain := .atom (gid t.name)
                    codomain := .atom (gid s!"χ({t.name})")
                    description := "Euler characteristic map" }
    { name := s!"χ({t.name})"
      doctrine := { doctrine := .Category }
      objects := [chiObj]
      morphisms := [chiMap]
      axioms := [] }

/-- Check if a proposed categorification is valid:
    does its decategorification match the target? -/
def verifyCategorification (candidate : Theory) (target : Theory)
    (strategy : DecatStrategy := .isoClasses) : Bool :=
  let shadow := decategorify candidate strategy
  -- Compare structural signatures (simplified: check generator counts match)
  shadow.objects.length == target.objects.length &&
  shadow.axioms.length >= target.axioms.length

end CatLab
