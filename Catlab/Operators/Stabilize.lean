/-
  CatLab — Stabilization / Spectra

  Takes a pointed category and formally inverts the suspension functor,
  producing the category of spectra. A spectrum is a sequence of objects
  (X_0, X_1, X_2, ...) with structure maps σ_n : ΣX_n → X_{n+1}.

  The construction includes:
  - Spectrum objects: graded sequences up to a finite level
  - Structure (bonding) maps between consecutive levels
  - Shift functor Σ : Spectra → Spectra
  - Infinite suspension functor Σ^∞ : C → Spectra
-/

import Catlab.Core.Theory

namespace CatLab

/-- Helper: create a GeneratorId with a graded name -/
private def gradedId (base : Name) (n : Nat) (k : GeneratorKind := .sort) : GeneratorId :=
  { name := .graded base n, kind := k }

/-- Helper: create an Expr.atom with a graded name -/
private def gradedAtom (base : Name) (n : Nat) (k : GeneratorKind := .sort) : Expr :=
  .atom (gradedId base n k)

/-- Stabilize a pointed category: formally invert the suspension functor
    to produce the category of spectra.

    A spectrum object for each base object A is a sequence
      (A_0, A_1, ..., A_maxLevel)
    with bonding maps σ_n : ΣA_n → A_{n+1}.

    The result includes:
    - Spectrum objects at each grading level
    - Structure maps (bonding maps) between consecutive levels
    - Shift functor Σ on spectra (shifts grading up by 1)
    - Infinite suspension functor Σ^∞ embedding the base into spectra -/
def stabilize (t : Theory) (maxLevel : Nat := 3) : Theory :=
  let levels := List.range (maxLevel + 1)

  -- For each base object A, create spectrum objects A_0, A_1, ..., A_maxLevel
  let spectrumObjects := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Sp") a.id.name
    levels.map fun n =>
      { id := gradedId baseName n
        description := s!"Spectrum level {n} of {a.id.name}" : Generator0 }

  -- Suspension objects: ΣA_n for each level (except the last)
  let suspensionObjects := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Sp") a.id.name
    (List.range maxLevel).map fun n =>
      { id := { name := Name.app (.root "Σ") (.graded baseName n), kind := .sort }
        description := s!"Suspension of spectrum level {n} of {a.id.name}" : Generator0 }

  -- Bonding maps: σ_n : ΣA_n → A_{n+1} for each base object and level
  let bondingMaps := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Sp") a.id.name
    (List.range maxLevel).map fun n =>
      let suspObj := Name.app (.root "Σ") (.graded baseName n)
      { id := { name := Name.nested (.graded baseName n) "σ", kind := .morphism }
        domain := .atom { name := suspObj, kind := .sort }
        codomain := gradedAtom baseName (n + 1)
        description := s!"Bonding map σ_{n} : Σ{a.id.name}_{n} → {a.id.name}_{n+1}" : Generator1 }

  -- Suspension maps on spectra: for each morphism f : A → B (atomic endpoints) in the base,
  -- create graded morphisms Sp(f)_n : A_n → B_n at each level
  let atomicMorphisms := t.morphisms.filter fun f =>
    match f.domain, f.codomain with
    | .atom _, .atom _ => true
    | _, _ => false
  let spectrumMorphisms := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let spDom := Name.app (.root "Sp") domName
    let spCod := Name.app (.root "Sp") codName
    levels.map fun n =>
      { id := { name := .graded (Name.app (.root "Sp") f.id.name) n, kind := .morphism }
        domain := gradedAtom spDom n
        codomain := gradedAtom spCod n
        description := s!"Spectrum map Sp({f.id.name})_{n}" : Generator1 }

  -- Shift functor Σ : Spectra → Spectra (shifts grading up by 1)
  -- On objects: (Σ E)_n = E_{n+1}
  let shiftObjects := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Sp") a.id.name
    let shiftedBase := Name.app (.root "Shift") baseName
    levels.map fun n =>
      { id := { name := .graded shiftedBase n, kind := .sort }
        description := s!"Shifted spectrum (ΣE)_{n} = E_{n+1} for {a.id.name}" : Generator0 }

  -- Shift identification axioms: (Σ E)_n = E_{n+1}
  let shiftAxioms := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Sp") a.id.name
    let shiftedBase := Name.app (.root "Shift") baseName
    (List.range maxLevel).map fun n =>
      { id := gid s!"shift_id_{a.id.name}_{n}" (k := .twoCell)
        leftPath := .id (gradedAtom shiftedBase n)
        rightPath := .id (gradedAtom baseName (n + 1))
        description := s!"Shift identification: (ΣE)_{n} = E_{n+1} for {a.id.name}" : Generator2 }

  -- Infinite suspension functor Σ^∞ : C → Spectra
  -- On objects: (Σ^∞ A)_n = Σⁿ A, but we represent it as the spectrum with A at level 0
  let infSuspObjects := t.objects.map fun a =>
    { id := { name := Name.app (.root "Σ∞") a.id.name, kind := .morphism }
      domain := .atom a.id
      codomain := gradedAtom (Name.app (.root "Sp") a.id.name) 0
      description := s!"Infinite suspension Σ^∞ embedding {a.id.name} at level 0" : Generator1 }

  -- Infinite suspension on morphisms: Σ^∞(f) maps to Sp(f)_0
  let infSuspMorphisms := atomicMorphisms.map fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    { id := { name := Name.app (.root "Σ∞") f.id.name, kind := .twoCell }
      leftPath := .comp (.atom { name := Name.app (.root "Σ∞") domName, kind := .morphism })
                        (.atom { name := .graded (Name.app (.root "Sp") f.id.name) 0, kind := .morphism })
      rightPath := .comp (.atom f.id)
                         (.atom { name := Name.app (.root "Σ∞") codName, kind := .morphism })
      description := s!"Σ^∞ naturality for {f.id.name}" : Generator2 }

  -- Bonding map naturality: for each f : A → B (atomic), σ_n commutes with Sp(f)
  let bondingNaturality := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let spDom := Name.app (.root "Sp") domName
    let spCod := Name.app (.root "Sp") codName
    (List.range maxLevel).map fun n =>
      let σA := GeneratorId.mk (Name.nested (.graded spDom n) "σ") 0 .morphism
      let σB := GeneratorId.mk (Name.nested (.graded spCod n) "σ") 0 .morphism
      let spF_n := GeneratorId.mk (.graded (Name.app (.root "Sp") f.id.name) n) 0 .morphism
      let spF_n1 := GeneratorId.mk (.graded (Name.app (.root "Sp") f.id.name) (n + 1)) 0 .morphism
      { id := gid s!"bonding_nat_{f.id.name}_{n}" (k := .twoCell)
        leftPath := .comp (.atom σA) (.atom spF_n1)
        rightPath := .comp (.atom spF_n) (.atom σB)
        description := s!"Bonding naturality: Sp(f)_{n+1} ∘ σ_A = σ_B ∘ Sp(f)_{n}" : Generator2 }

  { name := s!"Spectra({t.name})"
    doctrine := { doctrine := .StableCategory }
    objects := t.objects ++ spectrumObjects ++ suspensionObjects ++ shiftObjects
    morphisms := t.morphisms ++ bondingMaps ++ spectrumMorphisms ++ infSuspObjects
    axioms := shiftAxioms ++ infSuspMorphisms }

end CatLab
