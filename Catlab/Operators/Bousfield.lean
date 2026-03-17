/-
  CatLab — Bousfield Localization for Presheaf Categories

  Given a theory and a set of morphisms W, compute the full subcategory
  of W-local objects: objects X such that for every w : A → B in W,
  the induced map Hom(B, X) → Hom(A, X) is a bijection.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Bousfield localization: compute the category of W-local objects.

    An object X is W-local if for every w : A → B in the designated
    set of morphisms, precomposition with w gives a bijection
    Hom(B, X) ≅ Hom(A, X).

    The result includes:
    - Objects: W-local objects (one for each base object, marked local)
    - Morphisms: inherited from the base, restricted to local objects
    - Axioms: the locality conditions (precomposition isos) -/
def bousfieldLocalization (t : Theory) (localMorphisms : List GeneratorId) : Theory :=
  -- Objects: for each base object X, create L_W(X) — the W-local replacement
  let localObjects := t.objects.map fun x =>
    { id := { name := Name.app (.root "L_W") x.id.name, index := 0, kind := .sort }
      description := s!"W-local replacement of {x.id.name}" : Generator0 }

  -- Localization maps: η_X : X → L_W(X)
  let locMaps := t.objects.map fun x =>
    { id := { name := Name.nested (Name.app (.root "L_W") x.id.name) "η", index := 0, kind := .morphism }
      domain := .atom x.id
      codomain := .atom { name := Name.app (.root "L_W") x.id.name, index := 0, kind := .sort }
      description := s!"Localization map X → L_W(X) for {x.id.name}" : Generator1 }

  -- Morphisms between local objects: for each base morphism f : A → B,
  -- an induced L_W(f) : L_W(A) → L_W(B)
  let localMorphisms' := t.morphisms.map fun f =>
    let dn := f.domain.toName
    let cn := f.codomain.toName
    { id := { name := Name.app (.root "L_W") f.id.name, index := 0, kind := .morphism }
      domain := .atom { name := Name.app (.root "L_W") dn, index := 0, kind := .sort }
      codomain := .atom { name := Name.app (.root "L_W") cn, index := 0, kind := .sort }
      description := s!"Localized morphism L_W({f.id.name})" : Generator1 }

  -- Naturality of localization: L_W(f) ∘ η_A = η_B ∘ f
  let naturalityAxioms := t.morphisms.map fun f =>
    let dn := f.domain.toName
    let cn := f.codomain.toName
    let ηA : GeneratorId := { name := Name.nested (Name.app (.root "L_W") dn) "η", index := 0, kind := .morphism }
    let ηB : GeneratorId := { name := Name.nested (Name.app (.root "L_W") cn) "η", index := 0, kind := .morphism }
    let lwF : GeneratorId := { name := Name.app (.root "L_W") f.id.name, index := 0, kind := .morphism }
    { id := gid s!"loc_nat_{f.id.name}" (k := .twoCell)
      leftPath := .comp (.atom ηA) (.atom lwF)
      rightPath := .comp (.atom f.id) (.atom ηB)
      description := s!"Naturality: L_W(f) ∘ η = η ∘ f for {f.id.name}" : Generator2 }

  -- Locality axioms: for each w : A → B in W and each local object L_W(X),
  -- precomposition with w is an iso: Hom(B, L_W(X)) ≅ Hom(A, L_W(X))
  -- We express this by adding a formal section: for each w and X,
  -- a lift morphism making w* invertible.
  let localityLifts := localMorphisms.flatMap fun wId =>
    match t.findMorphism wId.name with
    | some w => t.objects.map fun x =>
      let lwX : GeneratorId := { name := Name.app (.root "L_W") x.id.name, index := 0, kind := .sort }
      let liftName := Name.pair (Name.arrow w.id.name lwX.name (.root "lift")) x.id.name
      { id := { name := liftName, index := 0, kind := .morphism }
        domain := .hom w.domain (.atom lwX)
        codomain := .hom w.codomain (.atom lwX)
        description := s!"Locality lift: Hom(w*, L_W({x.id.name})) section for {wId.name}" : Generator1 }
    | none => []

  -- Locality axioms: w* ∘ lift = id (the precomposition map is an iso)
  let localityAxioms := localMorphisms.flatMap fun wId =>
    match t.findMorphism wId.name with
    | some w => t.objects.flatMap fun x =>
      let lwX : GeneratorId := { name := Name.app (.root "L_W") x.id.name, index := 0, kind := .sort }
      let liftId : GeneratorId := { name := Name.pair (Name.arrow w.id.name lwX.name (.root "lift")) x.id.name, index := 0, kind := .morphism }
      [ { id := gid s!"locality_left_{wId.name}_{x.id.name}" (k := .twoCell)
          leftPath := .comp (.atom liftId) (.atom wId)
          rightPath := .id (.hom w.codomain (.atom lwX))
          description := s!"Left locality: lift ∘ w* = id for {wId.name} at {x.id.name}" : Generator2 },
        { id := gid s!"locality_right_{wId.name}_{x.id.name}" (k := .twoCell)
          leftPath := .comp (.atom wId) (.atom liftId)
          rightPath := .id (.hom w.domain (.atom lwX))
          description := s!"Right locality: w* ∘ lift = id for {wId.name} at {x.id.name}" : Generator2 } ]
    | none => []

  { name := s!"L_W({t.name})"
    doctrine := t.doctrine
    objects := localObjects
    morphisms := locMaps ++ localMorphisms' ++ localityLifts
    axioms := naturalityAxioms ++ localityAxioms }

end CatLab
