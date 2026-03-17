/-
  CatLab — Joyal-Street-Verity Int Construction

  Given a traced monoidal category C, the Int construction produces a
  compact closed category Int(C) where:

  - Objects: pairs (A⁺, A⁻)
  - Morphisms: (A⁺,A⁻) → (B⁺,B⁻) are morphisms A⁺ ⊗ B⁻ → B⁺ ⊗ A⁻
  - Composition uses the trace to close off the feedback loop
  - Every object (A⁺, A⁻) has a dual (A⁻, A⁺)
-/

import Catlab.Core.Theory

namespace CatLab

/-- Build the Int construction Int(C).

    Takes a theory C (assumed traced monoidal) and produces a compact
    closed category whose objects are pairs and whose morphisms route
    through tensor products, using the trace for composition. -/
def intConstruction (t : Theory) : Theory :=
  -- Objects: pairs (A⁺, A⁻) for each pair of objects in C
  let intObjects := t.objects.flatMap fun aPlus =>
    t.objects.map fun aMinus =>
      let name : Name := .pair aPlus.id.name aMinus.id.name
      ({ id := { name, kind := .sort }
         description := s!"Int object ({aPlus.id}⁺, {aMinus.id}⁻)" } : Generator0)

  -- Morphisms: (A⁺,A⁻) → (B⁺,B⁻) is a morphism A⁺ ⊗ B⁻ → B⁺ ⊗ A⁻
  let intMorphisms := t.objects.flatMap fun aPlus =>
    t.objects.flatMap fun aMinus =>
      t.objects.flatMap fun bPlus =>
        t.objects.map fun bMinus =>
          let srcName : Name := .pair aPlus.id.name aMinus.id.name
          let tgtName : Name := .pair bPlus.id.name bMinus.id.name
          let morphName : Name := .arrow srcName tgtName (.root "int")
          ({ id := { name := morphName, kind := .morphism }
             domain := .tensor (.atom aPlus.id) (.atom bMinus.id)
             codomain := .tensor (.atom bPlus.id) (.atom aMinus.id)
             description := s!"Int morphism: {aPlus.id} ⊗ {bMinus.id} → {bPlus.id} ⊗ {aMinus.id}" }
            : Generator1)

  -- Identity: id on (A⁺, A⁻) is the symmetry σ : A⁺ ⊗ A⁻ → A⁺ ⊗ A⁻
  -- (which is just the identity morphism in the underlying category)
  let identityAxioms := t.objects.flatMap fun aPlus =>
    t.objects.map fun aMinus =>
      let pairName : Name := .pair aPlus.id.name aMinus.id.name
      let idMorphName : Name := .arrow pairName pairName (.root "int")
      ({ id := { name := .nested pairName "id_law", kind := .twoCell }
         leftPath := .atom { name := idMorphName, kind := .morphism }
         rightPath := .id (.tensor (.atom aPlus.id) (.atom aMinus.id))
         description := s!"Identity on ({aPlus.id}, {aMinus.id}) is id on tensor" }
        : Generator2)

  -- Composition uses trace: given f : A⁺⊗B⁻ → B⁺⊗A⁻ and g : B⁺⊗C⁻ → C⁺⊗B⁻,
  -- their composite is Tr^{B⁺,B⁻}(rearrange ; (f ⊗ g) ; rearrange)
  -- We record this as a structural axiom schema.
  let compAxiom : Generator2 :=
    { id := gid "int_comp_law" (k := .twoCell)
      quantifiers :=
        [ { name := "A+", kind := .sort }
        , { name := "A-", kind := .sort }
        , { name := "B+", kind := .sort }
        , { name := "B-", kind := .sort }
        , { name := "C+", kind := .sort }
        , { name := "C-", kind := .sort }
        , { name := "f", kind := .morphism
            domain := some (.tensor (.var "A+") (.var "B-"))
            codomain := some (.tensor (.var "B+") (.var "A-")) }
        , { name := "g", kind := .morphism
            domain := some (.tensor (.var "B+") (.var "C-"))
            codomain := some (.tensor (.var "C+") (.var "B-")) } ]
      leftPath := .var "g∘f"  -- the composite in Int(C)
      rightPath := .var "Tr(f,g)"  -- trace-based composition
      description := "Composition in Int(C) uses the trace to close the B⁺/B⁻ feedback loop" }

  -- Duality: (A⁺, A⁻)* = (A⁻, A⁺) — compact closure
  let dualityAxioms := t.objects.flatMap fun aPlus =>
    t.objects.map fun aMinus =>
      let pairName : Name := .pair aPlus.id.name aMinus.id.name
      let dualName : Name := .pair aMinus.id.name aPlus.id.name
      ({ id := { name := .nested pairName "dual", kind := .twoCell }
         leftPath := .atom { name := .op pairName, kind := .sort }
         rightPath := .atom { name := dualName, kind := .sort }
         description := s!"Dual: ({aPlus.id}, {aMinus.id})* = ({aMinus.id}, {aPlus.id})" }
        : Generator2)

  -- Unit and counit for compact closure
  let unitAxioms := t.objects.flatMap fun aPlus =>
    t.objects.map fun aMinus =>
      let pairName : Name := .pair aPlus.id.name aMinus.id.name
      let dualName : Name := .pair aMinus.id.name aPlus.id.name
      let tensorName : Name := .tensor pairName dualName
      let unitName : Name := .nested tensorName "eta"
      ({ id := { name := unitName, kind := .morphism }
         domain := .unit
         codomain := .tensor
           (.atom { name := pairName, kind := .sort })
           (.atom { name := dualName, kind := .sort })
         description := s!"Unit: I → ({aPlus.id},{aMinus.id}) ⊗ ({aMinus.id},{aPlus.id})" }
        : Generator1)

  let counitMorphisms := t.objects.flatMap fun aPlus =>
    t.objects.map fun aMinus =>
      let pairName : Name := .pair aPlus.id.name aMinus.id.name
      let dualName : Name := .pair aMinus.id.name aPlus.id.name
      let tensorName : Name := .tensor dualName pairName
      let counitName : Name := .nested tensorName "epsilon"
      ({ id := { name := counitName, kind := .morphism }
         domain := .tensor
           (.atom { name := dualName, kind := .sort })
           (.atom { name := pairName, kind := .sort })
         codomain := .unit
         description := s!"Counit: ({aMinus.id},{aPlus.id}) ⊗ ({aPlus.id},{aMinus.id}) → I" }
        : Generator1)

  { name := s!"Int({t.name})"
    doctrine := { doctrine := .SymmetricMonoidal
                  constraints := ["compact closed"] }
    objects := intObjects
    morphisms := intMorphisms ++ unitAxioms ++ counitMorphisms
    axioms := identityAxioms ++ [compAxiom] ++ dualityAxioms }

end CatLab
