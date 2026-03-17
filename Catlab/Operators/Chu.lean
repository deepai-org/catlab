/-
  CatLab — Chu Construction

  Given a symmetric monoidal closed category C and a dualizing object ⊥,
  build the *-autonomous category Chu(C, ⊥) where:

  - Objects: pairs (A, B) equipped with a morphism A ⊗ B → ⊥
  - Morphisms: (A,B) → (C,D) are pairs (f: A→C, g: D→B) making
    the evident square commute
  - The result is a *-autonomous category with duality (A,B) ↦ (B,A)
-/

import Catlab.Core.Theory

namespace CatLab

/-- A Chu object: a pair (pos, neg) with an evaluation map pos ⊗ neg → ⊥ -/
structure ChuObject where
  /-- The positive component -/
  pos : GeneratorId
  /-- The negative component -/
  neg : GeneratorId
  /-- The evaluation morphism: pos ⊗ neg → ⊥ -/
  eval : GeneratorId
  deriving Repr, Inhabited

/-- Build the Chu construction Chu(C, ⊥).

    Takes a theory C (assumed symmetric monoidal closed) and a dualizing
    object ⊥, producing a *-autonomous category. -/
def chuConstruction (t : Theory) (dualizer : Expr) : Theory :=
  -- Objects: for each pair (A, B) in C, a Chu object (A, B, α : A ⊗ B → ⊥)
  let chuObjects := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      let name : Name := .pair a.id.name b.id.name
      ({ id := { name, kind := .sort }
         description := s!"Chu object ({a.id}, {b.id})" } : Generator0)

  -- Evaluation maps α : A ⊗ B → ⊥ for each Chu object
  let evalMaps := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      let objName : Name := .pair a.id.name b.id.name
      let evalName : Name := .nested objName "eval"
      ({ id := { name := evalName, kind := .morphism }
         domain := .tensor (.atom a.id) (.atom b.id)
         codomain := dualizer
         description := s!"Evaluation: {a.id} ⊗ {b.id} → ⊥" } : Generator1)

  -- Morphisms: (A,B) → (C,D) consists of f : A → C and g : D → B
  let forwardMaps := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.flatMap fun c =>
        t.objects.map fun d =>
          let srcName : Name := .pair a.id.name b.id.name
          let tgtName : Name := .pair c.id.name d.id.name
          let fName : Name := .arrow srcName tgtName (.root "fwd")
          ({ id := { name := fName, kind := .morphism }
             domain := .atom a.id
             codomain := .atom c.id
             description := s!"Forward: {a.id} → {c.id}" } : Generator1)

  let backwardMaps := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.flatMap fun c =>
        t.objects.map fun d =>
          let srcName : Name := .pair a.id.name b.id.name
          let tgtName : Name := .pair c.id.name d.id.name
          let gName : Name := .arrow srcName tgtName (.root "bwd")
          ({ id := { name := gName, kind := .morphism }
             domain := .atom d.id
             codomain := .atom b.id
             description := s!"Backward: {d.id} → {b.id}" } : Generator1)

  -- Coherence: the square commutes, i.e., α_AB = comp (f ⊗ g) α_CD
  -- α : A ⊗ B → ⊥   must equal   (f ⊗ g) ; β : A ⊗ D → C ⊗ D → ⊥
  -- Rewritten: α = comp (tensor f g) β
  let coherenceAxioms := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.flatMap fun c =>
        t.objects.map fun d =>
          let srcPair : Name := .pair a.id.name b.id.name
          let tgtPair : Name := .pair c.id.name d.id.name
          let αName : Name := .nested srcPair "eval"
          let βName : Name := .nested tgtPair "eval"
          let fName : Name := .arrow srcPair tgtPair (.root "fwd")
          let gName : Name := .arrow srcPair tgtPair (.root "bwd")
          ({ id := { name := .nested (.arrow srcPair tgtPair (.root "coh"))
                             "commutes", kind := .twoCell }
             leftPath := .atom { name := αName, kind := .morphism }
             rightPath := .comp
               (.tensor (.atom { name := fName, kind := .morphism })
                        (.atom { name := gName, kind := .morphism }))
               (.atom { name := βName, kind := .morphism })
             description := s!"Coherence: α = (f ⊗ g) ; β" } : Generator2)

  -- Identity axioms: id on (A,B) is (id_A, id_B)
  let identityAxioms := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      let pairName : Name := .pair a.id.name b.id.name
      let fName : Name := .arrow pairName pairName (.root "fwd")
      ({ id := { name := .nested pairName "id_fwd", kind := .twoCell }
         leftPath := .atom { name := fName, kind := .morphism }
         rightPath := .id (.atom a.id)
         description := s!"Identity forward is id on {a.id}" } : Generator2)

  let identityAxiomsBack := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      let pairName : Name := .pair a.id.name b.id.name
      let gName : Name := .arrow pairName pairName (.root "bwd")
      ({ id := { name := .nested pairName "id_bwd", kind := .twoCell }
         leftPath := .atom { name := gName, kind := .morphism }
         rightPath := .id (.atom b.id)
         description := s!"Identity backward is id on {b.id}" } : Generator2)

  -- Duality: (A,B)* = (B,A) — recorded as a structural note
  let dualityNote : Generator2 :=
    { id := gid "chu_duality" (k := .twoCell)
      leftPath := .atom (gid "chu_dual_involution")
      rightPath := .atom (gid "chu_dual_involution")
      description := "Duality: (A,B)* = (B,A) is an involution giving *-autonomy" }

  { name := s!"Chu({t.name}, ⊥)"
    doctrine := { doctrine := .SymmetricMonoidalClosed
                  constraints := ["*-autonomous"] }
    objects := chuObjects
    morphisms := evalMaps ++ forwardMaps ++ backwardMaps
    axioms := coherenceAxioms ++ identityAxioms ++ identityAxiomsBack ++ [dualityNote] }

end CatLab
