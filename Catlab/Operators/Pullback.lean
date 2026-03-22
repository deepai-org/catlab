/-
  CatLab -- Pullback of Theories (Fibered Product)

  The pullback of two morphisms f : T₁ → T₃ and g : T₂ → T₃ is the
  fibered product T₁ ×_{T₃} T₂: the theory of pairs (x ∈ T₁, y ∈ T₂)
  such that f(x) = g(y) in T₃.

  This is the dual of Pushout (amalgamated sum). Where pushout is "merge",
  pullback is "diff" / "intersection":

    theoryProduct T₁ T₂       = pullback (terminalMorphism T₁) (terminalMorphism T₂)
    theoryIntersect T₁ T₂     = pullback (inclusion T₁ T₃) (inclusion T₂ T₃)

  Algorithm:
    Given f : T₁ → T₃ and g : T₂ → T₃:
    1. For each object pair (x ∈ T₁, y ∈ T₂): if f(x) = g(y) in T₃,
       emit a pullback object (x, y).
    2. For each morphism pair (m ∈ T₁, n ∈ T₂): if f(m) = g(n) in T₃
       AND their domains/codomains are paired, emit a pullback morphism (m, n).
    3. For each axiom pair (a ∈ T₁, b ∈ T₂): if translating both through the
       object/morphism pairing yields the same equation, emit a pullback axiom.

  The result is the maximal shared sub-structure: the largest theory that
  maps into both T₁ and T₂ compatibly over T₃.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Catlab.Core.Primitives

namespace CatLab

/-- The pullback T₁ ×_{T₃} T₂ of f : T₁ → T₃ and g : T₂ → T₃.
    Returns `none` when f and g have different target theories. -/
def theoryPullback (f g : TheoryMorphism) : Option Theory :=
  if f.target.name != g.target.name then none
  else
    let t1 := f.source
    let t2 := g.source
    let t3 := f.target

    -- Step 1: pair objects where f(x) = g(y) in T₃
    -- Build a map from T₃-object-name → T₂-object for reverse lookup
    let t2ObjByImage : List (Name × Generator0) :=
      t2.objects.filterMap fun o =>
        match g.onObjects.apply o.id with
        | .atom gid => some (gid.name, o)
        | _ => none

    let pairedObjects : List (Generator0 × Generator0) :=
      t1.objects.filterMap fun o1 =>
        match f.onObjects.apply o1.id with
        | .atom fImg =>
          t2ObjByImage.find? (fun (n, _) => n == fImg.name) |>.map (·.2) |>.map (o1, ·)
        | _ => none

    -- Build name maps: T₁-name → pullback-name, T₂-name → pullback-name
    -- Pullback object names: use T₁'s name (canonical choice)
    let objMap1 : List (Name × Name) := pairedObjects.map fun (o1, _) => (o1.id.name, o1.id.name)
    let objMap2 : List (Name × Name) := pairedObjects.map fun (o1, o2) => (o2.id.name, o1.id.name)

    let renameFromT1 (n : Name) : Name :=
      (objMap1.find? (·.1 == n)).map (·.2) |>.getD n
    let renameFromT2 (n : Name) : Name :=
      (objMap2.find? (·.1 == n)).map (·.2) |>.getD n

    let pullbackObjects : List Generator0 :=
      pairedObjects.map fun (o1, _) => o1

    -- Step 2: pair morphisms where f(m) = g(n) in T₃
    -- AND domains/codomains are themselves paired objects
    let pairedObjNames1 : List Name := pairedObjects.map (·.1.id.name)
    let pairedObjNames2 : List Name := pairedObjects.map (·.2.id.name)

    -- Check if all atoms in an expr are paired objects from a given theory
    let allAtomsPaired (e : Expr) (paired : List Name) : Bool :=
      e.atoms.all fun n => paired.any (· == n) || n == Name.root "terminal" || n == Name.root "unit"

    let t2MorByImage : List (Name × Generator1) :=
      t2.morphisms.filterMap fun m =>
        match g.onMorphisms.apply m.id with
        | .atom gid => some (gid.name, m)
        | _ => none

    let pairedMorphisms : List (Generator1 × Generator1) :=
      t1.morphisms.filterMap fun m1 =>
        -- m1's domain/codomain atoms must all be in paired objects
        if !allAtomsPaired m1.domain pairedObjNames1 ||
           !allAtomsPaired m1.codomain pairedObjNames1 then none
        else
          match f.onMorphisms.apply m1.id with
          | .atom fImg =>
            match t2MorByImage.find? (fun (n, _) => n == fImg.name) with
            | some (_, m2) =>
              -- m2's domain/codomain atoms must also be in paired objects
              if !allAtomsPaired m2.domain pairedObjNames2 ||
                 !allAtomsPaired m2.codomain pairedObjNames2 then none
              else some (m1, m2)
            | none => none
          | _ => none

    let morMap1 : List (Name × Name) := pairedMorphisms.map fun (m1, _) => (m1.id.name, m1.id.name)
    let morMap2 : List (Name × Name) := pairedMorphisms.map fun (m1, m2) => (m2.id.name, m1.id.name)

    let renameFromT1Full (n : Name) : Name :=
      (objMap1.find? (·.1 == n)).map (·.2) |>.getD
        ((morMap1.find? (·.1 == n)).map (·.2) |>.getD n)
    let renameFromT2Full (n : Name) : Name :=
      (objMap2.find? (·.1 == n)).map (·.2) |>.getD
        ((morMap2.find? (·.1 == n)).map (·.2) |>.getD n)

    let pullbackMorphisms : List Generator1 :=
      pairedMorphisms.map fun (m1, _) =>
        { m1 with
          domain   := m1.domain.mapNames renameFromT1
          codomain := m1.codomain.mapNames renameFromT1 }

    -- Step 3: pair axioms
    -- An axiom from T₁ is in the pullback if there exists a matching axiom in T₂
    -- such that after renaming through the pairing, they state the same equation.
    let pairedMorNames1 := pairedMorphisms.map (·.1.id.name)
    let filteredAxioms := t1.axioms.filter fun a1 =>
      -- All atoms in the axiom must reference paired generators
      let allAtoms := a1.leftPath.atoms ++ a1.rightPath.atoms
      let allPaired := allAtoms.all fun n =>
        pairedObjNames1.any (· == n) || pairedMorNames1.any (· == n)
      if !allPaired then false
      else
        -- Check if T₂ has a corresponding axiom
        let lhs1 := a1.leftPath.mapNames renameFromT1Full
        let rhs1 := a1.rightPath.mapNames renameFromT1Full
        t2.axioms.any fun a2 =>
          let lhs2 := a2.leftPath.mapNames renameFromT2Full
          let rhs2 := a2.rightPath.mapNames renameFromT2Full
          (lhs1 == lhs2 && rhs1 == rhs2) || (lhs1 == rhs2 && rhs1 == lhs2)
    let pullbackAxioms := filteredAxioms.map fun a =>
      { a with
        leftPath  := a.leftPath.mapNames renameFromT1Full
        rightPath := a.rightPath.mapNames renameFromT1Full }

    some {
      name      := s!"{t1.name} ×_({t3.name}) {t2.name}"
      doctrine  := if t1.doctrine.doctrine.rank <= t2.doctrine.doctrine.rank
                   then t1.doctrine else t2.doctrine
      objects   := pullbackObjects
      morphisms := pullbackMorphisms
      axioms    := pullbackAxioms }

/-- A pullback cone: the apex theory P plus the two projection morphisms
    (cone legs) mapping P → T₁ and P → T₂. -/
structure PullbackCone where
  apex : Theory
  /-- Left projection: P → T₁ -/
  leftProj : TheoryMorphism
  /-- Right projection: P → T₂ -/
  rightProj : TheoryMorphism

/-- Compute the pullback cone with correct projection mappings. -/
def pullbackCone (f g : TheoryMorphism) : Option PullbackCone :=
  if f.target.name != g.target.name then none
  else
    let t1 := f.source
    let t2 := g.source

    match theoryPullback f g with
    | none => none
    | some apex =>
      -- Left projection: P → T₁. Each pullback generator maps to its T₁ origin.
      -- Since we used T₁ names for the pullback, this is the identity on names.
      let leftOnObjects := GeneratorMap.ofList
        (apex.objects.map fun o => (o.id, .atom o.id))
      let leftOnMorphisms := GeneratorMap.ofList
        (apex.morphisms.map fun m => (m.id, .atom m.id))
      let leftProj : TheoryMorphism :=
        { name := s!"π₁ : {apex.name} → {t1.name}"
          source := apex
          target := t1
          onObjects := leftOnObjects
          onMorphisms := leftOnMorphisms }

      -- Right projection: P → T₂. Each pullback generator maps to its T₂ pair.
      -- We need the reverse mapping: pullback-name → T₂-name
      -- Rebuild the pairing to get the T₂ names
      let t2ObjByImage : List (Name × Generator0) :=
        t2.objects.filterMap fun o =>
          match g.onObjects.apply o.id with
          | .atom gid => some (gid.name, o)
          | _ => none

      let pairedObjects : List (Generator0 × Generator0) :=
        t1.objects.filterMap fun o1 =>
          match f.onObjects.apply o1.id with
          | .atom fImg =>
            t2ObjByImage.find? (fun (n, _) => n == fImg.name) |>.map (·.2) |>.map (o1, ·)
          | _ => none

      let t2MorByImage : List (Name × Generator1) :=
        t2.morphisms.filterMap fun m =>
          match g.onMorphisms.apply m.id with
          | .atom gid => some (gid.name, m)
          | _ => none

      let pairedMorphisms : List (Generator1 × Generator1) :=
        t1.morphisms.filterMap fun m1 =>
          match f.onMorphisms.apply m1.id with
          | .atom fImg =>
            t2MorByImage.find? (fun (n, _) => n == fImg.name) |>.map (·.2) |>.map (m1, ·)
          | _ => none

      let rightOnObjects := GeneratorMap.ofList
        (pairedObjects.filterMap fun (o1, o2) =>
          -- Only include objects that are in the apex
          if apex.objects.any (fun o => o.id.name == o1.id.name)
          then some (o1.id, .atom o2.id)
          else none)
      let rightOnMorphisms := GeneratorMap.ofList
        (pairedMorphisms.filterMap fun (m1, m2) =>
          if apex.morphisms.any (fun m => m.id.name == m1.id.name)
          then some (m1.id, .atom m2.id)
          else none)
      let rightProj : TheoryMorphism :=
        { name := s!"π₂ : {apex.name} → {t2.name}"
          source := apex
          target := t2
          onObjects := rightOnObjects
          onMorphisms := rightOnMorphisms }

      some { apex, leftProj, rightProj }

/-- Product as pullback over ⊤ (terminal theory).
    Dual of theoryCoproduct = pushout over ⊥. -/
def theoryProduct' (t1 t2 : Theory) : Option Theory :=
  let term := terminalTheory
  let f := terminalMorphism t1
  let g := terminalMorphism t2
  theoryPullback f g

end CatLab
