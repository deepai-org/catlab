/-
  CatLab — Family Construction (Fam(C))

  Takes a category C and constructs Fam(C), the category of set-indexed
  families of objects of C.

  Objects: pairs (I, X) where I is a set and X : I → Ob(C) is a family
  Morphisms: (I, X) → (J, Y) consist of a function f : I → J together
             with a family of morphisms {h_i : X(i) → Y(f(i))}_{i ∈ I}
-/

import Catlab.Core.Theory

namespace CatLab

/-- Helper to create a GeneratorId with a structured Name -/
private def famGid (n : Name) (k : GeneratorKind := .sort) : GeneratorId :=
  { name := n, index := 0, kind := k }

/-- Compute Fam(C), the family construction over C.

    Objects: set-indexed families of objects of C. In our finite presentation,
    an object is a finite list of objects [X₁, …, Xₙ] (indexed by {1,…,n}).

    Morphisms: (I, X) → (J, Y) is a reindexing function σ : I → J together
    with component morphisms hᵢ : Xᵢ → Y_{σ(i)} for each i ∈ I.

    This is the free coproduct completion of C when C lacks coproducts. -/
def familyCategory (t : Theory) : Theory :=
  let baseName := Name.root t.name

  -- Empty family (indexed by ∅)
  let emptyFamily : Generator0 :=
    { id := famGid (.app (.root "Fam") (.graded baseName 0))
      description := "Empty family" }

  -- Singleton families: each object A of C gives the family {A}
  let singletonFamilies := t.objects.map fun a =>
    { id := famGid (.app (.root "Fam") (.graded a.id.name 1))
      description := s!"Singleton family ({a.id.name.toString})" : Generator0 }

  -- Pair families: each pair (A, B) gives the family {A, B}
  let pairFamilies := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      let pName := Name.pair a.id.name b.id.name
      { id := famGid (.app (.root "Fam") (.graded pName 2))
        description := s!"Family ({a.id.name.toString}, {b.id.name.toString})" : Generator0 }

  -- Morphisms between singleton families: {A} → {B} is just a morphism A → B
  let singletonMorphisms := t.morphisms.map fun f =>
    let domObjName := match f.domain with | .atom g => g.name | _ => .root "?"
    let codObjName := match f.codomain with | .atom g => g.name | _ => .root "?"
    let domId := famGid (.app (.root "Fam") (.graded domObjName 1))
    let codId := famGid (.app (.root "Fam") (.graded codObjName 1))
    { id := famGid (.app (.root "fam") f.id.name) .morphism
      domain := .atom domId
      codomain := .atom codId
      description := s!"Family morphism from singleton: {f.id.name}" : Generator1 }

  -- Diagonal morphism: {A} → {A, A}
  let diagonalMorphisms := t.objects.map fun a =>
    let singleName := .app (.root "Fam") (.graded a.id.name 1)
    let pairName := .app (.root "Fam") (.graded (Name.pair a.id.name a.id.name) 2)
    { id := famGid (.nested (.app (.root "Fam") a.id.name) "Δ") .morphism
      domain := .atom (famGid singleName)
      codomain := .atom (famGid pairName)
      description := s!"Diagonal" : Generator1 }

  -- Fold morphism: {A, A} → {A}
  let foldMorphisms := t.objects.map fun a =>
    let singleName := .app (.root "Fam") (.graded a.id.name 1)
    let pairName := .app (.root "Fam") (.graded (Name.pair a.id.name a.id.name) 2)
    { id := famGid (.nested (.app (.root "Fam") a.id.name) "∇") .morphism
      domain := .atom (famGid pairName)
      codomain := .atom (famGid singleName)
      description := s!"Fold" : Generator1 }

  -- Projection morphisms: {A, B} → {A} and {A, B} → {B}
  let projMorphisms := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      let pairName := Name.app (.root "Fam") (.graded (Name.pair a.id.name b.id.name) 2)
      let singleA := Name.app (.root "Fam") (.graded a.id.name 1)
      let singleB := Name.app (.root "Fam") (.graded b.id.name 1)
      [ { id := famGid (.nested pairName "π₁") .morphism
          domain := .atom (famGid pairName)
          codomain := .atom (famGid singleA)
          description := "Project to first component" : Generator1 },
        { id := famGid (.nested pairName "π₂") .morphism
          domain := .atom (famGid pairName)
          codomain := .atom (famGid singleB)
          description := "Project to second component" : Generator1 } ]

  { name := s!"Fam({t.name})"
    doctrine := t.doctrine
    objects := [emptyFamily] ++ singletonFamilies ++ pairFamilies
    morphisms := singletonMorphisms ++ diagonalMorphisms ++ foldMorphisms ++ projMorphisms
    axioms := [] }

end CatLab
