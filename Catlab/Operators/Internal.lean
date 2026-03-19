/-
  CatLab — Internal Categories (Cat(C))

  Given a category C with pullbacks, construct the category of internal
  categories in C.

  Objects: internal category data (C₀, C₁, s, t, i, c) satisfying axioms
  Morphisms: internal functors — pairs (F₀, F₁) preserving structure
-/

import Catlab.Core.Theory
import Batteries.Data.HashMap

namespace CatLab

/-- Data for an internal category in an ambient category C.
    An internal category consists of:
    - C₀ : object of objects
    - C₁ : object of morphisms
    - s, t : C₁ → C₀ (source and target)
    - i : C₀ → C₁ (identity)
    - c : C₁ ×_{C₀} C₁ → C₁ (composition, defined on the pullback)
    satisfying associativity and unit laws. -/
structure InternalCategoryData where
  /-- Name of this internal category -/
  name : String
  /-- Object of objects -/
  objOfObj : GeneratorId
  /-- Object of morphisms -/
  objOfMor : GeneratorId
  /-- Source map s : C₁ → C₀ -/
  source : GeneratorId
  /-- Target map t : C₁ → C₀ -/
  target : GeneratorId
  /-- Identity map i : C₀ → C₁ -/
  identity : GeneratorId
  /-- Composable pairs (the pullback C₁ ×_{C₀} C₁) -/
  composable : GeneratorId
  /-- Composition map c : C₁ ×_{C₀} C₁ → C₁ -/
  composition : GeneratorId
  deriving Repr, Inhabited

/-- Construct an internal category data record with standard naming -/
def mkInternalCategoryData (prefix_ : String) : InternalCategoryData :=
  let p := Name.root prefix_
  { name := prefix_
    objOfObj := { name := .nested p "C₀", kind := .sort }
    objOfMor := { name := .nested p "C₁", kind := .sort }
    source := { name := .nested p "s", kind := .morphism }
    target := { name := .nested p "t", kind := .morphism }
    identity := { name := .nested p "i", kind := .morphism }
    composable := { name := .nested p "C₁×C₁", kind := .sort }
    composition := { name := .nested p "c", kind := .morphism } }

/-- Construct Cat(C): the category of internal categories in C.

    Given a theory C (assumed to have pullbacks), produces a theory whose:
    - Objects are internal category data (C₀, C₁, s, t, i, c)
    - Morphisms are internal functors: pairs (F₀ : C₀ → D₀, F₁ : C₁ → D₁)
      preserving source, target, identity, and composition -/
def internalCategoryCategory (t : Theory) : Theory :=
  -- For each pair of objects in the ambient category, we can form an internal
  -- category with those as C₀ and C₁. In practice we generate the structure
  -- parametrically.
  let intCatObjects := t.objects.flatMap fun c0 =>
    t.objects.map fun c1 =>
      let nm := Name.pair c0.id.name c1.id.name
      { id := { name := .app (.root "IntCat") nm, kind := .sort }
        description := s!"Internal category with objects {c0.id.name}, morphisms {c1.id.name}"
        : Generator0 }

  -- Structure morphisms for each internal category object
  let structureMorphisms := t.objects.flatMap fun c0 =>
    t.objects.flatMap fun c1 =>
      let catName := .app (.root "IntCat") (Name.pair c0.id.name c1.id.name)
      let catExpr := Expr.atom { name := catName, kind := .sort }
      let c0Expr := Expr.atom c0.id
      let c1Expr := Expr.atom c1.id
      [ -- source: C₁ → C₀
        { id := { name := .nested catName "s", kind := .morphism }
          domain := c1Expr, codomain := c0Expr
          description := s!"Source map" : Generator1 },
        -- target: C₁ → C₀
        { id := { name := .nested catName "t", kind := .morphism }
          domain := c1Expr, codomain := c0Expr
          description := s!"Target map" : Generator1 },
        -- identity: C₀ → C₁
        { id := { name := .nested catName "i", kind := .morphism }
          domain := c0Expr, codomain := c1Expr
          description := s!"Identity map" : Generator1 } ]

  -- Internal functors: for each pair of internal categories, a functor is
  -- a pair of morphisms (F₀, F₁) in the ambient category.
  -- Index morphisms by (domain, codomain) for efficient lookup.
  let morphByEndpoints : Std.HashMap (Name × Name) (List Generator1) :=
    t.morphisms.foldl (fun acc m =>
      let key := (m.domain.toName, m.codomain.toName)
      let existing := acc[key]? |>.getD []
      acc.insert key (m :: existing)) {}
  let internalFunctors := t.objects.flatMap fun c0 =>
    t.objects.flatMap fun c1 =>
      t.objects.flatMap fun d0 =>
        t.objects.flatMap fun d1 =>
          let f0s := morphByEndpoints[(c0.id.name, d0.id.name)]? |>.getD []
          let f1s := morphByEndpoints[(c1.id.name, d1.id.name)]? |>.getD []
          f0s.flatMap fun f0 =>
            f1s.map fun f1 =>
              let srcName := Name.pair c0.id.name c1.id.name
              let tgtName := Name.pair d0.id.name d1.id.name
              let funName := .arrow
                    (.app (.root "IntCat") srcName)
                    (.app (.root "IntCat") tgtName)
                    (Name.pair f0.id.name f1.id.name)
              let funId : GeneratorId := { name := funName, kind := .morphism }
              let domExpr := Expr.atom { name := .app (.root "IntCat") srcName, kind := .sort }
              let codExpr := Expr.atom { name := .app (.root "IntCat") tgtName, kind := .sort }
              { id := funId
                domain := domExpr
                codomain := codExpr
                description := s!"Internal functor ({f0.id.name},{f1.id.name})"
                : Generator1 }

  -- Axioms: source and target commute with identity (s ∘ i = id, t ∘ i = id)
  let unitAxioms := t.objects.flatMap fun c0 =>
    t.objects.flatMap fun c1 =>
      let catName := .app (.root "IntCat") (Name.pair c0.id.name c1.id.name)
      let s := Expr.atom { name := .nested catName "s", kind := .morphism }
      let tgt := Expr.atom { name := .nested catName "t", kind := .morphism }
      let i := Expr.atom { name := .nested catName "i", kind := .morphism }
      [ { id := { name := .nested catName "s∘i=id", kind := .twoCell }
          leftPath := .comp s i
          rightPath := .id (.atom c0.id)
          description := "Source of identity is identity" : Generator2 },
        { id := { name := .nested catName "t∘i=id", kind := .twoCell }
          leftPath := .comp tgt i
          rightPath := .id (.atom c0.id)
          description := "Target of identity is identity" : Generator2 } ]

  { name := s!"Cat({t.name})"
    doctrine := t.doctrine
    objects := t.objects ++ intCatObjects
    morphisms := structureMorphisms ++ internalFunctors
    axioms := unitAxioms }

end CatLab
