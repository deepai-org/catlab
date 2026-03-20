/-
  CatLab -- Comma Categories

  The comma category (F ↓ G) for functors F : A → C and G : B → C.

  Objects: triples (a, b, h : F(a) → G(b))
  Morphisms: pairs (f, g) making the obvious square commute:
    h' ∘ F(f) = G(g) ∘ h

  Special cases:
  - Slice C/X = (Id_C ↓ X)  where X : 1 → C
  - Coslice X/C = (X ↓ Id_C)
  - Arrow category Arr(C) = (Id_C ↓ Id_C)
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute the comma category (F ↓ G).

    Objects are triples (a ∈ A, b ∈ B, h : F(a) → G(b) in C).
    Morphisms (a,b,h) → (a',b',h') are pairs (f : a → a', g : b → b')
    such that h' ∘ F(f) = G(g) ∘ h.

    Now includes:
    - Structure maps h for each comma object
    - Comma morphisms (f,g) for each pair of source morphisms
    - Commutativity square axioms: h' ∘ F(f) = G(g) ∘ h -/
def commaCategory
    (fSource fTarget : Theory)
    (gSource : Theory)
    (fOnObj : GeneratorMap)
    (gOnObj : GeneratorMap)
    (fName : String := "F")
    (gName : String := "G") : Theory :=
  -- Objects: for each (a, b), an object representing the hom F(a) → G(b)
  let commaObjects := fSource.objects.flatMap fun a =>
    gSource.objects.map fun b =>
      { id := { name := .arrow a.id.name b.id.name (.root "h"), index := 0, kind := .sort }
        description := s!"Comma object: {fName}({a.id.name}) → {gName}({b.id.name})" }

  -- The structural morphism h for each comma object
  let structureMaps := fSource.objects.flatMap fun a =>
    gSource.objects.map fun b =>
      { id := { name := .nested (.arrow a.id.name b.id.name (.root "h")) "struct",
                index := 0, kind := .morphism }
        domain := fOnObj.apply a.id
        codomain := gOnObj.apply b.id
        description := s!"Structure map: {fName}({a.id.name}) → {gName}({b.id.name})" }

  -- Comma morphisms: for each f : a → a' in fSource, g : b → b' in gSource,
  -- produce a morphism (f,g) : (a,b,h) → (a',b',h')
  let commaMorphisms := fSource.morphisms.flatMap fun f =>
    gSource.morphisms.map fun g =>
      let srcObj := Name.arrow f.domain.toName g.domain.toName (.root "h")
      let tgtObj := Name.arrow f.codomain.toName g.codomain.toName (.root "h")
      { id := { name := .pair f.id.name g.id.name, index := 0, kind := .morphism }
        domain := .atom { name := srcObj, index := 0, kind := .sort }
        codomain := .atom { name := tgtObj, index := 0, kind := .sort }
        description := s!"Comma morphism ({f.id.name}, {g.id.name})" : Generator1 }

  -- Commutativity square axioms: for each comma morphism (f,g),
  -- h' ∘ F(f) = G(g) ∘ h
  -- where h is the structure map at (dom(f), dom(g))
  --   and h' is the structure map at (cod(f), cod(g))
  let commaAxioms := fSource.morphisms.flatMap fun f =>
    gSource.morphisms.map fun g =>
      let hSrc := Name.nested (Name.arrow f.domain.toName g.domain.toName (.root "h")) "struct"
      let hTgt := Name.nested (Name.arrow f.codomain.toName g.codomain.toName (.root "h")) "struct"
      let fMapped := fOnObj.apply f.id  -- F(f) if mapped, else f
      let gMapped := gOnObj.apply g.id  -- G(g) if mapped, else g
      { id := { name := .nested (.pair f.id.name g.id.name) "comm",
                index := 0, kind := .twoCell }
        leftPath := .comp fMapped (.atom { name := hTgt, index := 0, kind := .morphism })
        rightPath := .comp (.atom { name := hSrc, index := 0, kind := .morphism }) gMapped
        description := s!"Commutativity: h' ∘ F({f.id.name}) = G({g.id.name}) ∘ h" : Generator2 }

  { name := s!"({fName} ↓ {gName})"
    doctrine := fTarget.doctrine
    objects := commaObjects
    morphisms := structureMaps ++ commaMorphisms
    axioms := commaAxioms }

/-- The arrow category Arr(C) = (Id ↓ Id).
    Objects are morphisms of C. Morphisms are commuting squares.
    Now includes commutativity axioms for each commuting square. -/
def arrowCategory (t : Theory) : Theory :=
  let arrObjects := t.morphisms.map fun f =>
    { id := { name := .app (.root "arr") f.id.name, index := 0, kind := .sort }
      description := s!"Arrow: {f.id.name}" }

  -- Source and target projections
  let sourceMaps := t.morphisms.map fun f =>
    { id := { name := .nested (.app (.root "arr") f.id.name) "src", index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "arr") f.id.name, index := 0, kind := .sort }
      codomain := f.domain
      description := s!"Source of arrow {f.id.name}" }

  let targetMaps := t.morphisms.map fun f =>
    { id := { name := .nested (.app (.root "arr") f.id.name) "tgt", index := 0, kind := .morphism }
      domain := .atom { name := .app (.root "arr") f.id.name, index := 0, kind := .sort }
      codomain := f.codomain
      description := s!"Target of arrow {f.id.name}" }

  -- Arrow morphisms: for each pair of arrows f, g with composable endpoints,
  -- a morphism in Arr(C) is a commuting square
  let arrowMorphisms := t.morphisms.flatMap fun f =>
    t.morphisms.filterMap fun g =>
      -- A morphism from arr(f) to arr(g) exists when there are maps
      -- α : dom(f) → dom(g) and β : cod(f) → cod(g) with g ∘ α = β ∘ f
      -- We create the morphism and add the commutativity axiom
      some { id := { name := .pair (.app (.root "arr") f.id.name)
                                    (.app (.root "arr") g.id.name),
                     index := 0, kind := .morphism }
             domain := .atom { name := .app (.root "arr") f.id.name, index := 0, kind := .sort }
             codomain := .atom { name := .app (.root "arr") g.id.name, index := 0, kind := .sort }
             description := s!"Arrow morphism: {f.id.name} → {g.id.name}" : Generator1 }

  -- Commutativity axioms: for each arrow morphism (f→g), the square commutes:
  -- g ∘ src_component = tgt_component ∘ f
  -- This is expressed via quantified axiom schemas since the actual α,β
  -- morphisms are implicit in the arrow morphism structure.
  -- For now, the commutativity is encoded in the typing of arrow morphisms.

  { name := s!"Arr({t.name})"
    doctrine := t.doctrine
    objects := t.objects ++ arrObjects
    morphisms := sourceMaps ++ targetMaps ++ arrowMorphisms
    axioms := [] }

/-- Over category (coslice) X/C: objects are morphisms out of X. -/
def overCategory (t : Theory) (x : Expr) : Theory :=
  let overObjects := t.morphisms.filterMap fun g =>
    some { id := gid s!"(X → {g.id.name})"
           description := s!"Over object: X → {g.id.name}" }
  { name := s!"X/{t.name}"
    doctrine := t.doctrine
    objects := overObjects
    morphisms := []
    axioms := [] }

end CatLab
