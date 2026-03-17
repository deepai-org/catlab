/-
  CatLab -- Comma Categories

  The comma category (F ↓ G) for functors F : A → C and G : B → C.

  Objects: triples (a, b, h : F(a) → G(b))
  Morphisms: pairs (f, g) making the obvious square commute

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
    such that h' ∘ F(f) = G(g) ∘ h. -/
def commaCategory
    (fSource fTarget : Theory)
    (gSource : Theory)
    (fOnObj : GeneratorId → Expr)
    (gOnObj : GeneratorId → Expr)
    (fName : String := "F")
    (gName : String := "G") : Theory :=
  -- Objects: for each (a, b), an object representing the hom F(a) → G(b)
  let commaObjects := fSource.objects.flatMap fun a =>
    gSource.objects.map fun b =>
      { id := gid s!"({a.id.name},{b.id.name},h)"
        description := s!"Comma object: {fName}({a.id.name}) → {gName}({b.id.name})" }

  -- The structural morphism h for each comma object
  let structureMaps := fSource.objects.flatMap fun a =>
    gSource.objects.map fun b =>
      { id := gid s!"h_{a.id.name}_{b.id.name}"
        domain := fOnObj a.id
        codomain := gOnObj b.id
        description := s!"Structure map: {fName}({a.id.name}) → {gName}({b.id.name})" }

  { name := s!"({fName} ↓ {gName})"
    doctrine := fTarget.doctrine
    objects := commaObjects
    morphisms := structureMaps
    axioms := [] }

/-- The arrow category Arr(C) = (Id ↓ Id).
    Objects are morphisms of C. Morphisms are commuting squares. -/
def arrowCategory (t : Theory) : Theory :=
  let arrObjects := t.morphisms.map fun f =>
    { id := gid s!"arr({f.id.name})"
      description := s!"Arrow: {f.id.name}" }

  -- Source and target projections
  let sourceMaps := t.morphisms.map fun f =>
    { id := gid s!"src_{f.id.name}"
      domain := .atom (gid s!"arr({f.id.name})")
      codomain := f.domain
      description := s!"Source of arrow {f.id.name}" }

  let targetMaps := t.morphisms.map fun f =>
    { id := gid s!"tgt_{f.id.name}"
      domain := .atom (gid s!"arr({f.id.name})")
      codomain := f.codomain
      description := s!"Target of arrow {f.id.name}" }

  { name := s!"Arr({t.name})"
    doctrine := t.doctrine
    objects := arrObjects
    morphisms := sourceMaps ++ targetMaps
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
