/-
  CatLab — Collage (Cograph) of a Profunctor

  Given two theories C and D and profunctor data (a list of heteromorphisms
  from C-objects to D-objects), construct the collage category.

  The collage contains:
  - All objects of C and D
  - All morphisms of C and D
  - Heteromorphisms from C-objects to D-objects
  - No morphisms from D-objects to C-objects

  This is the categorical analogue of a bipartite graph.
-/

import Catlab.Core.Theory

namespace CatLab

/-- A heteromorphism specification for profunctor data: a morphism from
    an object of C to an object of D. -/
structure HeteroMorphism where
  id : GeneratorId
  source : Expr       -- an object expression in C
  target : Expr       -- an object expression in D
  description : String := ""
  deriving Repr, Inhabited

/-- Compute the collage category of a profunctor.

    Given theories C and D, and heteromorphism data H : C^op × D → Set,
    the collage is the category with:
    - Objects: Ob(C) ⊔ Ob(D)
    - Hom(c, c') = C(c, c')         for c, c' in C
    - Hom(d, d') = D(d, d')         for d, d' in D
    - Hom(c, d) = H(c, d)           for c in C, d in D
    - Hom(d, c) = ∅                  for d in D, c in C

    Composition of heteromorphisms with C/D morphisms is given by the
    profunctor action. -/
def collage
    (c d : Theory)
    (hetero : List HeteroMorphism)
    (name : String := "Collage") : Theory :=
  -- Prefix C and D objects/morphisms to avoid name clashes
  let cObjects : List Generator0 := c.objects.map fun obj =>
    { obj with id := gid s!"C.{obj.id.name}" }

  let dObjects : List Generator0 := d.objects.map fun obj =>
    { obj with id := gid s!"D.{obj.id.name}" }

  let cMorphisms : List Generator1 := c.morphisms.map fun m =>
    { m with
      id := gid s!"C.{m.id.name}"
      domain := m.domain.mapNames (fun n => .root s!"C.{n}")
      codomain := m.codomain.mapNames (fun n => .root s!"C.{n}") }

  let dMorphisms : List Generator1 := d.morphisms.map fun m =>
    { m with
      id := gid s!"D.{m.id.name}"
      domain := m.domain.mapNames (fun n => .root s!"D.{n}")
      codomain := m.codomain.mapNames (fun n => .root s!"D.{n}") }

  -- Heteromorphisms go from C-objects to D-objects
  let heteroMorphisms : List Generator1 := hetero.map fun h =>
    { id := h.id
      domain := h.source.mapNames (fun n => .root s!"C.{n}")
      codomain := h.target.mapNames (fun n => .root s!"D.{n}")
      description := h.description }

  -- Axioms from C and D, with prefixed names
  let cAxioms : List Generator2 := c.axioms.map fun ax =>
    { ax with
      id := gid s!"C.{ax.id.name}"
      leftPath := ax.leftPath.mapNames (fun n => .root s!"C.{n}")
      rightPath := ax.rightPath.mapNames (fun n => .root s!"C.{n}") }

  let dAxioms : List Generator2 := d.axioms.map fun ax =>
    { ax with
      id := gid s!"D.{ax.id.name}"
      leftPath := ax.leftPath.mapNames (fun n => .root s!"D.{n}")
      rightPath := ax.rightPath.mapNames (fun n => .root s!"D.{n}") }

  -- Composition axioms: for f : c → c' in C and h : c' → d in hetero,
  -- h ∘ f should be a heteromorphism (profunctor left action).
  -- We represent this structurally — the composition is well-typed by construction.

  { name := name
    doctrine := c.doctrine
    objects := cObjects ++ dObjects
    morphisms := cMorphisms ++ dMorphisms ++ heteroMorphisms
    axioms := cAxioms ++ dAxioms }

end CatLab
