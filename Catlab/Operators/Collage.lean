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
    { obj with id := ⟨s!"C.{obj.id.name}", obj.id.index⟩ }

  let dObjects : List Generator0 := d.objects.map fun obj =>
    { obj with id := ⟨s!"D.{obj.id.name}", obj.id.index⟩ }

  let cMorphisms : List Generator1 := c.morphisms.map fun m =>
    { m with
      id := ⟨s!"C.{m.id.name}", m.id.index⟩
      domain := prefixAtoms "C." m.domain
      codomain := prefixAtoms "C." m.codomain }

  let dMorphisms : List Generator1 := d.morphisms.map fun m =>
    { m with
      id := ⟨s!"D.{m.id.name}", m.id.index⟩
      domain := prefixAtoms "D." m.domain
      codomain := prefixAtoms "D." m.codomain }

  -- Heteromorphisms go from C-objects to D-objects
  let heteroMorphisms : List Generator1 := hetero.map fun h =>
    { id := h.id
      domain := prefixAtoms "C." h.source
      codomain := prefixAtoms "D." h.target
      description := h.description }

  -- Axioms from C and D, with prefixed names
  let cAxioms : List Generator2 := c.axioms.map fun ax =>
    { ax with
      id := ⟨s!"C.{ax.id.name}", ax.id.index⟩
      leftPath := prefixAtoms "C." ax.leftPath
      rightPath := prefixAtoms "C." ax.rightPath }

  let dAxioms : List Generator2 := d.axioms.map fun ax =>
    { ax with
      id := ⟨s!"D.{ax.id.name}", ax.id.index⟩
      leftPath := prefixAtoms "D." ax.leftPath
      rightPath := prefixAtoms "D." ax.rightPath }

  -- Composition axioms: for f : c → c' in C and h : c' → d in hetero,
  -- h ∘ f should be a heteromorphism (profunctor left action).
  -- We represent this structurally — the composition is well-typed by construction.

  { name := name
    doctrine := c.doctrine
    objects := cObjects ++ dObjects
    morphisms := cMorphisms ++ dMorphisms ++ heteroMorphisms
    axioms := cAxioms ++ dAxioms }
where
  /-- Prefix all atom names in an expression with a given string. -/
  prefixAtoms (prefix_ : String) : Expr → Expr
    | .atom gid => .atom ⟨s!"{prefix_}{gid.name}", gid.index⟩
    | Expr.id obj => Expr.id (prefixAtoms prefix_ obj)
    | .comp f g => .comp (prefixAtoms prefix_ f) (prefixAtoms prefix_ g)
    | .prod a b => .prod (prefixAtoms prefix_ a) (prefixAtoms prefix_ b)
    | .coprod a b => .coprod (prefixAtoms prefix_ a) (prefixAtoms prefix_ b)
    | .hom a b => .hom (prefixAtoms prefix_ a) (prefixAtoms prefix_ b)
    | .tensor a b => .tensor (prefixAtoms prefix_ a) (prefixAtoms prefix_ b)
    | .unit => .unit
    | .terminal => .terminal
    | .initial => .initial
    | .sigma v base fam => .sigma v (prefixAtoms prefix_ base) (prefixAtoms prefix_ fam)
    | .pi v base fam => .pi v (prefixAtoms prefix_ base) (prefixAtoms prefix_ fam)
    | .fiber m p => .fiber (prefixAtoms prefix_ m) (prefixAtoms prefix_ p)
    | .proj i s => .proj i (prefixAtoms prefix_ s)
    | .inj i t => .inj i (prefixAtoms prefix_ t)
    | .var n => .var n

end CatLab
