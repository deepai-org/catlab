/-
  CatLab -- Span and Cospan Categories

  A span from A to B in C is a triple (A ← S → B), i.e., an object S
  with morphisms l : S → A and r : S → B. Composition is by pullback.

  Dually, a cospan from A to B is a triple (A → S ← B).
  Composition of cospans is by pushout.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Batteries.Data.HashMap

namespace CatLab

/-- A span between two objects: a roof A ← S → B -/
structure Span where
  /-- The apex of the span -/
  apex : GeneratorId
  /-- The left leg: S → A -/
  leftLeg : GeneratorId
  /-- The right leg: S → B -/
  rightLeg : GeneratorId
  /-- Source object A -/
  source : GeneratorId
  /-- Target object B -/
  target : GeneratorId
  deriving Repr, Inhabited

/-- Compute the category of spans in C.

    Objects: same as objects of C.
    Morphisms: for each pair (A, B) and each object S with morphisms
      l : S → A and r : S → B, a span morphism from A to B.
    This builds the span category from the generators of C. -/
def spanCategory (t : Theory) : Theory :=
  -- Objects: same as C
  let spanObjects := t.objects

  -- Morphisms: for each triple (A, S, B) with l : S → A and r : S → B,
  -- generate a span morphism A → B
  -- Group morphisms by domain using an index for O(N) instead of O(N²)
  let domIndex := t.outEdgeIndex
  let spanMorphisms := t.objects.flatMap fun s =>
    let outgoing := domIndex[s.id.name]? |>.getD []
    outgoing.flatMap fun l =>
      outgoing.filterMap fun r =>
        if l.id == r.id then none
        else
          let spanName : Name := .pair l.id.name r.id.name
          some { id := { name := spanName, index := 0, kind := .morphism }
                 domain := l.codomain
                 codomain := r.codomain
                 description := s!"Span via {l.id.name}, {r.id.name}" : Generator1 }

  -- Axioms: identity spans (when l = r = id) and associativity would require
  -- pullback structure; we record the generators here.
  { name := s!"Span({t.name})"
    doctrine := t.doctrine
    objects := spanObjects
    morphisms := spanMorphisms
    axioms := [] }

/-- Compute the category of cospans in C (dual of spans).

    Objects: same as objects of C.
    Morphisms: for each pair (A, B) and object S with morphisms
      l : A → S and r : B → S, a cospan morphism from A to B.
    Composition is by pushout. -/
def cospanCategory (t : Theory) : Theory :=
  let cospanObjects := t.objects

  -- Group morphisms by codomain using an index for O(N) instead of O(N²)
  let codIndex := t.inEdgeIndex
  let cospanMorphisms := t.objects.flatMap fun s =>
    let incoming := codIndex[s.id.name]? |>.getD []
    incoming.flatMap fun l =>
      incoming.filterMap fun r =>
        if l.id == r.id then none
        else
          let cospanName : Name := .pair l.id.name r.id.name
          some { id := { name := cospanName, index := 0, kind := .morphism }
                 domain := l.domain
                 codomain := r.domain
                 description := s!"Cospan via {l.id.name}, {r.id.name}" : Generator1 }

  { name := s!"Cospan({t.name})"
    doctrine := t.doctrine
    objects := cospanObjects
    morphisms := cospanMorphisms
    axioms := [] }

end CatLab
