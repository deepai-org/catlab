/-
  CatLab — Grothendieck Construction (∫F)

  Takes an indexed category (a functor F : Cᵒᵖ → Cat) and "flattens" it
  into a single fibered category ∫F over C.

  Objects of ∫F: pairs (c, x) where c ∈ C and x ∈ F(c)
  Morphisms (c,x) → (d,y): pairs (f : c → d, g : F(f)(x) → y)
-/

import Catlab.Core.Theory

namespace CatLab

/-- An indexed category: for each object of the base, a fiber theory,
    and for each morphism, a "reindexing" functor between fibers. -/
structure IndexedCategory where
  /-- The base theory -/
  base : Theory
  /-- For each base object, the fiber theory -/
  fiber : GeneratorId → Theory
  /-- For each base morphism, the reindexing map (as morphism generators) -/
  reindex : GeneratorId → List Generator1

/-- The Grothendieck construction: flatten an indexed category into
    a single fibered theory.

    ∫F has:
    - Objects: (c, x) for c in base, x in fiber(c)
    - Morphisms: (f, g) where f : c → d in base, g : reindex(f)(x) → y in fiber(d) -/
def grothendieck (ic : IndexedCategory) : Theory :=
  -- Objects: pairs of (base object, fiber object)
  let totalObjects := ic.base.objects.flatMap fun c =>
    let fib := ic.fiber c.id
    fib.objects.map fun x =>
      { id := { name := .root s!"({c.id.name},{x.id.name})", index := 0 }
        description := s!"Total object: {x.id.name} over {c.id.name}" }

  -- Morphisms: pairs of (base morphism, fiber morphism)
  let totalMorphisms := ic.base.morphisms.flatMap fun f =>
    let reindexMaps := ic.reindex f.id
    reindexMaps.map fun g =>
      { id := { name := .root s!"({f.id.name},{g.id.name})", index := 0 }
        domain := .atom { name := .root s!"({repr f.domain},{repr g.domain})", index := 0 }
        codomain := .atom { name := .root s!"({repr f.codomain},{repr g.codomain})", index := 0 }
        description := s!"Total morphism: ({f.id.name},{g.id.name})" }

  -- The projection functor ∫F → C is implicit in the naming
  { name := s!"∫({ic.base.name})"
    doctrine := ic.base.doctrine
    objects := totalObjects
    morphisms := totalMorphisms
    axioms := [] }

/-- The projection functor π : ∫F → C, sending (c,x) ↦ c -/
def grothendieckProjection (ic : IndexedCategory) (total : Theory) : List Generator1 :=
  total.objects.map fun obj =>
    -- Extract base component from the pair name (simplified)
    { id := { name := .root s!"π_{obj.id.name}", index := 0 }
      domain := .atom obj.id
      codomain := .atom (gid "base")
      description := s!"Projection of {obj.id.name} to base" }

end CatLab
