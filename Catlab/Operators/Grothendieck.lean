/-
  CatLab — Grothendieck Construction (∫F)

  Takes an indexed category (a functor F : Cᵒᵖ → Cat) and "flattens" it
  into a single fibered category ∫F over C.

  Objects of ∫F: pairs (c, x) where c ∈ C and x ∈ F(c)
  Morphisms (c,x) → (d,y): pairs (f : c → d, g : F(f)(x) → y)

  Now includes:
  - Projection functor axioms (π preserves composition and identity)
  - Functoriality axioms (composition in total category respects base + fiber)
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
    - Morphisms: (f, g) where f : c → d in base, g : reindex(f)(x) → y in fiber(d)
    - Projection morphisms π : (c,x) → c for each total object
    - Projection functor axioms: π preserves the base component
    - Functoriality: composition in ∫F projects to composition in base -/
def grothendieck (ic : IndexedCategory) : Theory :=
  -- Objects: pairs of (base object, fiber object)
  let totalObjects := ic.base.objects.flatMap fun c =>
    let fib := ic.fiber c.id
    fib.objects.map fun x =>
      { id := { name := .pair c.id.name x.id.name, index := 0, kind := .sort }
        description := s!"Total object: {x.id.name} over {c.id.name}" : Generator0 }

  -- Morphisms: pairs of (base morphism, fiber morphism)
  let totalMorphisms := ic.base.morphisms.flatMap fun f =>
    let reindexMaps := ic.reindex f.id
    reindexMaps.map fun g =>
      { id := { name := .pair f.id.name g.id.name, index := 0, kind := .morphism }
        domain := .atom { name := .pair f.domain.toName g.domain.toName, index := 0, kind := .sort }
        codomain := .atom { name := .pair f.codomain.toName g.codomain.toName, index := 0, kind := .sort }
        description := s!"Total morphism: ({f.id.name},{g.id.name})" : Generator1 }

  -- Projection morphisms: π sends (c,x) to the base object c
  let projections := totalObjects.map fun obj =>
    let baseName := match obj.id.name with
      | .pair l _ => l
      | other => other
    { id := { name := .app (.root "π") obj.id.name, index := 0, kind := .morphism }
      domain := .atom obj.id
      codomain := .atom { name := baseName, index := 0, kind := .sort }
      description := s!"Projection: π({obj.id.name})" : Generator1 }

  -- Projection functor axioms: for each total morphism (f,g),
  -- π ∘ (f,g) = f ∘ π  (projection commutes with total morphisms)
  let projAxioms := totalMorphisms.map fun m =>
    let baseMorName := match m.id.name with
      | .pair l _ => l
      | other => other
    let srcProjName := .app (.root "π") m.domain.toName
    let tgtProjName := .app (.root "π") m.codomain.toName
    { id := { name := .nested (.app (.root "π") m.id.name) "nat",
              index := 0, kind := .twoCell }
      leftPath := .comp (.atom m.id)
                        (.atom { name := tgtProjName, index := 0, kind := .morphism })
      rightPath := .comp (.atom { name := srcProjName, index := 0, kind := .morphism })
                         (.atom { name := baseMorName, index := 0, kind := .morphism })
      description := s!"Projection naturality: π ∘ ({m.id.name}) = base_mor ∘ π" : Generator2 }

  -- Identity morphisms: id_(c,x) for each total object
  let identities := totalObjects.map fun obj =>
    { id := { name := .app (.root "id") obj.id.name, index := 0, kind := .morphism }
      domain := .atom obj.id
      codomain := .atom obj.id
      description := s!"Identity: id_{obj.id.name}" : Generator1 }

  -- Identity law: π ∘ id_(c,x) = id_c ∘ π
  let idAxioms := totalObjects.map fun obj =>
    let baseName := match obj.id.name with
      | .pair l _ => l
      | other => other
    { id := { name := .nested (.app (.root "id") obj.id.name) "law",
              index := 0, kind := .twoCell }
      leftPath := .comp (.atom { name := .app (.root "id") obj.id.name, index := 0, kind := .morphism })
                        (.atom { name := .app (.root "π") obj.id.name, index := 0, kind := .morphism })
      rightPath := .comp (.atom { name := .app (.root "π") obj.id.name, index := 0, kind := .morphism })
                         (.id (.atom { name := baseName, index := 0, kind := .sort }))
      description := s!"Identity law: π ∘ id = id ∘ π at {obj.id.name}" : Generator2 }

  { name := s!"∫({ic.base.name})"
    doctrine := ic.base.doctrine
    objects := totalObjects
    morphisms := totalMorphisms ++ projections ++ identities
    axioms := projAxioms ++ idAxioms }

/-- The projection functor π : ∫F → C, sending (c,x) ↦ c -/
def grothendieckProjection (ic : IndexedCategory) (total : Theory) : List Generator1 :=
  total.objects.map fun obj =>
    let baseName := match obj.id.name with
      | .pair l _ => l
      | other => other
    { id := { name := .app (.root "π") obj.id.name, index := 0, kind := .morphism }
      domain := .atom obj.id
      codomain := .atom { name := baseName, index := 0, kind := .sort }
      description := s!"Projection of {obj.id.name} to base" }

end CatLab
