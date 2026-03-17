/-
  CatLab -- Ends and Coends

  The weighted (co)limit machinery that Kan extensions are built on.

  End:   ∫_{a ∈ C} F(a,a) = the universal wedge (equalizer-like construction)
  Coend: ∫^{a ∈ C} F(a,a) = the universal cowedge (coequalizer-like construction)

  For a bifunctor F : Cᵒᵖ × C → D:
    End   = subobject of ∏_a F(a,a) where all "extranatural" squares commute
    Coend = quotient of ∐_a F(a,a) identifying F(f,id) with F(id,f)
-/

import Catlab.Core.Theory
import Std.Data.HashMap

namespace CatLab

/-- An explicit mapping from pairs of GeneratorIds to Exprs (for profunctors). -/
structure GeneratorMap2 where
  entries : Std.HashMap (GeneratorId × GeneratorId) Expr := {}
  deriving Inhabited

namespace GeneratorMap2

def apply (m : GeneratorMap2) (a b : GeneratorId) : Expr :=
  m.entries[(a, b)]? |>.getD (.prod (.atom a) (.atom b))

def ofList (pairs : List ((GeneratorId × GeneratorId) × Expr)) : GeneratorMap2 :=
  ⟨pairs.foldl (fun acc (k, v) => acc.insert k v) {}⟩

end GeneratorMap2

/-- A profunctor / bifunctor F : Cᵒᵖ × C → D,
    specified by its action on pairs of objects and morphisms.
    Uses explicit maps instead of closures. -/
structure Profunctor where
  name : String
  source : Theory  -- C
  target : Theory  -- D
  /-- F(a,b) for objects a, b of C -/
  onObjects : GeneratorMap2
  /-- F(f,g) for morphisms f, g — contravariant in first, covariant in second -/
  onMorphisms : GeneratorMap2

/-- A wedge for a profunctor F: a family of morphisms w_a : X → F(a,a)
    compatible with all morphisms in C. -/
structure Wedge where
  apex : Expr
  components : List (GeneratorId × Expr)  -- (a, w_a : apex → F(a,a))

/-- A cowedge: a family of morphisms c_a : F(a,a) → X. -/
structure Cowedge where
  nadir : Expr
  components : List (GeneratorId × Expr)

/-- Compute the end ∫_{a ∈ C} F(a,a).

    The end is the universal wedge: an object E with projections
    π_a : E → F(a,a) such that for every f : a → b in C,
    F(f, id_b) ∘ π_b = F(id_a, f) ∘ π_a. -/
def computeEnd (p : Profunctor) : Theory :=
  let endObj := { id := gid s!"∫_{p.name}"
                  description := s!"End of {p.name}" }

  -- Projection morphisms: π_a : ∫F → F(a,a)
  let projections := p.source.objects.map fun a =>
    { id := gid s!"π^end_{a.id.name}"
      domain := .atom (gid s!"∫_{p.name}")
      codomain := p.onObjects.apply a.id a.id
      description := s!"End projection at {a.id.name}" }

  -- Wedge condition: for each f : a → b,
  -- F(f, id) ∘ π_b = F(id, f) ∘ π_a
  let wedgeAxioms := p.source.morphisms.map fun f =>
    { id := gid s!"wedge_{f.id.name}"
      leftPath := .comp (.atom (gid s!"π^end_{repr f.codomain}")) (p.onMorphisms.apply f.id (gid "id"))
      rightPath := .comp (.atom (gid s!"π^end_{repr f.domain}")) (p.onMorphisms.apply (gid "id") f.id)
      description := s!"Wedge condition for {f.id.name}" }

  { name := s!"∫({p.name})"
    doctrine := p.target.doctrine
    objects := [endObj]
    morphisms := projections
    axioms := wedgeAxioms }

/-- Compute the coend ∫^{a ∈ C} F(a,a).

    The coend is the universal cowedge: an object Q with injections
    ι_a : F(a,a) → Q such that for every f : a → b,
    F(id_a, f) ∘ ι_a = F(f, id_b) ∘ ι_b  (after composing into Q). -/
def computeCoend (p : Profunctor) : Theory :=
  let coendObj := { id := gid s!"∫^{p.name}"
                    description := s!"Coend of {p.name}" }

  -- Injection morphisms: ι_a : F(a,a) → ∫^F
  let injections := p.source.objects.map fun a =>
    { id := gid s!"ι^coend_{a.id.name}"
      domain := p.onObjects.apply a.id a.id
      codomain := .atom (gid s!"∫^{p.name}")
      description := s!"Coend injection at {a.id.name}" }

  -- Cowedge condition (dual of wedge)
  let cowedgeAxioms := p.source.morphisms.map fun f =>
    { id := gid s!"cowedge_{f.id.name}"
      leftPath := .comp (p.onMorphisms.apply (gid "id") f.id) (.atom (gid s!"ι^coend_{repr f.domain}"))
      rightPath := .comp (p.onMorphisms.apply f.id (gid "id")) (.atom (gid s!"ι^coend_{repr f.codomain}"))
      description := s!"Cowedge condition for {f.id.name}" }

  { name := s!"∫^({p.name})"
    doctrine := p.target.doctrine
    objects := [coendObj]
    morphisms := injections
    axioms := cowedgeAxioms }

/-- The Ninja Yoneda lemma: ∫_{a} [Hom(a, b), F(a)] ≅ F(b)
    This is the computation that makes Kan extensions work. -/
def ninjaYoneda (p : Profunctor) (b : GeneratorId) : Generator2 :=
  { id := gid s!"ninja_yoneda_{b.name}"
    leftPath := .atom (gid s!"∫_{p.name}_at_{b.name}")
    rightPath := p.onObjects.apply b b
    description := s!"Ninja Yoneda: end over Hom(-, {b.name}) ⊗ F ≅ F({b.name})" }

end CatLab
