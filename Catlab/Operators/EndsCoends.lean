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

namespace CatLab

/-- A profunctor / bifunctor F : Cᵒᵖ × C → D,
    specified by its action on pairs of objects and morphisms. -/
structure Profunctor where
  name : String
  source : Theory  -- C
  target : Theory  -- D
  /-- F(a,b) for objects a, b of C -/
  onObjects : GeneratorId → GeneratorId → Expr
  /-- F(f,g) for morphisms f, g — contravariant in first, covariant in second -/
  onMorphisms : GeneratorId → GeneratorId → Expr

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
  let endObj := { id := ⟨s!"∫_{p.name}", 0⟩
                  description := s!"End of {p.name}" }

  -- Projection morphisms: π_a : ∫F → F(a,a)
  let projections := p.source.objects.map fun a =>
    { id := ⟨s!"π^end_{a.id.name}", 0⟩
      domain := .atom ⟨s!"∫_{p.name}", 0⟩
      codomain := p.onObjects a.id a.id
      description := s!"End projection at {a.id.name}" }

  -- Wedge condition: for each f : a → b,
  -- F(f, id) ∘ π_b = F(id, f) ∘ π_a
  let wedgeAxioms := p.source.morphisms.map fun f =>
    { id := ⟨s!"wedge_{f.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"π^end_{repr f.codomain}", 0⟩) (p.onMorphisms f.id ⟨"id", 0⟩)
      rightPath := .comp (.atom ⟨s!"π^end_{repr f.domain}", 0⟩) (p.onMorphisms ⟨"id", 0⟩ f.id)
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
  let coendObj := { id := ⟨s!"∫^{p.name}", 0⟩
                    description := s!"Coend of {p.name}" }

  -- Injection morphisms: ι_a : F(a,a) → ∫^F
  let injections := p.source.objects.map fun a =>
    { id := ⟨s!"ι^coend_{a.id.name}", 0⟩
      domain := p.onObjects a.id a.id
      codomain := .atom ⟨s!"∫^{p.name}", 0⟩
      description := s!"Coend injection at {a.id.name}" }

  -- Cowedge condition (dual of wedge)
  let cowedgeAxioms := p.source.morphisms.map fun f =>
    { id := ⟨s!"cowedge_{f.id.name}", 0⟩
      leftPath := .comp (p.onMorphisms ⟨"id", 0⟩ f.id) (.atom ⟨s!"ι^coend_{repr f.domain}", 0⟩)
      rightPath := .comp (p.onMorphisms f.id ⟨"id", 0⟩) (.atom ⟨s!"ι^coend_{repr f.codomain}", 0⟩)
      description := s!"Cowedge condition for {f.id.name}" }

  { name := s!"∫^({p.name})"
    doctrine := p.target.doctrine
    objects := [coendObj]
    morphisms := injections
    axioms := cowedgeAxioms }

/-- The Ninja Yoneda lemma: ∫_{a} [Hom(a, b), F(a)] ≅ F(b)
    This is the computation that makes Kan extensions work. -/
def ninjaYoneda (p : Profunctor) (b : GeneratorId) : Generator2 :=
  { id := ⟨s!"ninja_yoneda_{b.name}", 0⟩
    leftPath := .atom ⟨s!"∫_{p.name}_at_{b.name}", 0⟩
    rightPath := p.onObjects b b
    description := s!"Ninja Yoneda: end over Hom(-, {b.name}) ⊗ F ≅ F({b.name})" }

end CatLab
