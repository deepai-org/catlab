/-
  CatLab — Limits & Colimits Engine

  The universal construction engine. Products, coproducts, pullbacks, pushouts,
  equalizers, coequalizers, terminal/initial objects — all computed here.

  Every other operator eventually delegates to this module.
-/

import Catlab.Core.Theory

namespace CatLab

/-- A diagram is a small category mapped into a target theory:
    a collection of objects and morphisms between them. -/
structure Diagram where
  /-- The nodes of the diagram, each referencing an Expr in the theory -/
  nodes : List (String × Expr)
  /-- The edges: (source_name, target_name, morphism_expr) -/
  edges : List (String × String × Expr)
  deriving Repr, Inhabited

/-- A cone over a diagram: an apex object with projection morphisms -/
structure Cone where
  apex : Expr
  projections : List (String × Expr)  -- node_name → projection morphism
  deriving Repr, Inhabited

/-- A cocone over a diagram: a nadir object with injection morphisms -/
structure Cocone where
  nadir : Expr
  injections : List (String × Expr)  -- node_name → injection morphism
  deriving Repr, Inhabited

/-- Result of a limit computation: the new generators added to a theory -/
structure LimitResult where
  /-- The universal object -/
  object : Generator0
  /-- The projection/injection morphisms -/
  morphisms : List Generator1
  /-- The universal property axioms -/
  axioms : List Generator2
  deriving Repr, Inhabited

/-- Compute the binary product of two expressions.
    Returns generators for A × B, π₁, π₂, and the universal property. -/
def computeProduct (a b : Expr) (namePrefix : String := "prod") : LimitResult :=
  let prodObj := Expr.prod a b
  { object := { id := ⟨namePrefix, 0⟩, description := s!"Product of {repr a} and {repr b}" }
    morphisms := [
      { id := ⟨s!"{namePrefix}_π₁", 0⟩, domain := prodObj, codomain := a,
        description := "First projection" },
      { id := ⟨s!"{namePrefix}_π₂", 0⟩, domain := prodObj, codomain := b,
        description := "Second projection" }
    ]
    axioms := [
      { id := ⟨s!"{namePrefix}_univ", 0⟩,
        leftPath := .comp (.atom ⟨"⟨f,g⟩", 0⟩) (.atom ⟨s!"{namePrefix}_π₁", 0⟩),
        rightPath := .atom ⟨"f", 0⟩,
        description := "Universal property of product" }
    ] }

/-- Compute the binary coproduct (disjoint union) of two expressions. -/
def computeCoproduct (a b : Expr) (namePrefix : String := "coprod") : LimitResult :=
  let coprodObj := Expr.coprod a b
  { object := { id := ⟨namePrefix, 0⟩, description := s!"Coproduct of {repr a} and {repr b}" }
    morphisms := [
      { id := ⟨s!"{namePrefix}_ι₁", 0⟩, domain := a, codomain := coprodObj,
        description := "First injection" },
      { id := ⟨s!"{namePrefix}_ι₂", 0⟩, domain := b, codomain := coprodObj,
        description := "Second injection" }
    ]
    axioms := [
      { id := ⟨s!"{namePrefix}_univ", 0⟩,
        leftPath := .comp (.atom ⟨s!"{namePrefix}_ι₁", 0⟩) (.atom ⟨"[f,g]", 0⟩),
        rightPath := .atom ⟨"f", 0⟩,
        description := "Universal property of coproduct" }
    ] }

/-- Compute the pullback of f : A → C and g : B → C.
    Returns the pullback object P with projections p₁ : P → A, p₂ : P → B
    satisfying f ∘ p₁ = g ∘ p₂. -/
def computePullback (f g : Generator1) (namePrefix : String := "pb") : LimitResult :=
  let pbObj := Expr.atom ⟨namePrefix, 0⟩
  let pbId : GeneratorId := ⟨namePrefix, 0⟩
  { object := { id := pbId, description := s!"Pullback of {f.id.name} and {g.id.name}" }
    morphisms := [
      { id := ⟨s!"{namePrefix}_p₁", 0⟩, domain := pbObj, codomain := f.domain,
        description := "Pullback projection to first factor" },
      { id := ⟨s!"{namePrefix}_p₂", 0⟩, domain := pbObj, codomain := g.domain,
        description := "Pullback projection to second factor" }
    ]
    axioms := [
      { id := ⟨s!"{namePrefix}_comm", 0⟩,
        leftPath := .comp (.atom ⟨s!"{namePrefix}_p₁", 0⟩) (.atom f.id),
        rightPath := .comp (.atom ⟨s!"{namePrefix}_p₂", 0⟩) (.atom g.id),
        description := "Pullback square commutes: f ∘ p₁ = g ∘ p₂" }
    ] }

/-- Compute the pushout of f : C → A and g : C → B.
    Dual to pullback. -/
def computePushout (f g : Generator1) (namePrefix : String := "po") : LimitResult :=
  let poObj := Expr.atom ⟨namePrefix, 0⟩
  let poId : GeneratorId := ⟨namePrefix, 0⟩
  { object := { id := poId, description := s!"Pushout of {f.id.name} and {g.id.name}" }
    morphisms := [
      { id := ⟨s!"{namePrefix}_ι₁", 0⟩, domain := f.codomain, codomain := poObj,
        description := "Pushout injection from first factor" },
      { id := ⟨s!"{namePrefix}_ι₂", 0⟩, domain := g.codomain, codomain := poObj,
        description := "Pushout injection from second factor" }
    ]
    axioms := [
      { id := ⟨s!"{namePrefix}_comm", 0⟩,
        leftPath := .comp (.atom f.id) (.atom ⟨s!"{namePrefix}_ι₁", 0⟩),
        rightPath := .comp (.atom g.id) (.atom ⟨s!"{namePrefix}_ι₂", 0⟩),
        description := "Pushout square commutes: ι₁ ∘ f = ι₂ ∘ g" }
    ] }

/-- Compute the equalizer of f, g : A → B.
    The subobject E → A where f and g agree. -/
def computeEqualizer (f g : Generator1) (namePrefix : String := "eq") : LimitResult :=
  let eqObj := Expr.atom ⟨namePrefix, 0⟩
  let eqId : GeneratorId := ⟨namePrefix, 0⟩
  { object := { id := eqId, description := s!"Equalizer of {f.id.name} and {g.id.name}" }
    morphisms := [
      { id := ⟨s!"{namePrefix}_ι", 0⟩, domain := eqObj, codomain := f.domain,
        description := "Equalizer inclusion" }
    ]
    axioms := [
      { id := ⟨s!"{namePrefix}_eq", 0⟩,
        leftPath := .comp (.atom ⟨s!"{namePrefix}_ι", 0⟩) (.atom f.id),
        rightPath := .comp (.atom ⟨s!"{namePrefix}_ι", 0⟩) (.atom g.id),
        description := "Equalizer condition: f ∘ ι = g ∘ ι" }
    ] }

/-- Compute the coequalizer of f, g : A → B.
    The quotient B → Q where f and g are identified. -/
def computeCoequalizer (f g : Generator1) (namePrefix : String := "coeq") : LimitResult :=
  let coeqObj := Expr.atom ⟨namePrefix, 0⟩
  let coeqId : GeneratorId := ⟨namePrefix, 0⟩
  { object := { id := coeqId, description := s!"Coequalizer of {f.id.name} and {g.id.name}" }
    morphisms := [
      { id := ⟨s!"{namePrefix}_π", 0⟩, domain := f.codomain, codomain := coeqObj,
        description := "Coequalizer quotient map" }
    ]
    axioms := [
      { id := ⟨s!"{namePrefix}_eq", 0⟩,
        leftPath := .comp (.atom f.id) (.atom ⟨s!"{namePrefix}_π", 0⟩),
        rightPath := .comp (.atom g.id) (.atom ⟨s!"{namePrefix}_π", 0⟩),
        description := "Coequalizer condition: π ∘ f = π ∘ g" }
    ] }

/-- Adjoin a limit result into a theory, extending it with new generators -/
def Theory.adjoinLimit (t : Theory) (lr : LimitResult) : Theory :=
  { t with
    objects := t.objects ++ [lr.object]
    morphisms := t.morphisms ++ lr.morphisms
    axioms := t.axioms ++ lr.axioms }

end CatLab
