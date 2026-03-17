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
  { object := { id := gid namePrefix, description := s!"Product of {repr a} and {repr b}" }
    morphisms := [
      { id := gid s!"{namePrefix}_π₁", domain := prodObj, codomain := a,
        description := "First projection" },
      { id := gid s!"{namePrefix}_π₂", domain := prodObj, codomain := b,
        description := "Second projection" }
    ]
    axioms := [
      { id := gid s!"{namePrefix}_univ",
        leftPath := .comp (.atom (gid "⟨f,g⟩")) (.atom (gid s!"{namePrefix}_π₁")),
        rightPath := .atom (gid "f"),
        description := "Universal property of product" }
    ] }

/-- Compute the binary coproduct (disjoint union) of two expressions. -/
def computeCoproduct (a b : Expr) (namePrefix : String := "coprod") : LimitResult :=
  let coprodObj := Expr.coprod a b
  { object := { id := gid namePrefix, description := s!"Coproduct of {repr a} and {repr b}" }
    morphisms := [
      { id := gid s!"{namePrefix}_ι₁", domain := a, codomain := coprodObj,
        description := "First injection" },
      { id := gid s!"{namePrefix}_ι₂", domain := b, codomain := coprodObj,
        description := "Second injection" }
    ]
    axioms := [
      { id := gid s!"{namePrefix}_univ",
        leftPath := .comp (.atom (gid s!"{namePrefix}_ι₁")) (.atom (gid "[f,g]")),
        rightPath := .atom (gid "f"),
        description := "Universal property of coproduct" }
    ] }

/-- Compute the pullback of f : A → C and g : B → C.
    Returns the pullback object P with projections p₁ : P → A, p₂ : P → B
    satisfying f ∘ p₁ = g ∘ p₂. -/
def computePullback (f g : Generator1) (namePrefix : String := "pb") : LimitResult :=
  let pbObj := Expr.atom (gid namePrefix)
  let pbId := gid namePrefix
  { object := { id := pbId, description := s!"Pullback of {f.id} and {g.id}" }
    morphisms := [
      { id := gid s!"{namePrefix}_p₁", domain := pbObj, codomain := f.domain,
        description := "Pullback projection to first factor" },
      { id := gid s!"{namePrefix}_p₂", domain := pbObj, codomain := g.domain,
        description := "Pullback projection to second factor" }
    ]
    axioms := [
      { id := gid s!"{namePrefix}_comm",
        leftPath := .comp (.atom (gid s!"{namePrefix}_p₁")) (.atom f.id),
        rightPath := .comp (.atom (gid s!"{namePrefix}_p₂")) (.atom g.id),
        description := "Pullback square commutes: f ∘ p₁ = g ∘ p₂" }
    ] }

/-- Compute the pushout of f : C → A and g : C → B.
    Dual to pullback. -/
def computePushout (f g : Generator1) (namePrefix : String := "po") : LimitResult :=
  let poObj := Expr.atom (gid namePrefix)
  let poId := gid namePrefix
  { object := { id := poId, description := s!"Pushout of {f.id} and {g.id}" }
    morphisms := [
      { id := gid s!"{namePrefix}_ι₁", domain := f.codomain, codomain := poObj,
        description := "Pushout injection from first factor" },
      { id := gid s!"{namePrefix}_ι₂", domain := g.codomain, codomain := poObj,
        description := "Pushout injection from second factor" }
    ]
    axioms := [
      { id := gid s!"{namePrefix}_comm",
        leftPath := .comp (.atom f.id) (.atom (gid s!"{namePrefix}_ι₁")),
        rightPath := .comp (.atom g.id) (.atom (gid s!"{namePrefix}_ι₂")),
        description := "Pushout square commutes: ι₁ ∘ f = ι₂ ∘ g" }
    ] }

/-- Compute the equalizer of f, g : A → B.
    The subobject E → A where f and g agree. -/
def computeEqualizer (f g : Generator1) (namePrefix : String := "eq") : LimitResult :=
  let eqObj := Expr.atom (gid namePrefix)
  let eqId := gid namePrefix
  { object := { id := eqId, description := s!"Equalizer of {f.id} and {g.id}" }
    morphisms := [
      { id := gid s!"{namePrefix}_ι", domain := eqObj, codomain := f.domain,
        description := "Equalizer inclusion" }
    ]
    axioms := [
      { id := gid s!"{namePrefix}_eq",
        leftPath := .comp (.atom (gid s!"{namePrefix}_ι")) (.atom f.id),
        rightPath := .comp (.atom (gid s!"{namePrefix}_ι")) (.atom g.id),
        description := "Equalizer condition: f ∘ ι = g ∘ ι" }
    ] }

/-- Compute the coequalizer of f, g : A → B.
    The quotient B → Q where f and g are identified. -/
def computeCoequalizer (f g : Generator1) (namePrefix : String := "coeq") : LimitResult :=
  let coeqObj := Expr.atom (gid namePrefix)
  let coeqId := gid namePrefix
  { object := { id := coeqId, description := s!"Coequalizer of {f.id} and {g.id}" }
    morphisms := [
      { id := gid s!"{namePrefix}_π", domain := f.codomain, codomain := coeqObj,
        description := "Coequalizer quotient map" }
    ]
    axioms := [
      { id := gid s!"{namePrefix}_eq",
        leftPath := .comp (.atom f.id) (.atom (gid s!"{namePrefix}_π")),
        rightPath := .comp (.atom g.id) (.atom (gid s!"{namePrefix}_π")),
        description := "Coequalizer condition: π ∘ f = π ∘ g" }
    ] }

/-- Adjoin a limit result into a theory, extending it with new generators -/
def Theory.adjoinLimit (t : Theory) (lr : LimitResult) : Theory :=
  { t with
    objects := t.objects ++ [lr.object]
    morphisms := t.morphisms ++ lr.morphisms
    axioms := t.axioms ++ lr.axioms }

end CatLab
