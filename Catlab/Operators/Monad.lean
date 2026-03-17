/-
  CatLab — Monads & the Eilenberg-Moore Construction

  Given a monad T on a theory C, compute the Eilenberg-Moore category C^T
  (the category of T-algebras).

  Objects of C^T: pairs (A, α : TA → A) satisfying unit and associativity laws
  Morphisms: T-algebra homomorphisms
-/

import Catlab.Core.Theory

namespace CatLab

/-- A monad on a theory: an endomorphism T with unit η and multiplication μ -/
structure MonadData where
  /-- The underlying endofunctor (as a mapping on generator names) -/
  functor : Expr → Expr
  /-- Unit: η_A : A → TA -/
  unit : GeneratorId
  /-- Multiplication: μ_A : TTA → TA -/
  mult : GeneratorId
  /-- The theory this monad acts on -/
  base : Theory

/-- A comonad: dual of a monad, with counit ε and comultiplication δ -/
structure ComonadData where
  functor : Expr → Expr
  counit : GeneratorId
  comult : GeneratorId
  base : Theory

/-- Compute the Eilenberg-Moore category C^T for a monad T.

    Objects are T-algebras: (A, α : TA → A) where
    - α ∘ η_A = id_A  (unit law)
    - α ∘ μ_A = α ∘ Tα  (associativity law) -/
def eilenbergMoore (m : MonadData) : Theory :=
  let algebras := m.base.objects.map fun a =>
    let _ta := m.functor (.atom a.id)
    { id := ⟨s!"Alg({a.id.name})", 0⟩
      description := s!"Free T-algebra on {a.id.name}" }

  let structureMaps := m.base.objects.map fun a =>
    let ta := m.functor (.atom a.id)
    { id := ⟨s!"α_{a.id.name}", 0⟩
      domain := ta
      codomain := .atom a.id
      description := s!"Structure map for T-algebra on {a.id.name}" }

  let unitLaws := m.base.objects.map fun a =>
    { id := ⟨s!"unit_law_{a.id.name}", 0⟩
      leftPath := .comp (.atom m.unit) (.atom ⟨s!"α_{a.id.name}", 0⟩)
      rightPath := .id (.atom a.id)
      description := s!"Unit law: α ∘ η = id for {a.id.name}" }

  let assocLaws := m.base.objects.map fun a =>
    { id := ⟨s!"assoc_law_{a.id.name}", 0⟩
      leftPath := .comp (.atom m.mult) (.atom ⟨s!"α_{a.id.name}", 0⟩)
      rightPath := .comp (m.functor (.atom ⟨s!"α_{a.id.name}", 0⟩)) (.atom ⟨s!"α_{a.id.name}", 0⟩)
      description := s!"Associativity: α ∘ μ = α ∘ Tα for {a.id.name}" }

  { name := s!"{m.base.name}^T"
    doctrine := m.base.doctrine
    objects := algebras
    morphisms := structureMaps
    axioms := unitLaws ++ assocLaws }

/-- Compute the co-Eilenberg-Moore category C_G for a comonad G.
    Objects are G-coalgebras: (A, α : A → GA). -/
def coEilenbergMoore (g : ComonadData) : Theory :=
  let coalgebras := g.base.objects.map fun a =>
    { id := ⟨s!"CoAlg({a.id.name})", 0⟩
      description := s!"G-coalgebra on {a.id.name}" }

  let structureMaps := g.base.objects.map fun a =>
    let ga := g.functor (.atom a.id)
    { id := ⟨s!"δ_{a.id.name}", 0⟩
      domain := .atom a.id
      codomain := ga
      description := s!"Coalgebra structure map for {a.id.name}" }

  { name := s!"{g.base.name}_G"
    doctrine := g.base.doctrine
    objects := coalgebras
    morphisms := structureMaps
    axioms := [] }

end CatLab
