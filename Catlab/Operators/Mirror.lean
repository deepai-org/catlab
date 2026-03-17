/-
  CatLab — Mirror Operator (C^op)

  The opposite category: reverse every morphism's domain and codomain,
  and swap the sides of every equation.

  Mathematically trivial, physically profound: turns algebras into geometries.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Reverse an expression by swapping hom directions -/
def Expr.mirror : Expr → Expr
  | .atom gid => .atom gid
  | Expr.id obj => Expr.id obj.mirror
  | .comp f g => .comp g.mirror f.mirror  -- reverse composition order
  | .prod a b => .coprod a.mirror b.mirror  -- products ↔ coproducts
  | .coprod a b => .prod a.mirror b.mirror
  | .hom a b => .hom b.mirror a.mirror
  | .tensor a b => .tensor a.mirror b.mirror  -- tensor is self-dual
  | .unit => .unit
  | .terminal => .initial  -- terminal ↔ initial
  | .initial => .terminal
  | .sigma v base fam => .pi v base.mirror fam.mirror  -- Σ ↔ Π
  | .pi v base fam => .sigma v base.mirror fam.mirror
  | .fiber m p => .fiber m.mirror p.mirror
  | .proj i s => .inj i s.mirror  -- projections ↔ injections
  | .inj i t => .proj i t.mirror
  | .var n => .var n

/-- The Mirror operator: compute C^op.

    Swaps domain/codomain of every morphism and reverses equation sides.
    This is Stone Duality in action: Boolean Algebra ↦ Stone Spaces. -/
def mirror (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}ᵒᵖ"
    morphisms := t.morphisms.map fun g =>
      { g with
        id := { g.id with name := s!"{g.id.name}ᵒᵖ" }
        domain := g.codomain.mirror
        codomain := g.domain.mirror }
    axioms := t.axioms.map fun a =>
      { a with
        id := { a.id with name := s!"{a.id.name}ᵒᵖ" }
        leftPath := a.rightPath.mirror
        rightPath := a.leftPath.mirror
        proofName := none } }

/-- Mirror is an involution: (C^op)^op ≅ C -/
theorem Expr.mirror_mirror (e : Expr) : e.mirror.mirror = e := by
  induction e <;> simp_all [Expr.mirror]

end CatLab
