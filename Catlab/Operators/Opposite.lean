/-
  CatLab — Opposite Category (C^op)

  The straightforward categorical opposite: same objects, reversed morphisms,
  reversed composition. Unlike Mirror.lean (which swaps products/coproducts,
  limits/colimits, etc. for theory duality), this is the plain opposite
  category construction.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Rename atoms of morphisms with `.op` -/
private def opRenameAtoms (t : Theory) (e : Expr) : Expr :=
  e.mapAtoms fun
    | .atom g =>
      if t.morphisms.any (fun m => m.id == g) then
        .atom { g with name := .op g.name }
      else .atom g
    | other => other

/-- Reverse composition in an expression, and rename morphism atoms with `.op`.
    This is simpler than `mirror`: it only reverses `.comp` and renames atoms,
    leaving products, coproducts, limits, etc. untouched. -/
partial def Expr.opposite (t : Theory) : Expr → Expr
  | .atom g =>
    if t.morphisms.any (fun m => m.id == g) then
      .atom { g with name := .op g.name }
    else .atom g
  | .id obj => .id obj
  | .comp f g => .comp (g.opposite t) (f.opposite t)  -- reverse composition
  | .hom a b => .hom b a  -- swap hom direction
  | .prod a b => .prod (a.opposite t) (b.opposite t)
  | .coprod a b => .coprod (a.opposite t) (b.opposite t)
  | .tensor a b => .tensor (a.opposite t) (b.opposite t)
  | .unit => .unit
  | .terminal => .terminal
  | .initial => .initial
  | .var n => .var n
  | .app fn x => .app (fn.opposite t) (x.opposite t)
  | .sigma v base fam => .sigma v (base.opposite t) (fam.opposite t)
  | .pi v base fam => .pi v (base.opposite t) (fam.opposite t)
  | .fiber m p => .fiber (m.opposite t) (p.opposite t)
  | .proj i s => .proj i (s.opposite t)
  | .inj i s => .inj i (s.opposite t)
  | .limit d => .limit (d.opposite t)
  | .colimit d => .colimit (d.opposite t)
  | .natComponent n x => .natComponent (n.opposite t) (x.opposite t)
  | .path A x y => .path (A.opposite t) (y.opposite t) (x.opposite t)
  | .refl x => .refl (x.opposite t)
  | .pathJ mot rc tgt pf => .pathJ (mot.opposite t) (rc.opposite t) (tgt.opposite t) (pf.opposite t)
  | .hcomp sys base => .hcomp (sys.opposite t) (base.opposite t)
  | .fill sys base => .fill (sys.opposite t) (base.opposite t)
  | .coe p a => .coe (p.opposite t) (a.opposite t)
  | .bvar i => .bvar i
  | .fvar uid => .fvar uid
  | .lam v dom body => .lam v (dom.opposite t) (body.opposite t)
  | .univ n => .univ n

/-- Compute C^op, the opposite category.

    Objects stay the same. Morphisms f : A → B become f^op : B → A.
    Composition is reversed: (g ∘ f)^op = f^op ∘ g^op.
    Axiom paths are reversed and morphism atoms renamed with `.op`. -/
def opposite (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}ᵒᵖ"
    morphisms := t.morphisms.map fun g =>
      { g with
        id := { g.id with name := .op g.id.name }
        domain := g.codomain
        codomain := g.domain }
    axioms := t.axioms.map fun a =>
      { a with
        id := { a.id with name := .op a.id.name }
        leftPath := a.rightPath.opposite t
        rightPath := a.leftPath.opposite t
        proofName := none } }

end CatLab
