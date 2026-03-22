/-
  CatLab -- Pretty Printer
-/

import Catlab.Core.Theory

namespace CatLab

/-- Pretty-print an expression using mathematical notation -/
partial def Expr.pp : Expr → String
  | .atom gid => gid.name.toString
  | Expr.id obj => s!"id({obj.pp})"
  | .comp f g => s!"{f.pp} ∘ {g.pp}"
  | .prod a b => s!"{a.pp} × {b.pp}"
  | .coprod a b => s!"{a.pp} + {b.pp}"
  | .hom a b => s!"[{a.pp}, {b.pp}]"
  | .tensor a b => s!"{a.pp} ⊗ {b.pp}"
  | .unit => "I"
  | .terminal => "1"
  | .initial => "0"
  | .sigma v base fam => s!"Σ ({v} : {base.pp}), {fam.pp}"
  | .pi v base fam => s!"Π ({v} : {base.pp}), {fam.pp}"
  | .fiber m p => s!"fib({m.pp}, {p.pp})"
  | .proj i _ => s!"π_{i}"
  | .inj i _ => s!"ι_{i}"
  | .var n => n
  | .app f x => s!"{f.pp}({x.pp})"
  | .limit d => s!"lim({d.pp})"
  | .colimit d => s!"colim({d.pp})"
  | .natComponent n x => s!"{n.pp}_{x.pp}"
  | .path A x y => s!"{x.pp} =_{A.pp} {y.pp}"
  | .refl x => s!"refl({x.pp})"
  | .pathJ mot rc tgt pf => s!"J({mot.pp}, {rc.pp}, {tgt.pp}, {pf.pp})"
  | .hcomp sys base => s!"hcomp({sys.pp}, {base.pp})"
  | .fill sys base => s!"fill({sys.pp}, {base.pp})"
  | .coe p a => s!"coe({p.pp}, {a.pp})"
  | .bvar i => s!"#{i}"
  | .fvar uid => s!"?{uid}"
  | .lam v dom body => s!"λ ({v} : {dom.pp}), {body.pp}"
  | .univ n => s!"U_{n}"

instance : ToString Expr where
  toString := Expr.pp

def Generator1.pp (m : Generator1) : String :=
  s!"{m.id.name.toString} : {m.domain.pp} → {m.codomain.pp}"

def Generator2.pp (a : Generator2) : String :=
  s!"{a.id.name.toString} : {a.leftPath.pp} = {a.rightPath.pp}"

def Theory.pp (t : Theory) : String :=
  let header := s!"theory {t.name} : {repr t.doctrine.doctrine} where"
  let objs := t.objects.map (fun o => s!"  sort {o.id.name.toString}") |> String.intercalate "\n"
  let mors := t.morphisms.map (fun m => s!"  {m.pp}") |> String.intercalate "\n"
  let axs := t.axioms.map (fun a => s!"  {a.pp}") |> String.intercalate "\n"
  let sections := [header]
    ++ (if t.objects.isEmpty then [] else ["\n  -- Sorts", objs])
    ++ (if t.morphisms.isEmpty then [] else ["\n  -- Operations", mors])
    ++ (if t.axioms.isEmpty then [] else ["\n  -- Axioms", axs])
  sections |> String.intercalate "\n"

end CatLab
