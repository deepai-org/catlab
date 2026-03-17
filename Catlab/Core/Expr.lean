/-
  CatLab -- Categorical Abstract Syntax Trees

  The Expr type is the internal representation for all categorical expressions.
  It serves as the IR that every operator transforms.
-/

namespace CatLab

/-- A named generator identifier -/
structure GeneratorId where
  name : String
  index : Nat := 0
  deriving Repr, BEq, Hashable, Inhabited

instance : ToString GeneratorId where
  toString g := if g.index == 0 then g.name else s!"{g.name}_{g.index}"

/-- The core expression type for categorical ASTs. -/
inductive Expr where
  | atom (id : GeneratorId)
  | id (obj : Expr)
  | comp (f g : Expr)
  | prod (a b : Expr)
  | coprod (a b : Expr)
  | hom (a b : Expr)
  | tensor (a b : Expr)
  | unit
  | terminal
  | initial
  | sigma (varName : String) (base : Expr) (family : Expr)
  | pi (varName : String) (base : Expr) (family : Expr)
  | fiber (morphism : Expr) (point : Expr)
  | proj (index : Nat) (source : Expr)
  | inj (index : Nat) (target : Expr)
  | var (name : String)

instance : Inhabited Expr := ⟨.unit⟩
deriving instance Repr for Expr

namespace Expr

def atom' (name : String) : Expr := .atom ⟨name, 0⟩

def compList : List Expr → Expr
  | [] => .unit
  | [f] => f
  | f :: fs => .comp f (compList fs)

def prodList : List Expr → Expr
  | [] => .terminal
  | [a] => a
  | a :: as => .prod a (prodList as)

def coprodList : List Expr → Expr
  | [] => .initial
  | [a] => a
  | a :: as => .coprod a (coprodList as)

def tensorList : List Expr → Expr
  | [] => .unit
  | [a] => a
  | a :: as => .tensor a (tensorList as)

end Expr

/-- Substitution: replace free occurrences of var name with replacement -/
def Expr.subst (e : Expr) (name : String) (replacement : Expr) : Expr :=
  match e with
  | .var n => if n == name then replacement else e
  | .atom _ | .unit | .terminal | .initial => e
  | .id obj => .id (obj.subst name replacement)
  | .comp f g => .comp (f.subst name replacement) (g.subst name replacement)
  | .prod a b => .prod (a.subst name replacement) (b.subst name replacement)
  | .coprod a b => .coprod (a.subst name replacement) (b.subst name replacement)
  | .hom a b => .hom (a.subst name replacement) (b.subst name replacement)
  | .tensor a b => .tensor (a.subst name replacement) (b.subst name replacement)
  | .sigma v base fam =>
    if v == name then .sigma v (base.subst name replacement) fam
    else .sigma v (base.subst name replacement) (fam.subst name replacement)
  | .pi v base fam =>
    if v == name then .pi v (base.subst name replacement) fam
    else .pi v (base.subst name replacement) (fam.subst name replacement)
  | .fiber m p => .fiber (m.subst name replacement) (p.subst name replacement)
  | .proj i s => .proj i (s.subst name replacement)
  | .inj i t => .inj i (t.subst name replacement)

end CatLab
