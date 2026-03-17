/-
  CatLab -- Categorical Abstract Syntax Trees

  The Expr type is the internal representation for all categorical expressions.
  It serves as the IR that every operator transforms.
-/

namespace CatLab

-- ============================================================
-- Structured Names
-- ============================================================

/-- Structured name for generators — an AST that preserves provenance.
    Instead of flattening structured data into strings, names carry
    their construction history so operators can decompose them. -/
inductive Name where
  | root (name : String)
  | nested (parent : Name) (child : String)
  | inl (inner : Name)
  | inr (inner : Name)
  | op (inner : Name)
  | app (functor : Name) (arg : Name)
  /-- Graded name: base name at a specific degree (e.g., N(C)_2 for 2-simplices) -/
  | graded (base : Name) (degree : Nat)
  /-- Pair of names: for comma objects (a, b, h), product objects, etc. -/
  | pair (left : Name) (right : Name)
  /-- Arrow between names: for objects that are morphisms (arrow category, comma) -/
  | arrow (src : Name) (tgt : Name) (label : Name)
  /-- Tensor product of names: for Eckmann-Hilton and Day convolution -/
  | tensor (left : Name) (right : Name)
  /-- Simplicial face map name: dᵢ at dimension n -/
  | simplexFace (i : Nat) (dim : Nat)
  /-- Simplicial degeneracy map name: sᵢ at dimension n -/
  | simplexDegeneracy (i : Nat) (dim : Nat)
  /-- Negation of a name (for Heyting/Boolean operators) -/
  | neg (inner : Name)
  deriving Repr, Hashable, Inhabited

partial def Name.toString : Name → String
  | .root s => s
  | .nested parent child => s!"{parent.toString}.{child}"
  | .inl inner => s!"inl({inner.toString})"
  | .inr inner => s!"inr({inner.toString})"
  | .op inner => s!"{inner.toString}ᵒᵖ"
  | .app f x => s!"{f.toString}({x.toString})"
  | .graded base n => s!"{base.toString}_{n}"
  | .pair l r => s!"({l.toString},{r.toString})"
  | .arrow s t l => s!"({s.toString}→{t.toString}:{l.toString})"
  | .tensor l r => s!"{l.toString}⊗{r.toString}"
  | .simplexFace i n => s!"d_{i}^{n}"
  | .simplexDegeneracy i n => s!"s_{i}^{n}"
  | .neg inner => s!"¬{inner.toString}"

partial def Name.beq : Name → Name → Bool
  | .root a, .root b => a == b
  | .nested p1 c1, .nested p2 c2 => p1.beq p2 && c1 == c2
  | .inl a, .inl b => a.beq b
  | .inr a, .inr b => a.beq b
  | .op a, .op b => a.beq b
  | .app f1 x1, .app f2 x2 => f1.beq f2 && x1.beq x2
  | .graded b1 n1, .graded b2 n2 => b1.beq b2 && n1 == n2
  | .pair l1 r1, .pair l2 r2 => l1.beq l2 && r1.beq r2
  | .arrow s1 t1 l1, .arrow s2 t2 l2 => s1.beq s2 && t1.beq t2 && l1.beq l2
  | .tensor l1 r1, .tensor l2 r2 => l1.beq l2 && r1.beq r2
  | .simplexFace i1 n1, .simplexFace i2 n2 => i1 == i2 && n1 == n2
  | .simplexDegeneracy i1 n1, .simplexDegeneracy i2 n2 => i1 == i2 && n1 == n2
  | .neg a, .neg b => a.beq b
  | _, _ => false

/-- Extract the graded degree from a Name, if it is graded -/
def Name.degree? : Name → Option Nat
  | .graded _ n => some n
  | _ => none

/-- Extract the left component of a pair or tensor Name -/
def Name.left? : Name → Option Name
  | .pair l _ => some l
  | .tensor l _ => some l
  | _ => none

/-- Extract the right component of a pair or tensor Name -/
def Name.right? : Name → Option Name
  | .pair _ r => some r
  | .tensor _ r => some r
  | _ => none

/-- Check if a Name is a negation -/
def Name.isNeg? : Name → Option Name
  | .neg inner => some inner
  | _ => none

/-- Check if a Name is a simplex face map -/
def Name.isSimplexFace? : Name → Option (Nat × Nat)
  | .simplexFace i n => some (i, n)
  | _ => none

/-- Check if a Name is a simplex degeneracy map -/
def Name.isSimplexDegeneracy? : Name → Option (Nat × Nat)
  | .simplexDegeneracy i n => some (i, n)
  | _ => none

instance : BEq Name where beq := Name.beq
instance : ToString Name where toString := Name.toString

-- ============================================================
-- Generator Kinds
-- ============================================================

/-- The dimensional level of a generator -/
inductive GeneratorKind where
  | sort
  | morphism
  | twoCell
  deriving Repr, BEq, Hashable, Inhabited

-- ============================================================
-- Generator Identifiers
-- ============================================================

/-- A typed, namespaced generator identifier -/
structure GeneratorId where
  name : Name
  index : Nat := 0
  kind : GeneratorKind := .sort
  deriving Repr, Hashable, Inhabited

def GeneratorId.beq (a b : GeneratorId) : Bool :=
  a.name == b.name && a.kind == b.kind && a.index == b.index

instance : BEq GeneratorId where beq := GeneratorId.beq

instance : ToString GeneratorId where
  toString g :=
    let base := g.name.toString
    if g.index == 0 then base else s!"{base}_{g.index}"

/-- Shorthand: create a GeneratorId from a string -/
def gid (s : String) (idx : Nat := 0) (k : GeneratorKind := .sort) : GeneratorId :=
  ⟨.root s, idx, k⟩

-- ============================================================
-- The Core Expression Type
-- ============================================================

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
  -- Functor application: F(X)
  | app (functor : Expr) (arg : Expr)
  -- Limits and colimits over a diagram
  | limit (diagram : Expr)
  | colimit (diagram : Expr)
  -- Natural transformation component: α_X
  | natComponent (nat : Expr) (atObj : Expr)

instance : Inhabited Expr := ⟨.unit⟩
deriving instance Repr for Expr

namespace Expr

/-- Shorthand: atom from string -/
def atom' (name : String) : Expr := .atom (gid name)

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

/-- Deterministically flatten an Expr into a Name, preserving structure.
    Unlike the old `exprName` hack, this handles all Expr constructors
    instead of silently degrading to `"?"`. -/
partial def Expr.toName : Expr → Name
  | .atom g => g.name
  | .id obj => .app (.root "id") obj.toName
  | .comp f g => .app (.app (.root "∘") f.toName) g.toName
  | .prod a b => .pair a.toName b.toName
  | .coprod a b => .app (.app (.root "⊔") a.toName) b.toName
  | .hom a b => .arrow a.toName b.toName (.root "hom")
  | .tensor a b => .tensor a.toName b.toName
  | .unit => .root "𝟙"
  | .terminal => .root "⊤"
  | .initial => .root "⊥"
  | .sigma v base fam => .app (.app (.root s!"Σ_{v}") base.toName) fam.toName
  | .pi v base fam => .app (.app (.root s!"Π_{v}") base.toName) fam.toName
  | .fiber m p => .app (.app (.root "fib") m.toName) p.toName
  | .proj i src => .app (.root s!"π_{i}") src.toName
  | .inj i tgt => .app (.root s!"ι_{i}") tgt.toName
  | .var n => .root n
  | .app f x => .app f.toName x.toName
  | .limit d => .app (.root "lim") d.toName
  | .colimit d => .app (.root "colim") d.toName
  | .natComponent n x => .app n.toName x.toName

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
  | .app f x => .app (f.subst name replacement) (x.subst name replacement)
  | .limit d => .limit (d.subst name replacement)
  | .colimit d => .colimit (d.subst name replacement)
  | .natComponent n x => .natComponent (n.subst name replacement) (x.subst name replacement)

/-- Apply a function to every atom in an expression -/
partial def Expr.mapAtoms (e : Expr) (f : Expr → Expr) : Expr :=
  match e with
  | .atom _ => f e
  | .unit | .terminal | .initial | .var _ => e
  | .id obj => .id (obj.mapAtoms f)
  | .comp a b => .comp (a.mapAtoms f) (b.mapAtoms f)
  | .prod a b => .prod (a.mapAtoms f) (b.mapAtoms f)
  | .coprod a b => .coprod (a.mapAtoms f) (b.mapAtoms f)
  | .hom a b => .hom (a.mapAtoms f) (b.mapAtoms f)
  | .tensor a b => .tensor (a.mapAtoms f) (b.mapAtoms f)
  | .sigma v base fam => .sigma v (base.mapAtoms f) (fam.mapAtoms f)
  | .pi v base fam => .pi v (base.mapAtoms f) (fam.mapAtoms f)
  | .fiber m p => .fiber (m.mapAtoms f) (p.mapAtoms f)
  | .proj i s => .proj i (s.mapAtoms f)
  | .inj i t => .inj i (t.mapAtoms f)
  | .app fn x => .app (fn.mapAtoms f) (x.mapAtoms f)
  | .limit d => .limit (d.mapAtoms f)
  | .colimit d => .colimit (d.mapAtoms f)
  | .natComponent n x => .natComponent (n.mapAtoms f) (x.mapAtoms f)

/-- Map over generator names in an expression -/
partial def Expr.mapNames (e : Expr) (f : Name → Name) : Expr :=
  match e with
  | .atom gid => .atom { gid with name := f gid.name }
  | .unit | .terminal | .initial | .var _ => e
  | .id obj => .id (obj.mapNames f)
  | .comp a b => .comp (a.mapNames f) (b.mapNames f)
  | .prod a b => .prod (a.mapNames f) (b.mapNames f)
  | .coprod a b => .coprod (a.mapNames f) (b.mapNames f)
  | .hom a b => .hom (a.mapNames f) (b.mapNames f)
  | .tensor a b => .tensor (a.mapNames f) (b.mapNames f)
  | .sigma v base fam => .sigma v (base.mapNames f) (fam.mapNames f)
  | .pi v base fam => .pi v (base.mapNames f) (fam.mapNames f)
  | .fiber m p => .fiber (m.mapNames f) (p.mapNames f)
  | .proj i s => .proj i (s.mapNames f)
  | .inj i t => .inj i (t.mapNames f)
  | .app fn x => .app (fn.mapNames f) (x.mapNames f)
  | .limit d => .limit (d.mapNames f)
  | .colimit d => .colimit (d.mapNames f)
  | .natComponent n x => .natComponent (n.mapNames f) (x.mapNames f)

end CatLab
