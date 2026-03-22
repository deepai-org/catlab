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
  a.name == b.name && a.index == b.index

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
  -- ── Identity/Path types (HoTT) ─────────────────────────────────────────────
  -- The type of paths between x and y in space A: x =_A y
  | path (A x y : Expr)
  -- Reflexivity: the constant path at x
  | refl (x : Expr)
  -- Path induction (J-eliminator): J motive reflCase target proof
  --   motive   : Π (y : A) (p : x =_A y). U    (the dependent motive)
  --   reflCase : motive x (refl x)               (what to return at refl)
  --   target   : A                                (the endpoint)
  --   proof    : x =_A target                     (the path being eliminated)
  | pathJ (motive reflCase target proof : Expr)
  -- ── Cubical/HoTT constructors ─────────────────────────────────────────────
  -- Homogeneous composition: Kan filler output (the missing face of a box)
  | hcomp (system base : Expr)
  -- Fill: the interior of the box (the actual higher-dimensional cell)
  | fill (system base : Expr)
  -- Coercion/transport: given path p : A = B and term a : A, produce a term of B
  | coe (path term : Expr)
  -- ── Locally nameless variable binding ──────────────────────────────────────
  -- Bound variable: de Bruijn index (only appears under a binder)
  | bvar (index : Nat)
  -- Free variable: unique identifier (introduced when opening a binder)
  | fvar (uid : Nat)
  -- Lambda abstraction: λ (binderName : domain). body
  -- The body uses bvar 0 for the bound variable
  | lam (binderName : String) (domain : Expr) (body : Expr)
  -- ── Universe levels ──────────────────────────────────────────────────────
  -- The universe of types at level n: U_n : U_{n+1}
  | univ (level : Nat)

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
  | .path A x y => .app (.app (.app (.root "=") A.toName) x.toName) y.toName
  | .refl x => .app (.root "refl") x.toName
  | .pathJ mot rc tgt pf => .app (.app (.app (.app (.root "J") mot.toName) rc.toName) tgt.toName) pf.toName
  | .hcomp sys base => .app (.app (.root "hcomp") sys.toName) base.toName
  | .fill sys base => .app (.app (.root "fill") sys.toName) base.toName
  | .coe p a => .app (.app (.root "coe") p.toName) a.toName
  | .bvar i => .root s!"#{i}"
  | .fvar uid => .root s!"?{uid}"
  | .lam v dom body => .app (.app (.root s!"λ_{v}") dom.toName) body.toName
  | .univ n => .root s!"U_{n}"

/-- Substitution: replace free occurrences of var name with replacement -/
def Expr.subst (e : Expr) (name : String) (replacement : Expr) : Expr :=
  match e with
  | .var n => if n == name then replacement else e
  | .atom _ | .unit | .terminal | .initial | .bvar _ | .fvar _ | .univ _ => e
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
  | .path A x y => .path (A.subst name replacement) (x.subst name replacement) (y.subst name replacement)
  | .refl x => .refl (x.subst name replacement)
  | .pathJ mot rc tgt pf => .pathJ (mot.subst name replacement) (rc.subst name replacement) (tgt.subst name replacement) (pf.subst name replacement)
  | .hcomp sys base => .hcomp (sys.subst name replacement) (base.subst name replacement)
  | .fill sys base => .fill (sys.subst name replacement) (base.subst name replacement)
  | .coe p a => .coe (p.subst name replacement) (a.subst name replacement)
  | .lam v dom body =>
    .lam v (dom.subst name replacement) (body.subst name replacement)

/-- Apply a function to every atom in an expression -/
partial def Expr.mapAtoms (e : Expr) (f : Expr → Expr) : Expr :=
  match e with
  | .atom _ => f e
  | .unit | .terminal | .initial | .var _ | .bvar _ | .fvar _ | .univ _ => e
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
  | .path A x y => .path (A.mapAtoms f) (x.mapAtoms f) (y.mapAtoms f)
  | .refl x => .refl (x.mapAtoms f)
  | .pathJ mot rc tgt pf => .pathJ (mot.mapAtoms f) (rc.mapAtoms f) (tgt.mapAtoms f) (pf.mapAtoms f)
  | .hcomp sys base => .hcomp (sys.mapAtoms f) (base.mapAtoms f)
  | .fill sys base => .fill (sys.mapAtoms f) (base.mapAtoms f)
  | .coe p a => .coe (p.mapAtoms f) (a.mapAtoms f)
  | .lam v dom body => .lam v (dom.mapAtoms f) (body.mapAtoms f)

/-- Map over generator names in an expression -/
partial def Expr.mapNames (e : Expr) (f : Name → Name) : Expr :=
  match e with
  | .atom gid => .atom { gid with name := f gid.name }
  | .unit | .terminal | .initial | .var _ | .bvar _ | .fvar _ | .univ _ => e
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
  | .path A x y => .path (A.mapNames f) (x.mapNames f) (y.mapNames f)
  | .refl x => .refl (x.mapNames f)
  | .pathJ mot rc tgt pf => .pathJ (mot.mapNames f) (rc.mapNames f) (tgt.mapNames f) (pf.mapNames f)
  | .hcomp sys base => .hcomp (sys.mapNames f) (base.mapNames f)
  | .fill sys base => .fill (sys.mapNames f) (base.mapNames f)
  | .coe p a => .coe (p.mapNames f) (a.mapNames f)
  | .lam v dom body => .lam v (dom.mapNames f) (body.mapNames f)

/-- Collect all atom GeneratorIds referenced in an expression -/
def Expr.atomIds : Expr → List GeneratorId
  | .atom gid => [gid]
  | Expr.id obj => obj.atomIds
  | .comp f g => f.atomIds ++ g.atomIds
  | .prod a b => a.atomIds ++ b.atomIds
  | .coprod a b => a.atomIds ++ b.atomIds
  | .hom a b => a.atomIds ++ b.atomIds
  | .tensor a b => a.atomIds ++ b.atomIds
  | .sigma _ base fam => base.atomIds ++ fam.atomIds
  | .pi _ base fam => base.atomIds ++ fam.atomIds
  | .fiber m p => m.atomIds ++ p.atomIds
  | .proj _ s => s.atomIds
  | .inj _ t => t.atomIds
  | .app f x => f.atomIds ++ x.atomIds
  | .limit d => d.atomIds
  | .colimit d => d.atomIds
  | .natComponent n x => n.atomIds ++ x.atomIds
  | .path A x y => A.atomIds ++ x.atomIds ++ y.atomIds
  | .refl x => x.atomIds
  | .pathJ mot rc tgt pf => mot.atomIds ++ rc.atomIds ++ tgt.atomIds ++ pf.atomIds
  | .hcomp sys base => sys.atomIds ++ base.atomIds
  | .fill sys base => sys.atomIds ++ base.atomIds
  | .coe p a => p.atomIds ++ a.atomIds
  | .lam _ dom body => dom.atomIds ++ body.atomIds
  | .unit | .terminal | .initial | .var _ | .bvar _ | .fvar _ | .univ _ => []

/-- Collect all atom names referenced in an expression -/
def Expr.atoms (e : Expr) : List Name :=
  e.atomIds.map (·.name)

-- ============================================================
-- Locally Nameless Binding Operations
-- ============================================================

/-- Lift (shift) all bound variable indices ≥ cutoff by `offset`.
    Used when pushing a term under additional binders. -/
partial def Expr.liftBVars (e : Expr) (offset : Nat) (cutoff : Nat := 0) : Expr :=
  match e with
  | .bvar i => if i >= cutoff then .bvar (i + offset) else e
  | .fvar _ | .atom _ | .unit | .terminal | .initial | .var _ | .univ _ => e
  | .id obj => .id (obj.liftBVars offset cutoff)
  | .comp f g => .comp (f.liftBVars offset cutoff) (g.liftBVars offset cutoff)
  | .prod a b => .prod (a.liftBVars offset cutoff) (b.liftBVars offset cutoff)
  | .coprod a b => .coprod (a.liftBVars offset cutoff) (b.liftBVars offset cutoff)
  | .hom a b => .hom (a.liftBVars offset cutoff) (b.liftBVars offset cutoff)
  | .tensor a b => .tensor (a.liftBVars offset cutoff) (b.liftBVars offset cutoff)
  | .sigma v base fam => .sigma v (base.liftBVars offset cutoff) (fam.liftBVars offset (cutoff + 1))
  | .pi v base fam => .pi v (base.liftBVars offset cutoff) (fam.liftBVars offset (cutoff + 1))
  | .lam v dom body => .lam v (dom.liftBVars offset cutoff) (body.liftBVars offset (cutoff + 1))
  | .fiber m p => .fiber (m.liftBVars offset cutoff) (p.liftBVars offset cutoff)
  | .proj i s => .proj i (s.liftBVars offset cutoff)
  | .inj i t => .inj i (t.liftBVars offset cutoff)
  | .app f x => .app (f.liftBVars offset cutoff) (x.liftBVars offset cutoff)
  | .limit d => .limit (d.liftBVars offset cutoff)
  | .colimit d => .colimit (d.liftBVars offset cutoff)
  | .natComponent n x => .natComponent (n.liftBVars offset cutoff) (x.liftBVars offset cutoff)
  | .path A x y => .path (A.liftBVars offset cutoff) (x.liftBVars offset cutoff) (y.liftBVars offset cutoff)
  | .refl x => .refl (x.liftBVars offset cutoff)
  | .pathJ mot rc tgt pf => .pathJ (mot.liftBVars offset cutoff) (rc.liftBVars offset cutoff) (tgt.liftBVars offset cutoff) (pf.liftBVars offset cutoff)
  | .hcomp sys base => .hcomp (sys.liftBVars offset cutoff) (base.liftBVars offset cutoff)
  | .fill sys base => .fill (sys.liftBVars offset cutoff) (base.liftBVars offset cutoff)
  | .coe p a => .coe (p.liftBVars offset cutoff) (a.liftBVars offset cutoff)

/-- Instantiate: replace `bvar level` with `replacement` and decrement higher bvars.
    This is the "open" operation — it substitutes a term for the outermost bound variable.
    Call with level=0 to open the outermost binder. -/
partial def Expr.instantiate (e : Expr) (level : Nat) (replacement : Expr) : Expr :=
  match e with
  | .bvar i =>
    if i == level then replacement
    else if i > level then .bvar (i - 1)
    else e
  | .fvar _ | .atom _ | .unit | .terminal | .initial | .var _ | .univ _ => e
  | .id obj => .id (obj.instantiate level replacement)
  | .comp f g => .comp (f.instantiate level replacement) (g.instantiate level replacement)
  | .prod a b => .prod (a.instantiate level replacement) (b.instantiate level replacement)
  | .coprod a b => .coprod (a.instantiate level replacement) (b.instantiate level replacement)
  | .hom a b => .hom (a.instantiate level replacement) (b.instantiate level replacement)
  | .tensor a b => .tensor (a.instantiate level replacement) (b.instantiate level replacement)
  | .sigma v base fam =>
    .sigma v (base.instantiate level replacement) (fam.instantiate (level + 1) (replacement.liftBVars 1))
  | .pi v base fam =>
    .pi v (base.instantiate level replacement) (fam.instantiate (level + 1) (replacement.liftBVars 1))
  | .lam v dom body =>
    .lam v (dom.instantiate level replacement) (body.instantiate (level + 1) (replacement.liftBVars 1))
  | .fiber m p => .fiber (m.instantiate level replacement) (p.instantiate level replacement)
  | .proj i s => .proj i (s.instantiate level replacement)
  | .inj i t => .inj i (t.instantiate level replacement)
  | .app f x => .app (f.instantiate level replacement) (x.instantiate level replacement)
  | .limit d => .limit (d.instantiate level replacement)
  | .colimit d => .colimit (d.instantiate level replacement)
  | .natComponent n x => .natComponent (n.instantiate level replacement) (x.instantiate level replacement)
  | .path A x y => .path (A.instantiate level replacement) (x.instantiate level replacement) (y.instantiate level replacement)
  | .refl x => .refl (x.instantiate level replacement)
  | .pathJ mot rc tgt pf => .pathJ (mot.instantiate level replacement) (rc.instantiate level replacement) (tgt.instantiate level replacement) (pf.instantiate level replacement)
  | .hcomp sys base => .hcomp (sys.instantiate level replacement) (base.instantiate level replacement)
  | .fill sys base => .fill (sys.instantiate level replacement) (base.instantiate level replacement)
  | .coe p a => .coe (p.instantiate level replacement) (a.instantiate level replacement)

/-- Abstract: replace `fvar uid` with `bvar level` and increment higher bvars.
    This is the "close" operation — it captures a free variable under a binder.
    Call with level=0 to abstract the outermost binder. -/
partial def Expr.abstractOver (e : Expr) (uid : Nat) (level : Nat := 0) : Expr :=
  match e with
  | .fvar u => if u == uid then .bvar level else e
  | .bvar i => if i >= level then .bvar (i + 1) else e
  | .atom _ | .unit | .terminal | .initial | .var _ | .univ _ => e
  | .id obj => .id (obj.abstractOver uid level)
  | .comp f g => .comp (f.abstractOver uid level) (g.abstractOver uid level)
  | .prod a b => .prod (a.abstractOver uid level) (b.abstractOver uid level)
  | .coprod a b => .coprod (a.abstractOver uid level) (b.abstractOver uid level)
  | .hom a b => .hom (a.abstractOver uid level) (b.abstractOver uid level)
  | .tensor a b => .tensor (a.abstractOver uid level) (b.abstractOver uid level)
  | .sigma v base fam =>
    .sigma v (base.abstractOver uid level) (fam.abstractOver uid (level + 1))
  | .pi v base fam =>
    .pi v (base.abstractOver uid level) (fam.abstractOver uid (level + 1))
  | .lam v dom body =>
    .lam v (dom.abstractOver uid level) (body.abstractOver uid (level + 1))
  | .fiber m p => .fiber (m.abstractOver uid level) (p.abstractOver uid level)
  | .proj i s => .proj i (s.abstractOver uid level)
  | .inj i t => .inj i (t.abstractOver uid level)
  | .app f x => .app (f.abstractOver uid level) (x.abstractOver uid level)
  | .limit d => .limit (d.abstractOver uid level)
  | .colimit d => .colimit (d.abstractOver uid level)
  | .natComponent n x => .natComponent (n.abstractOver uid level) (x.abstractOver uid level)
  | .path A x y => .path (A.abstractOver uid level) (x.abstractOver uid level) (y.abstractOver uid level)
  | .refl x => .refl (x.abstractOver uid level)
  | .pathJ mot rc tgt pf => .pathJ (mot.abstractOver uid level) (rc.abstractOver uid level) (tgt.abstractOver uid level) (pf.abstractOver uid level)
  | .hcomp sys base => .hcomp (sys.abstractOver uid level) (base.abstractOver uid level)
  | .fill sys base => .fill (sys.abstractOver uid level) (base.abstractOver uid level)
  | .coe p a => .coe (p.abstractOver uid level) (a.abstractOver uid level)

/-- Convenience: open the outermost binder with a fresh fvar -/
def Expr.openBinder (e : Expr) (uid : Nat) : Expr :=
  e.instantiate 0 (.fvar uid)

/-- Convenience: close over a fvar to form a binder body -/
def Expr.closeBinder (e : Expr) (uid : Nat) : Expr :=
  e.abstractOver uid 0

/-- Check if an expression has any dangling bvars (bvar ≥ depth).
    Well-formed closed expressions should return false. -/
partial def Expr.hasFreeBVars (e : Expr) (depth : Nat := 0) : Bool :=
  match e with
  | .bvar i => i >= depth
  | .fvar _ | .atom _ | .unit | .terminal | .initial | .var _ | .univ _ => false
  | .id obj => obj.hasFreeBVars depth
  | .comp f g | .prod f g | .coprod f g | .hom f g | .tensor f g
  | .fiber f g | .app f g | .natComponent f g
  | .hcomp f g | .fill f g | .coe f g =>
    f.hasFreeBVars depth || g.hasFreeBVars depth
  | .path A x y => A.hasFreeBVars depth || x.hasFreeBVars depth || y.hasFreeBVars depth
  | .refl x => x.hasFreeBVars depth
  | .pathJ mot rc tgt pf => mot.hasFreeBVars depth || rc.hasFreeBVars depth || tgt.hasFreeBVars depth || pf.hasFreeBVars depth
  | .sigma _ b f | .pi _ b f | .lam _ b f =>
    b.hasFreeBVars depth || f.hasFreeBVars (depth + 1)
  | .proj _ s | .inj _ s | .limit s | .colimit s => s.hasFreeBVars depth

/-- Collect all fvar uids in an expression -/
partial def Expr.fvarIds (e : Expr) : List Nat :=
  match e with
  | .fvar uid => [uid]
  | .bvar _ | .atom _ | .unit | .terminal | .initial | .var _ | .univ _ => []
  | .id obj => obj.fvarIds
  | .comp f g | .prod f g | .coprod f g | .hom f g | .tensor f g
  | .fiber f g | .app f g | .natComponent f g
  | .hcomp f g | .fill f g | .coe f g =>
    f.fvarIds ++ g.fvarIds
  | .path A x y => A.fvarIds ++ x.fvarIds ++ y.fvarIds
  | .refl x => x.fvarIds
  | .pathJ mot rc tgt pf => mot.fvarIds ++ rc.fvarIds ++ tgt.fvarIds ++ pf.fvarIds
  | .sigma _ b f | .pi _ b f | .lam _ b f =>
    b.fvarIds ++ f.fvarIds
  | .proj _ s | .inj _ s | .limit s | .colimit s => s.fvarIds

-- ============================================================
-- Derived path operations (macros over J)
-- ============================================================

/-- Path composition (transitivity): given p : x =_A y and q : y =_A z,
    produce (p ⬝ q) : x =_A z.

    Built via J-elimination on q:
      motive  = λ (z : A) (q : y =_A z). x =_A z
      reflCase = p   (when q is refl y, the composite is just p)
      target  = z
      proof   = q

    The J-eliminator reduces: J motive p z q
    When q = refl y, this reduces to p.
    The e-graph / Hyperion will handle associativity natively. -/
def Expr.trans (A x y z p q : Expr) : Expr :=
  -- motive: λ (z : A) (q : y =_A z). x =_A z
  -- Using locally nameless: body references bvar 1 for z, bvar 0 for q
  let motive := Expr.lam "z" A (.lam "q" (.path A y (.bvar 1)) (.path A x (.bvar 1)))
  .pathJ motive p z q

/-- Path inverse (symmetry): given p : x =_A y, produce p⁻¹ : y =_A x.

    Built via J-elimination on p:
      motive  = λ (y : A) (p : x =_A y). y =_A x
      reflCase = refl x   (when p is refl x, the inverse is refl x)
      target  = y
      proof   = p -/
def Expr.symm (A x y p : Expr) : Expr :=
  let motive := Expr.lam "y" A (.lam "p" (.path A x (.bvar 1)) (.path A (.bvar 1) x))
  .pathJ motive (.refl x) y p

/-- ap (functorial action on paths): given f : A → B and p : x =_A y,
    produce ap f p : f(x) =_B f(y).

    Built via J-elimination on p:
      motive  = λ (y : A) (p : x =_A y). f(x) =_B f(y)
      reflCase = refl (f x)
      target  = y
      proof   = p -/
def Expr.ap (A B x y f p : Expr) : Expr :=
  let motive := Expr.lam "y" A (.lam "p" (.path A x (.bvar 1)) (.path B (.app f x) (.app f (.bvar 1))))
  .pathJ motive (.refl (.app f x)) y p

end CatLab
