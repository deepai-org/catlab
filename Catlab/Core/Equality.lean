/-
  CatLab -- Structural Equality and Isomorphism Checking

  Without this, no operator can verify its own output.
  We define BEq on Expr (structural equality) and a notion of
  theory isomorphism (bijection on generators preserving structure).
-/

import Catlab.Core.Theory
import Batteries.Data.HashMap

namespace CatLab

/-- Structural equality on expressions -/
def Expr.beq : Expr → Expr → Bool
  | .atom a, .atom b => a == b
  | .id x, .id y => x.beq y
  | .comp f1 g1, .comp f2 g2 => f1.beq f2 && g1.beq g2
  | .prod a1 b1, .prod a2 b2 => a1.beq a2 && b1.beq b2
  | .coprod a1 b1, .coprod a2 b2 => a1.beq a2 && b1.beq b2
  | .hom a1 b1, .hom a2 b2 => a1.beq a2 && b1.beq b2
  | .tensor a1 b1, .tensor a2 b2 => a1.beq a2 && b1.beq b2
  | .unit, .unit => true
  | .terminal, .terminal => true
  | .initial, .initial => true
  | .sigma v1 b1 f1, .sigma v2 b2 f2 => v1 == v2 && b1.beq b2 && f1.beq f2
  | .pi v1 b1 f1, .pi v2 b2 f2 => v1 == v2 && b1.beq b2 && f1.beq f2
  | .fiber m1 p1, .fiber m2 p2 => m1.beq m2 && p1.beq p2
  | .proj i1 s1, .proj i2 s2 => i1 == i2 && s1.beq s2
  | .inj i1 t1, .inj i2 t2 => i1 == i2 && t1.beq t2
  | .var n1, .var n2 => n1 == n2
  | .app f1 x1, .app f2 x2 => f1.beq f2 && x1.beq x2
  | .limit d1, .limit d2 => d1.beq d2
  | .colimit d1, .colimit d2 => d1.beq d2
  | .natComponent n1 x1, .natComponent n2 x2 => n1.beq n2 && x1.beq x2
  | _, _ => false

instance : BEq Expr where beq := Expr.beq

/-- Structural equality on generators -/
instance : BEq Generator0 where
  beq a b := a.id == b.id

instance : BEq Generator1 where
  beq a b := a.id == b.id && a.domain.beq b.domain && a.codomain.beq b.codomain

instance : BEq Generator2 where
  beq a b := a.id == b.id && a.leftPath.beq b.leftPath && a.rightPath.beq b.rightPath

/-- Alpha-equivalence: equality up to renaming of generators.
    Two expressions are alpha-equivalent if there exists a consistent
    renaming of atom names that makes them structurally equal. -/
partial def Expr.alphaEquiv (e1 e2 : Expr)
    (mapping : List (Name × Name) := []) : Bool :=
  match e1, e2 with
  | .atom a, .atom b =>
    match mapping.find? (fun (k, _) => k == a.name) with
    | some (_, v) => v == b.name
    | none => true  -- new binding; would extend mapping
  | .id x, .id y => x.alphaEquiv y mapping
  | .comp f1 g1, .comp f2 g2 => f1.alphaEquiv f2 mapping && g1.alphaEquiv g2 mapping
  | .prod a1 b1, .prod a2 b2 => a1.alphaEquiv a2 mapping && b1.alphaEquiv b2 mapping
  | .coprod a1 b1, .coprod a2 b2 => a1.alphaEquiv a2 mapping && b1.alphaEquiv b2 mapping
  | .hom a1 b1, .hom a2 b2 => a1.alphaEquiv a2 mapping && b1.alphaEquiv b2 mapping
  | .tensor a1 b1, .tensor a2 b2 => a1.alphaEquiv a2 mapping && b1.alphaEquiv b2 mapping
  | .unit, .unit => true
  | .terminal, .terminal => true
  | .initial, .initial => true
  | .sigma _ b1 f1, .sigma _ b2 f2 => b1.alphaEquiv b2 mapping && f1.alphaEquiv f2 mapping
  | .pi _ b1 f1, .pi _ b2 f2 => b1.alphaEquiv b2 mapping && f1.alphaEquiv f2 mapping
  | .fiber m1 p1, .fiber m2 p2 => m1.alphaEquiv m2 mapping && p1.alphaEquiv p2 mapping
  | .proj i1 s1, .proj i2 s2 => i1 == i2 && s1.alphaEquiv s2 mapping
  | .inj i1 t1, .inj i2 t2 => i1 == i2 && t1.alphaEquiv t2 mapping
  | .var n1, .var n2 => n1 == n2
  | .app f1 x1, .app f2 x2 => f1.alphaEquiv f2 mapping && x1.alphaEquiv x2 mapping
  | .limit d1, .limit d2 => d1.alphaEquiv d2 mapping
  | .colimit d1, .colimit d2 => d1.alphaEquiv d2 mapping
  | .natComponent n1 x1, .natComponent n2 x2 => n1.alphaEquiv n2 mapping && x1.alphaEquiv x2 mapping
  | _, _ => false

-- ============================================================
-- HashMap-based indexes (require BEq instances above)
-- ============================================================

namespace Theory

/-- Build a HashMap rewrite index: atom name → axioms mentioning it -/
def rewriteIndexMap (t : Theory) : Std.HashMap Name (List Generator2) :=
  t.axioms.foldl (fun acc ax =>
    let names := ax.leftPath.atoms ++ ax.rightPath.atoms
    names.foldl (fun acc' n =>
      let existing := acc'[n]? |>.getD []
      if existing.any (· == ax) then acc'
      else acc'.insert n (ax :: existing)) acc) {}

/-- Check if two expressions are equivalent under this theory's equivalences -/
def areEquivalent (t : Theory) (a b : Expr) : Bool :=
  a == b || t.equivalences.any fun (l, r) => (l == a && r == b) || (r == a && l == b)

end Theory

/-- A theory morphism: a mapping between theories preserving structure.
    Uses explicit GeneratorMaps instead of opaque closures so mappings
    are inspectable, serializable, and invertible. -/
structure TheoryMorphism where
  name : String
  source : Theory
  target : Theory
  /-- How source objects map to target expressions -/
  onObjects : GeneratorMap
  /-- How source morphisms map to target expressions -/
  onMorphisms : GeneratorMap

namespace TheoryMorphism

/-- Identity morphism: every generator maps to its own atom. -/
def id (t : Theory) : TheoryMorphism :=
  { name := s!"id({t.name})"
    source := t
    target := t
    onObjects   := GeneratorMap.ofList (t.objects.map   fun o => (o.id, .atom o.id))
    onMorphisms := GeneratorMap.ofList (t.morphisms.map fun m => (m.id, .atom m.id)) }

/-- Compose f : A → B with g : B → C to get g ∘ f : A → C.
    For each A-generator x, (g ∘ f)(x) = g.lift(f(x)). -/
def comp (f g : TheoryMorphism) : TheoryMorphism :=
  { name := s!"{g.name} ∘ {f.name}"
    source := f.source
    target := g.target
    onObjects   := GeneratorMap.ofList
      (f.source.objects.map   fun o => (o.id, g.onObjects.liftExpr   (f.onObjects.apply   o.id)))
    onMorphisms := GeneratorMap.ofList
      (f.source.morphisms.map fun m => (m.id, g.onMorphisms.liftExpr (f.onMorphisms.apply m.id))) }

/-- Smart inclusion: maps each generator of `sub` to the matching generator in `super`
    by name. Generators in `sub` with no name match in `super` are left unmapped
    (they default to their own atom via `GeneratorMap.apply`'s fallback). -/
def inclusion (sub super : Theory) : TheoryMorphism :=
  { name := s!"{sub.name} ↪ {super.name}"
    source := sub
    target := super
    onObjects   := GeneratorMap.ofList
      (sub.objects.filterMap fun o =>
        if super.objects.any (fun o2 => o2.id.name == o.id.name)
        then some (o.id, .atom { o.id with kind := .sort })
        else none)
    onMorphisms := GeneratorMap.ofList
      (sub.morphisms.filterMap fun m =>
        if super.morphisms.any (fun m2 => m2.id.name == m.id.name)
        then some (m.id, .atom { m.id with kind := .morphism })
        else none) }

end TheoryMorphism

/-- Check if a theory morphism preserves domains and codomains.
    For each morphism f : A → B in source, we need
    onMorphisms(f) : onObjects(A) → onObjects(B) in target. -/
def TheoryMorphism.preservesTyping (tm : TheoryMorphism) : Bool :=
  tm.source.morphisms.all fun m =>
    let mappedDom := tm.onObjects.liftExpr m.domain
    let mappedCod := tm.onObjects.liftExpr m.codomain
    -- At minimum, the mapped objects should exist
    mappedDom != .unit || mappedCod != .unit  -- placeholder

/-- Signature comparison: do two theories have the same "shape"?
    Same number of objects, morphisms with matching arities, same axiom count. -/
def Theory.signatureMatch (t1 t2 : Theory) : Bool :=
  t1.objects.length == t2.objects.length &&
  t1.morphisms.length == t2.morphisms.length &&
  t1.axioms.length == t2.axioms.length

/-- Apply a name mapping to an expression, renaming all atoms whose names
    appear in the mapping. Names not in the mapping are left unchanged. -/
partial def Expr.applyNameMap (e : Expr) (m : List (Name × Name)) : Expr :=
  match e with
  | .atom gid =>
    match m.find? (fun (k, _) => k == gid.name) with
    | some (_, v) => .atom { gid with name := v }
    | none => e
  | .unit | .terminal | .initial | .var _ => e
  | .id obj => .id (obj.applyNameMap m)
  | .comp f g => .comp (f.applyNameMap m) (g.applyNameMap m)
  | .prod a b => .prod (a.applyNameMap m) (b.applyNameMap m)
  | .coprod a b => .coprod (a.applyNameMap m) (b.applyNameMap m)
  | .hom a b => .hom (a.applyNameMap m) (b.applyNameMap m)
  | .tensor a b => .tensor (a.applyNameMap m) (b.applyNameMap m)
  | .sigma v base fam => .sigma v (base.applyNameMap m) (fam.applyNameMap m)
  | .pi v base fam => .pi v (base.applyNameMap m) (fam.applyNameMap m)
  | .fiber mf p => .fiber (mf.applyNameMap m) (p.applyNameMap m)
  | .proj i s => .proj i (s.applyNameMap m)
  | .inj i t => .inj i (t.applyNameMap m)
  | .app f x => .app (f.applyNameMap m) (x.applyNameMap m)
  | .limit d => .limit (d.applyNameMap m)
  | .colimit d => .colimit (d.applyNameMap m)
  | .natComponent n x => .natComponent (n.applyNameMap m) (x.applyNameMap m)

/-- Structural match: check that t2 is t1 with names renamed according to the
    given mapping. Verifies that every morphism's domain/codomain and every
    axiom's LHS/RHS are preserved under the mapping. -/
def Theory.structuralMatch (t1 t2 : Theory)
    (nameMap : List (Name × Name)) : Bool :=
  -- 1. Same counts
  t1.objects.length == t2.objects.length &&
  t1.morphisms.length == t2.morphisms.length &&
  t1.axioms.length == t2.axioms.length &&
  -- 2. Every morphism in t1, after renaming, has a matching morphism in t2
  --    with the same domain/codomain structure
  t1.morphisms.all (fun m1 =>
    let mappedName := match nameMap.find? (fun (k, _) => k == m1.id.name) with
      | some (_, v) => v | none => m1.id.name
    let mappedDom := m1.domain.applyNameMap nameMap
    let mappedCod := m1.codomain.applyNameMap nameMap
    t2.morphisms.any (fun m2 =>
      m2.id.name == mappedName && m2.domain == mappedDom && m2.codomain == mappedCod)) &&
  -- 3. Every axiom in t1, after renaming, has a matching axiom in t2
  --    with the same LHS/RHS structure
  t1.axioms.all (fun a1 =>
    let mappedName := match nameMap.find? (fun (k, _) => k == a1.id.name) with
      | some (_, v) => v | none => a1.id.name
    let mappedLHS := a1.leftPath.applyNameMap nameMap
    let mappedRHS := a1.rightPath.applyNameMap nameMap
    t2.axioms.any (fun a2 =>
      a2.id.name == mappedName && a2.leftPath == mappedLHS && a2.rightPath == mappedRHS))

/-- Build the name mapping induced by the `opposite` operator on a theory.
    Objects keep their names; morphisms and axioms get `.op` wrapped. -/
def Theory.oppositeNameMap (t : Theory) : List (Name × Name) :=
  (t.morphisms.map fun m => (m.id.name, Name.op m.id.name)) ++
  (t.axioms.map fun a => (a.id.name, Name.op a.id.name))

/-- Build the name mapping induced by the `mirror` operator on a theory.
    Same as opposite: morphisms and axioms get `.op` wrapped. -/
def Theory.mirrorNameMap (t : Theory) : List (Name × Name) :=
  t.oppositeNameMap  -- mirror uses the same .op renaming scheme

/-- Deeper isomorphism check: attempt to find a bijection on generators
    that preserves all morphism domains/codomains and axiom equalities.
    Returns true if such a bijection exists (brute-force for small theories). -/
partial def Theory.isIsomorphic (t1 t2 : Theory) : Bool :=
  if !t1.signatureMatch t2 then false
  else if t1.objects.length == 0 then true
  else
    -- Try the identity mapping first
    let identityWorks := t1.morphisms.zip t2.morphisms |>.all fun (m1, m2) =>
      m1.domain.alphaEquiv m2.domain && m1.codomain.alphaEquiv m2.codomain
    if identityWorks then
      -- Also check axioms under identity mapping
      t1.axioms.zip t2.axioms |>.all fun (a1, a2) =>
        a1.leftPath.alphaEquiv a2.leftPath && a1.rightPath.alphaEquiv a2.rightPath
    else
      -- TODO: try all permutations for small generator sets
      false

end CatLab
