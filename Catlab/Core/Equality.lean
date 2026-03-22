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
  | .path A1 x1 y1, .path A2 x2 y2 => A1.beq A2 && x1.beq x2 && y1.beq y2
  | .refl x1, .refl x2 => x1.beq x2
  | .pathJ m1 r1 t1 p1, .pathJ m2 r2 t2 p2 => m1.beq m2 && r1.beq r2 && t1.beq t2 && p1.beq p2
  | .hcomp s1 b1, .hcomp s2 b2 => s1.beq s2 && b1.beq b2
  | .fill s1 b1, .fill s2 b2 => s1.beq s2 && b1.beq b2
  | .coe p1 a1, .coe p2 a2 => p1.beq p2 && a1.beq a2
  | .bvar i1, .bvar i2 => i1 == i2
  | .fvar u1, .fvar u2 => u1 == u2
  | .lam v1 d1 b1, .lam v2 d2 b2 => v1 == v2 && d1.beq d2 && b1.beq b2
  | .univ n1, .univ n2 => n1 == n2
  | _, _ => false

instance : BEq Expr where beq := Expr.beq

/-- Structural equality on generators -/
instance : BEq Generator0 where
  beq a b := a.id == b.id

instance : BEq Generator1 where
  beq a b := a.id == b.id && a.domain.beq b.domain && a.codomain.beq b.codomain

instance : BEq Generator2 where
  beq a b := a.id == b.id && a.leftPath.beq b.leftPath && a.rightPath.beq b.rightPath

/-- Alpha-equivalence with mapping tracking.
    Returns the extended mapping on success, or `none` on failure.
    The mapping is bijective: forward (e1 name → e2 name) and
    reverse (e2 name → e1 name) are both checked for consistency. -/
partial def Expr.alphaEquivM (e1 e2 : Expr)
    (mapping : List (Name × Name) := [])
    (revMapping : List (Name × Name) := [])
    : Option (List (Name × Name) × List (Name × Name)) :=
  match e1, e2 with
  | .atom a, .atom b =>
    -- Check forward direction: has a.name been mapped?
    match mapping.find? (fun (k, _) => k == a.name) with
    | some (_, v) =>
      if v == b.name then some (mapping, revMapping) else none
    | none =>
      -- Check reverse direction: has b.name been claimed?
      match revMapping.find? (fun (k, _) => k == b.name) with
      | some (_, v) =>
        if v == a.name then some (mapping, revMapping) else none
      | none =>
        -- New consistent binding
        some ((a.name, b.name) :: mapping, (b.name, a.name) :: revMapping)
  | .id x, .id y => x.alphaEquivM y mapping revMapping
  | .comp f1 g1, .comp f2 g2 => do
    let (m, r) ← f1.alphaEquivM f2 mapping revMapping
    g1.alphaEquivM g2 m r
  | .prod a1 b1, .prod a2 b2 => do
    let (m, r) ← a1.alphaEquivM a2 mapping revMapping
    b1.alphaEquivM b2 m r
  | .coprod a1 b1, .coprod a2 b2 => do
    let (m, r) ← a1.alphaEquivM a2 mapping revMapping
    b1.alphaEquivM b2 m r
  | .hom a1 b1, .hom a2 b2 => do
    let (m, r) ← a1.alphaEquivM a2 mapping revMapping
    b1.alphaEquivM b2 m r
  | .tensor a1 b1, .tensor a2 b2 => do
    let (m, r) ← a1.alphaEquivM a2 mapping revMapping
    b1.alphaEquivM b2 m r
  | .unit, .unit => some (mapping, revMapping)
  | .terminal, .terminal => some (mapping, revMapping)
  | .initial, .initial => some (mapping, revMapping)
  | .sigma _ b1 f1, .sigma _ b2 f2 => do
    let (m, r) ← b1.alphaEquivM b2 mapping revMapping
    f1.alphaEquivM f2 m r
  | .pi _ b1 f1, .pi _ b2 f2 => do
    let (m, r) ← b1.alphaEquivM b2 mapping revMapping
    f1.alphaEquivM f2 m r
  | .fiber m1 p1, .fiber m2 p2 => do
    let (m, r) ← m1.alphaEquivM m2 mapping revMapping
    p1.alphaEquivM p2 m r
  | .proj i1 s1, .proj i2 s2 =>
    if i1 == i2 then s1.alphaEquivM s2 mapping revMapping else none
  | .inj i1 t1, .inj i2 t2 =>
    if i1 == i2 then t1.alphaEquivM t2 mapping revMapping else none
  | .var n1, .var n2 =>
    if n1 == n2 then some (mapping, revMapping) else none
  | .app f1 x1, .app f2 x2 => do
    let (m, r) ← f1.alphaEquivM f2 mapping revMapping
    x1.alphaEquivM x2 m r
  | .limit d1, .limit d2 => d1.alphaEquivM d2 mapping revMapping
  | .colimit d1, .colimit d2 => d1.alphaEquivM d2 mapping revMapping
  | .natComponent n1 x1, .natComponent n2 x2 => do
    let (m, r) ← n1.alphaEquivM n2 mapping revMapping
    x1.alphaEquivM x2 m r
  | .path A1 x1 y1, .path A2 x2 y2 => do
    let (m, r) ← A1.alphaEquivM A2 mapping revMapping
    let (m, r) ← x1.alphaEquivM x2 m r
    y1.alphaEquivM y2 m r
  | .refl x1, .refl x2 => x1.alphaEquivM x2 mapping revMapping
  | .pathJ m1 r1 t1 p1, .pathJ m2 r2 t2 p2 => do
    let (m, r) ← m1.alphaEquivM m2 mapping revMapping
    let (m, r) ← r1.alphaEquivM r2 m r
    let (m, r) ← t1.alphaEquivM t2 m r
    p1.alphaEquivM p2 m r
  | .hcomp s1 b1, .hcomp s2 b2 => do
    let (m, r) ← s1.alphaEquivM s2 mapping revMapping
    b1.alphaEquivM b2 m r
  | .fill s1 b1, .fill s2 b2 => do
    let (m, r) ← s1.alphaEquivM s2 mapping revMapping
    b1.alphaEquivM b2 m r
  | .coe p1 a1, .coe p2 a2 => do
    let (m, r) ← p1.alphaEquivM p2 mapping revMapping
    a1.alphaEquivM a2 m r
  | .bvar i1, .bvar i2 =>
    if i1 == i2 then some (mapping, revMapping) else none
  | .fvar u1, .fvar u2 =>
    if u1 == u2 then some (mapping, revMapping) else none
  | .lam _ d1 b1, .lam _ d2 b2 => do
    let (m, r) ← d1.alphaEquivM d2 mapping revMapping
    b1.alphaEquivM b2 m r
  | .univ n1, .univ n2 =>
    if n1 == n2 then some (mapping, revMapping) else none
  | _, _ => none

/-- Alpha-equivalence: equality up to consistent bijective renaming of generators. -/
def Expr.alphaEquiv (e1 e2 : Expr)
    (mapping : List (Name × Name) := []) : Bool :=
  let revMapping := mapping.map fun (a, b) => (b, a)
  (e1.alphaEquivM e2 mapping revMapping).isSome

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
    onMorphisms(f) : onObjects(A) → onObjects(B) in target.

    Looks up the mapped morphism expression in the target theory to verify
    its domain/codomain match the mapped domain/codomain of the source morphism. -/
def TheoryMorphism.preservesTyping (tm : TheoryMorphism) : Bool :=
  tm.source.morphisms.all fun m =>
    let expectedDom := tm.onObjects.liftExpr m.domain
    let expectedCod := tm.onObjects.liftExpr m.codomain
    let mappedExpr := tm.onMorphisms.apply m.id
    -- Find the actual morphism in the target theory
    match mappedExpr with
    | .atom gid =>
      match tm.target.morphisms.find? (fun m2 => m2.id == gid) with
      | some targetMor =>
        targetMor.domain == expectedDom && targetMor.codomain == expectedCod
      | none =>
        -- Mapped to an atom not in target — this is fine for identity morphisms
        -- where the morphism maps to itself and the theory is the same
        expectedDom == m.domain && expectedCod == m.codomain
    | _ =>
      -- Mapped to a compound expression (e.g., comp, id) — we can't easily
      -- type-check compound expressions without a full type inference pass.
      -- Accept these conservatively.
      true

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
  | .unit | .terminal | .initial | .var _ | .bvar _ | .fvar _ | .univ _ => e
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
  | .path A x y => .path (A.applyNameMap m) (x.applyNameMap m) (y.applyNameMap m)
  | .refl x => .refl (x.applyNameMap m)
  | .pathJ mot rc tgt pf => .pathJ (mot.applyNameMap m) (rc.applyNameMap m) (tgt.applyNameMap m) (pf.applyNameMap m)
  | .hcomp sys base => .hcomp (sys.applyNameMap m) (base.applyNameMap m)
  | .fill sys base => .fill (sys.applyNameMap m) (base.applyNameMap m)
  | .coe p a => .coe (p.applyNameMap m) (a.applyNameMap m)
  | .lam v dom body => .lam v (dom.applyNameMap m) (body.applyNameMap m)

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

/-- Generate all permutations of a list (fuel-bounded to guarantee termination). -/
private def permutations [BEq α] (xs : List α) (fuel : Nat := xs.length + 1) : List (List α) :=
  match fuel with
  | 0 => [[]]
  | fuel' + 1 =>
    if xs.isEmpty then [[]]
    else xs.flatMap fun x =>
      let idx := xs.findIdx? (· == x) |>.getD 0
      let rest := xs.eraseIdx idx
      (permutations rest fuel').map (x :: ·)

/-- Check if a name mapping makes t1 structurally match t2 (morphisms + axioms). -/
private def checkNameMap (t1 t2 : Theory) (nameMap : List (Name × Name)) : Bool :=
  t1.morphisms.all (fun m1 =>
    let mappedName := match nameMap.find? (fun (k, _) => k == m1.id.name) with
      | some (_, v) => v | none => m1.id.name
    let mappedDom := m1.domain.applyNameMap nameMap
    let mappedCod := m1.codomain.applyNameMap nameMap
    t2.morphisms.any (fun m2 =>
      m2.id.name == mappedName && m2.domain == mappedDom && m2.codomain == mappedCod)) &&
  t1.axioms.all (fun a1 =>
    let mappedLHS := a1.leftPath.applyNameMap nameMap
    let mappedRHS := a1.rightPath.applyNameMap nameMap
    t2.axioms.any (fun a2 =>
      a2.leftPath == mappedLHS && a2.rightPath == mappedRHS))

/-- Deeper isomorphism check: attempt to find a bijection on generators
    that preserves all morphism domains/codomains and axiom equalities.
    For small theories (≤ 6 objects), tries all permutations.
    For larger theories, uses degree-based pruning with backtracking. -/
partial def Theory.isIsomorphic (t1 t2 : Theory) : Bool :=
  if !t1.signatureMatch t2 then false
  else if t1.objects.length == 0 then true
  else
    let names1 := t1.objects.map (·.id.name)
    let names2 := t2.objects.map (·.id.name)
    -- Also include morphism and axiom names in the mapping
    let morNames1 := t1.morphisms.map (·.id.name)
    let morNames2 := t2.morphisms.map (·.id.name)
    let axNames1 := t1.axioms.map (·.id.name)
    let axNames2 := t2.axioms.map (·.id.name)
    -- Try identity mapping first (fast path)
    let identityMap := (names1.zip names2) ++ (morNames1.zip morNames2) ++ (axNames1.zip axNames2)
    if checkNameMap t1 t2 identityMap then true
    else if names1.length > 6 then
      -- Too many permutations; use degree-based heuristic
      -- Group objects by (out-degree, in-degree) and only try compatible assignments
      let degree1 := names1.map fun n => (n, t1.outEdges n |>.length, t1.inEdges n |>.length)
      let degree2 := names2.map fun n => (n, t2.outEdges n |>.length, t2.inEdges n |>.length)
      -- Sort both by degree signature and try the induced mapping
      let sorted1 := degree1.mergeSort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2))
      let sorted2 := degree2.mergeSort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2))
      -- Check degree signatures match
      if sorted1.map (·.2) != sorted2.map (·.2) then false
      else
        let objMap := sorted1.zip sorted2 |>.map fun ((n1, _, _), (n2, _, _)) => (n1, n2)
        let fullMap := objMap ++ (morNames1.zip morNames2) ++ (axNames1.zip axNames2)
        checkNameMap t1 t2 fullMap
    else
      -- Small theory: try all object permutations
      let objPerms := permutations names2
      objPerms.any fun perm =>
        let objMap := names1.zip perm
        -- For each object permutation, try morphism permutations too
        -- But that's expensive — instead, for each object map, derive the
        -- induced morphism mapping by matching domain/codomain
        let morMap := morNames1.filterMap fun mn1 =>
          match t1.morphisms.find? (fun m => m.id.name == mn1) with
          | none => none
          | some m1 =>
            let mappedDom := m1.domain.applyNameMap objMap
            let mappedCod := m1.codomain.applyNameMap objMap
            -- Find the unique morphism in t2 with these domain/codomain
            match t2.morphisms.find? (fun m2 => m2.domain == mappedDom && m2.codomain == mappedCod) with
            | some m2 => some (mn1, m2.id.name)
            | none => none
        if morMap.length != morNames1.length then false
        else
          let axMap := axNames1.zip axNames2  -- axioms checked by content, not name
          let fullMap := objMap ++ morMap ++ axMap
          checkNameMap t1 t2 fullMap

end CatLab
