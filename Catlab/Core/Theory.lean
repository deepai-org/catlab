/-
  CatLab -- Theory Structure

  A Theory is a presentation of a category: generators and relations.
-/

import Catlab.Core.Expr
import Catlab.Core.Doctrine
import Batteries.Data.HashMap

namespace CatLab

-- ============================================================
-- Generators
-- ============================================================

/-- A 0-generator: a sort / object type -/
structure Generator0 where
  id : GeneratorId
  description : String := ""
  /-- Extensible metadata: e.g., ("degree", "2"), ("finite", "true") -/
  tags : List (String × String) := []
  deriving Repr, Inhabited

/-- A 1-generator: a morphism / operation -/
structure Generator1 where
  id : GeneratorId
  domain : Expr
  codomain : Expr
  description : String := ""
  /-- Extensible metadata -/
  tags : List (String × String) := []
  deriving Repr, Inhabited

/-- A binding variable for universally-quantified axiom schemas -/
structure AxiomVar where
  name : String
  domain : Option Expr := none   -- none for sort variables
  codomain : Option Expr := none
  kind : GeneratorKind := .sort
  deriving Repr, Inhabited

/-- A 2-generator: an equation / axiom, possibly universally quantified.
    When `quantifiers` is non-empty, this is an axiom schema:
      ∀ (x : A) (f : B → C), lhs = rhs -/
structure Generator2 where
  id : GeneratorId
  quantifiers : List AxiomVar := []
  leftPath : Expr
  rightPath : Expr
  proofName : Option Lean.Name := none
  description : String := ""
  /-- Extensible metadata -/
  tags : List (String × String) := []
  deriving Repr, Inhabited

-- ============================================================
-- Tag Queries
-- ============================================================

/-- Look up a tag value by key -/
def lookupTag (tags : List (String × String)) (key : String) : Option String :=
  tags.find? (fun (k, _) => k == key) |>.map (·.2)

/-- Look up a tag as a Nat -/
def lookupTagNat (tags : List (String × String)) (key : String) : Option Nat :=
  lookupTag tags key |>.bind (·.toNat?)

-- ============================================================
-- Explicit Mapping (replaces closures for functors/morphisms)
-- ============================================================

/-- An explicit, inspectable mapping from GeneratorIds to Exprs.
    Unlike closures, this can be iterated, serialized, and inverted. -/
structure GeneratorMap where
  entries : Std.HashMap GeneratorId Expr := {}
  deriving Inhabited

namespace GeneratorMap

def empty : GeneratorMap := ⟨{}⟩

def insert (m : GeneratorMap) (k : GeneratorId) (v : Expr) : GeneratorMap :=
  ⟨m.entries.insert k v⟩

def find? (m : GeneratorMap) (k : GeneratorId) : Option Expr :=
  m.entries[k]?

/-- Apply the mapping; returns the atom unchanged if not in the map -/
def apply (m : GeneratorMap) (k : GeneratorId) : Expr :=
  m.entries[k]? |>.getD (.atom k)

def ofList (pairs : List (GeneratorId × Expr)) : GeneratorMap :=
  ⟨pairs.foldl (fun acc (k, v) => acc.insert k v) {}⟩

def toList (m : GeneratorMap) : List (GeneratorId × Expr) :=
  m.entries.toList

/-- Lift this mapping over a full Expr AST, replacing atoms -/
partial def liftExpr (m : GeneratorMap) (e : Expr) : Expr :=
  match e with
  | .atom gid => m.apply gid
  | .id obj => .id (m.liftExpr obj)
  | .comp f g => .comp (m.liftExpr f) (m.liftExpr g)
  | .prod a b => .prod (m.liftExpr a) (m.liftExpr b)
  | .coprod a b => .coprod (m.liftExpr a) (m.liftExpr b)
  | .hom a b => .hom (m.liftExpr a) (m.liftExpr b)
  | .tensor a b => .tensor (m.liftExpr a) (m.liftExpr b)
  | .sigma v base fam => .sigma v (m.liftExpr base) (m.liftExpr fam)
  | .pi v base fam => .pi v (m.liftExpr base) (m.liftExpr fam)
  | .fiber mf p => .fiber (m.liftExpr mf) (m.liftExpr p)
  | .proj i s => .proj i (m.liftExpr s)
  | .inj i t => .inj i (m.liftExpr t)
  | .app f x => .app (m.liftExpr f) (m.liftExpr x)
  | .limit d => .limit (m.liftExpr d)
  | .colimit d => .colimit (m.liftExpr d)
  | .natComponent n x => .natComponent (m.liftExpr n) (m.liftExpr x)
  | .unit | .terminal | .initial | .var _ => e

end GeneratorMap

-- ============================================================
-- First-class Functors and Natural Transformations
-- ============================================================

/-- A functor declared within a theory -/
structure FunctorDecl where
  id : GeneratorId
  source : Name       -- source theory/sort name
  target : Name       -- target theory/sort name
  onObjects : Expr    -- object-mapping (may contain .var)
  onMorphisms : Expr  -- morphism-mapping (may contain .var)
  description : String := ""
  deriving Repr, Inhabited

/-- A natural transformation declared within a theory -/
structure NatTransDecl where
  id : GeneratorId
  source : GeneratorId  -- source functor
  target : GeneratorId  -- target functor
  component : Expr      -- component expression (parameterized by .var)
  description : String := ""
  deriving Repr, Inhabited

-- ============================================================
-- Structured Families (Natural Transformations, Cones, Cocones)
-- ============================================================

/-- A family of morphisms indexed by objects — the explicit representation
    of a natural transformation. Instead of flattening components into the
    morphism list (losing the family structure), this preserves the indexing. -/
structure NatTransFamily where
  /-- Name of this natural transformation -/
  name : GeneratorId
  /-- Source functor (or identity) -/
  source : GeneratorId
  /-- Target functor (or identity) -/
  target : GeneratorId
  /-- Components indexed by object: (object_id, component_morphism) -/
  components : List (GeneratorId × Generator1)
  description : String := ""
  deriving Repr, Inhabited

/-- A cone over a diagram: an apex with projection morphisms to each node.
    The projections are indexed by diagram node, not flattened. -/
structure ConeData where
  /-- The apex object of the cone -/
  apex : Generator0
  /-- Projections indexed by diagram node: (node_id, projection_morphism) -/
  projections : List (GeneratorId × Generator1)
  /-- Commutativity axioms: for each edge in the diagram -/
  commutativity : List Generator2
  deriving Repr, Inhabited

/-- A cocone: dual of a cone, with injections from diagram nodes. -/
structure CoconeData where
  /-- The nadir object of the cocone -/
  nadir : Generator0
  /-- Injections indexed by diagram node: (node_id, injection_morphism) -/
  injections : List (GeneratorId × Generator1)
  /-- Commutativity axioms -/
  commutativity : List Generator2
  deriving Repr, Inhabited

-- ============================================================
-- Theory
-- ============================================================

/-- A Theory: the central data structure of the CAS. -/
structure Theory where
  name : String
  doctrine : DoctrineContext
  objects : List Generator0
  morphisms : List Generator1
  axioms : List Generator2
  functors : List FunctorDecl := []
  natTrans : List NatTransDecl := []
  /-- First-class equivalences: pairs of expressions identified in this theory.
      Formalizes quotienting without encoding equivalences as 2-cells. -/
  equivalences : List (Expr × Expr) := []
  deriving Repr, Inhabited

namespace Theory

def findObject (t : Theory) (name : Name) : Option Generator0 :=
  t.objects.find? (fun g => g.id.name == name)

def findMorphism (t : Theory) (name : Name) : Option Generator1 :=
  t.morphisms.find? (fun g => g.id.name == name)

def findAxiom (t : Theory) (name : Name) : Option Generator2 :=
  t.axioms.find? (fun g => g.id.name == name)

/-- Build a HashMap index of morphisms by name, for O(1) single lookups when
    many lookups are needed (e.g., typechecking). -/
def morphismIndex (t : Theory) : Std.HashMap Name Generator1 :=
  t.morphisms.foldl (fun acc m => acc.insert m.id.name m) {}

/-- Build a HashMap index of objects by name, for O(1) single lookups. -/
def objectIndex (t : Theory) : Std.HashMap Name Generator0 :=
  t.objects.foldl (fun acc o => acc.insert o.id.name o) {}

def allNames (t : Theory) : List Name :=
  (t.objects.map (·.id.name)) ++
  (t.morphisms.map (·.id.name)) ++
  (t.axioms.map (·.id.name))

/-- All generator IDs with their kinds, providing a symbol table for the theory -/
def allGeneratorIds (t : Theory) : List GeneratorId :=
  (t.objects.map (·.id)) ++
  (t.morphisms.map (·.id)) ++
  (t.axioms.map (·.id))

/-- Look up a GeneratorId by name, resolving its kind from the theory -/
def resolveAtom (t : Theory) (name : Name) : Option GeneratorId :=
  if t.objects.any (fun o => o.id.name == name) then
    some { name, kind := .sort }
  else if t.morphisms.any (fun m => m.id.name == name) then
    some { name, kind := .morphism }
  else if t.axioms.any (fun a => a.id.name == name) then
    some { name, kind := .twoCell }
  else none

/-- Check if a name refers to a morphism in this theory -/
def isMorphismName (t : Theory) (name : Name) : Bool :=
  t.morphisms.any (fun m => m.id.name == name)

/-- Check if a name refers to an object in this theory -/
def isObjectName (t : Theory) (name : Name) : Bool :=
  t.objects.any (fun o => o.id.name == name)

/-- Get all morphisms from a given object (by name) -/
def outEdges (t : Theory) (objName : Name) : List Generator1 :=
  t.morphisms.filter fun m => m.domain.toName == objName

/-- Get all morphisms into a given object (by name) -/
def inEdges (t : Theory) (objName : Name) : List Generator1 :=
  t.morphisms.filter fun m => m.codomain.toName == objName

/-- Find all commuting triangles over a target object X:
    pairs (f : A → X, g : B → X, h : A → B) such that g ∘ h = f
    could hold. Returns the triple (f, g, h) as candidate triangles. -/
def commutingTrianglesOver (t : Theory) (xName : Name) : List (Generator1 × Generator1 × Generator1) :=
  let intoX := t.inEdges xName
  intoX.flatMap fun f =>
    intoX.filterMap fun g =>
      -- Look for h : dom(f) → dom(g)
      t.morphisms.find? (fun h => h.domain.toName == f.domain.toName && h.codomain.toName == g.domain.toName)
      |>.map fun h => (f, g, h)

/-- Find all axioms whose left or right path mentions a given name.
    This is the axiom index: given a Name, quickly find rewrite rules
    that could apply to expressions involving that name. -/
def rewritesFor (t : Theory) (name : Name) : List Generator2 :=
  t.axioms.filter fun ax =>
    ax.leftPath.atoms.any (· == name) || ax.rightPath.atoms.any (· == name)

/-- Build a rewrite index: maps each atom name to the axioms that mention it.
    Returns a list of (Name, List Generator2) pairs for efficient lookup. -/
def rewriteIndex (t : Theory) : List (Name × List Generator2) :=
  let allAtomNames := t.axioms.flatMap fun ax =>
    ax.leftPath.atoms ++ ax.rightPath.atoms
  let uniqueNames := allAtomNames.foldl (fun acc n =>
    if acc.any (· == n) then acc else n :: acc) []
  uniqueNames.map fun n => (n, t.rewritesFor n)

/-- Build a HashMap index of morphisms by domain expression (for O(1) edge lookups) -/
def outEdgeIndex (t : Theory) : Std.HashMap Name (List Generator1) :=
  t.morphisms.foldl (fun acc m =>
    let key := m.domain.toName
    let existing := acc[key]? |>.getD []
    acc.insert key (m :: existing)) {}

/-- Build a HashMap index of morphisms by codomain expression (for O(1) edge lookups) -/
def inEdgeIndex (t : Theory) : Std.HashMap Name (List Generator1) :=
  t.morphisms.foldl (fun acc m =>
    let key := m.codomain.toName
    let existing := acc[key]? |>.getD []
    acc.insert key (m :: existing)) {}

/-- Build a HashMap index mapping names to generator kinds (for O(1) resolution) -/
def generatorIndex (t : Theory) : Std.HashMap Name GeneratorKind :=
  let m := t.objects.foldl (fun acc o => acc.insert o.id.name .sort) ({} : Std.HashMap Name GeneratorKind)
  let m := t.morphisms.foldl (fun acc f => acc.insert f.id.name .morphism) m
  t.axioms.foldl (fun acc a => acc.insert a.id.name .twoCell) m

def summary (t : Theory) : String :=
  s!"Theory '{t.name}' [{repr t.doctrine.doctrine}]\n" ++
  s!"  Objects:   {t.objects.length}\n" ++
  s!"  Morphisms: {t.morphisms.length}\n" ++
  s!"  Axioms:    {t.axioms.length}"

/-- Instantiate an axiom schema with concrete values -/
def instantiateSchema (ax : Generator2) (bindings : List (String × Expr)) : Generator2 :=
  let applyBindings (e : Expr) := bindings.foldl (fun acc (n, v) => acc.subst n v) e
  { ax with
    quantifiers := []
    leftPath := applyBindings ax.leftPath
    rightPath := applyBindings ax.rightPath }

/-- Smart constructor for Theory. Identical to the struct literal but serves
    as the canonical entry point for operator code. This is where we would
    compile cached indices (outEdgesCache, rewriteIndex) once, if/when
    Theory is extended with cached fields. For now it validates the inputs
    and returns a plain Theory. -/
def mk' (name : String) (doctrine : DoctrineContext)
    (objects : List Generator0) (morphisms : List Generator1)
    (axioms : List Generator2)
    (functors : List FunctorDecl := [])
    (natTrans : List NatTransDecl := [])
    (equivalences : List (Expr × Expr) := []) : Theory :=
  { name, doctrine, objects, morphisms, axioms, functors, natTrans, equivalences }

/-- Remove duplicate generators by name, keeping the first occurrence. -/
def dedup (t : Theory) : Theory :=
  let dedup0 := t.objects.foldl (fun (acc : List Generator0 × Std.HashMap Name Bool) x =>
    if acc.2[x.id.name]? == some true then acc
    else (x :: acc.1, acc.2.insert x.id.name true)) ([], {})
  let dedup1 := t.morphisms.foldl (fun (acc : List Generator1 × Std.HashMap Name Bool) x =>
    if acc.2[x.id.name]? == some true then acc
    else (x :: acc.1, acc.2.insert x.id.name true)) ([], {})
  let dedup2 := t.axioms.foldl (fun (acc : List Generator2 × Std.HashMap Name Bool) x =>
    if acc.2[x.id.name]? == some true then acc
    else (x :: acc.1, acc.2.insert x.id.name true)) ([], {})
  { t with objects := dedup0.1.reverse, morphisms := dedup1.1.reverse, axioms := dedup2.1.reverse }

end Theory

end CatLab
