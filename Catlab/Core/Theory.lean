/-
  CatLab -- Theory Structure

  A Theory is a presentation of a category: generators and relations.
-/

import Catlab.Core.Expr
import Catlab.Core.Doctrine

namespace CatLab

-- ============================================================
-- Generators
-- ============================================================

/-- A 0-generator: a sort / object type -/
structure Generator0 where
  id : GeneratorId
  description : String := ""
  deriving Repr, Inhabited

/-- A 1-generator: a morphism / operation -/
structure Generator1 where
  id : GeneratorId
  domain : Expr
  codomain : Expr
  description : String := ""
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
  deriving Repr, Inhabited

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
  deriving Repr, Inhabited

namespace Theory

def findObject (t : Theory) (name : Name) : Option Generator0 :=
  t.objects.find? (fun g => g.id.name == name)

def findMorphism (t : Theory) (name : Name) : Option Generator1 :=
  t.morphisms.find? (fun g => g.id.name == name)

def findAxiom (t : Theory) (name : Name) : Option Generator2 :=
  t.axioms.find? (fun g => g.id.name == name)

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

end Theory

end CatLab
