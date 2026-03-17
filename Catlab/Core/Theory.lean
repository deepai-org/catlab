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
