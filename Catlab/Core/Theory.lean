/-
  CatLab -- Theory Structure

  A Theory is a presentation of a category: generators and relations.
-/

import Catlab.Core.Expr
import Catlab.Core.Doctrine

namespace CatLab

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

/-- A 2-generator: an equation / axiom -/
structure Generator2 where
  id : GeneratorId
  leftPath : Expr
  rightPath : Expr
  proofName : Option Lean.Name := none
  description : String := ""
  deriving Repr, Inhabited

/-- A Theory: the central data structure of the CAS. -/
structure Theory where
  name : String
  doctrine : DoctrineContext
  objects : List Generator0
  morphisms : List Generator1
  axioms : List Generator2
  deriving Repr, Inhabited

namespace Theory

def findObject (t : Theory) (name : String) : Option Generator0 :=
  t.objects.find? (fun g => g.id.name == name)

def findMorphism (t : Theory) (name : String) : Option Generator1 :=
  t.morphisms.find? (fun g => g.id.name == name)

def findAxiom (t : Theory) (name : String) : Option Generator2 :=
  t.axioms.find? (fun g => g.id.name == name)

def allNames (t : Theory) : List String :=
  (t.objects.map (·.id.name)) ++
  (t.morphisms.map (·.id.name)) ++
  (t.axioms.map (·.id.name))

def summary (t : Theory) : String :=
  s!"Theory '{t.name}' [{repr t.doctrine.doctrine}]\n" ++
  s!"  Objects:   {t.objects.length}\n" ++
  s!"  Morphisms: {t.morphisms.length}\n" ++
  s!"  Axioms:    {t.axioms.length}"

end Theory

end CatLab
