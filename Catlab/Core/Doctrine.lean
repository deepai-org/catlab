/-
  CatLab -- Doctrine System

  A Doctrine specifies what categorical structure is available in a theory.
-/

import Catlab.Core.Expr

namespace CatLab

/-- The hierarchy of categorical doctrines. -/
inductive Doctrine where
  | Category
  | CartesianCategory
  | CartesianClosed
  | MonoidalCategory
  | BraidedMonoidal
  | SymmetricMonoidal
  | SymmetricMonoidalClosed
  | FinitelyComplete
  | FinitelyCocomplete
  | Abelian
  | Topos
  | GrothendieckTopos
  | LawvereTheory
  | StableCategory
  deriving Repr, Inhabited, BEq

def Doctrine.hasProducts : Doctrine → Bool
  | .CartesianCategory | .CartesianClosed | .FinitelyComplete
  | .FinitelyCocomplete | .Abelian | .Topos | .GrothendieckTopos
  | .LawvereTheory => true
  | _ => false

def Doctrine.hasCoproducts : Doctrine → Bool
  | .FinitelyCocomplete | .Abelian | .Topos | .GrothendieckTopos => true
  | _ => false

def Doctrine.hasTensor : Doctrine → Bool
  | .MonoidalCategory | .BraidedMonoidal | .SymmetricMonoidal
  | .SymmetricMonoidalClosed => true
  | _ => false

def Doctrine.hasExponentials : Doctrine → Bool
  | .CartesianClosed | .SymmetricMonoidalClosed | .Topos | .GrothendieckTopos => true
  | _ => false

def Doctrine.hasSubobjectClassifier : Doctrine → Bool
  | .Topos | .GrothendieckTopos => true
  | _ => false

/-- The full doctrine context attached to a theory -/
structure DoctrineContext where
  doctrine : Doctrine
  constraints : List String := []
  deriving Repr, Inhabited

end CatLab
