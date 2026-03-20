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
  | ElementaryTopos
  | MartinLofTypeTheory
  | PresentableInfinityCategory
  | ModelCategory
  | Derivator
  | InfinityNCategory
  | Operad
  | CubicalTypeTheory
  | LinearLogic
  | GeometricLogic
  | CohesiveHomotopyTypeTheory
  | EnrichedCategory
  | TriangulatedCategory
  | Locale
  | DifferentialGraded
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

/-- Does this doctrine describe an inherently higher-categorical structure?
    Higher-categorical doctrines (∞-categories, HoTT, cubical type theory) cannot
    be faithfully represented as strict 1-categorical presentations with equations.
    CatLab's representations of these are strictified approximations that capture
    the syntactic signature (generators and axiom schemas) but not the semantic
    homotopy-coherent structure (higher morphisms, homotopy limits/colimits, etc.). -/
def Doctrine.isHigherCategorical : Doctrine → Bool
  | .MartinLofTypeTheory         => true
  | .PresentableInfinityCategory => true
  | .InfinityNCategory           => true
  | .CubicalTypeTheory           => true
  | .CohesiveHomotopyTypeTheory  => true
  | _ => false

/-- The full doctrine context attached to a theory -/
structure DoctrineContext where
  doctrine : Doctrine
  constraints : List String := []
  /-- If true, this theory is a strictified 1-categorical presentation of a
      higher-categorical structure. Operators like `pushout` compute strict
      colimits, not homotopy colimits. See `Doctrine.isHigherCategorical`. -/
  strictified : Bool := false
  /-- Truncation level: the highest dimension at which the presentation is complete.
      `none` means the theory is not truncated (either not higher-categorical,
      or the full presentation is given).
      `some n` means k-cells for k > n are either absent or collapsed to identities.
      Examples: a 1-category has truncationLevel = some 1,
                an (∞,2)-category presentation has truncationLevel = some 2. -/
  truncationLevel : Option Nat := none
  deriving Repr, Inhabited

end CatLab
