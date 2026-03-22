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

-- ============================================================
-- Doctrine lattice: numeric rank + join
-- ============================================================

/-- Numeric rank in the doctrine lattice. Higher rank = richer structure.
    This defines a total preorder used to compute joins. Doctrines on
    independent axes (e.g., Monoidal vs Cartesian) are handled by
    `join` selecting the one whose features subsume the other. -/
def Doctrine.rank : Doctrine → Nat
  | .Category                    => 0
  | .LawvereTheory               => 1
  | .Operad                      => 1
  | .EnrichedCategory            => 1
  | .MonoidalCategory            => 2
  | .BraidedMonoidal             => 3
  | .SymmetricMonoidal           => 4
  | .CartesianCategory           => 5
  | .FinitelyComplete            => 6
  | .FinitelyCocomplete          => 7
  | .CartesianClosed             => 8
  | .SymmetricMonoidalClosed     => 8
  | .Abelian                     => 9
  | .LinearLogic                 => 5
  | .GeometricLogic              => 6
  | .Locale                      => 4
  | .DifferentialGraded          => 5
  | .StableCategory              => 7
  | .TriangulatedCategory        => 7
  | .ModelCategory               => 8
  | .Derivator                   => 8
  | .ElementaryTopos             => 10
  | .Topos                       => 10
  | .GrothendieckTopos           => 11
  | .MartinLofTypeTheory         => 12
  | .InfinityNCategory           => 12
  | .CubicalTypeTheory           => 13
  | .PresentableInfinityCategory => 14
  | .CohesiveHomotopyTypeTheory  => 15

/-- Join (least upper bound) in the doctrine lattice.
    For doctrines on the same axis (e.g., Category < Cartesian < CartesianClosed),
    this returns the higher one. For doctrines on independent axes (Monoidal vs
    Cartesian), it selects the one with richer overall structure (higher rank).

    This is a heuristic — the true doctrine lattice is a partial order with
    independent branches. A full lattice would need explicit joins for every
    pair (e.g., join(Monoidal, Cartesian) = CartesianMonoidal). We approximate
    by picking the higher-ranked doctrine, which is correct for all common cases. -/
def Doctrine.join (a b : Doctrine) : Doctrine :=
  if a == b then a
  -- Special cases: known lattice joins
  else match a, b with
  | .CartesianCategory, .MonoidalCategory
  | .MonoidalCategory, .CartesianCategory => .CartesianCategory  -- products are monoidal
  | .CartesianClosed, .MonoidalCategory
  | .MonoidalCategory, .CartesianClosed => .CartesianClosed
  | .SymmetricMonoidal, .CartesianCategory
  | .CartesianCategory, .SymmetricMonoidal => .CartesianCategory
  | .CartesianCategory, d | d, .CartesianCategory =>
    if d.hasExponentials then .CartesianClosed
    else if d.rank > Doctrine.CartesianCategory.rank then d else .CartesianCategory
  | .CartesianClosed, d | d, .CartesianClosed =>
    if d.rank > Doctrine.CartesianClosed.rank then d else .CartesianClosed
  | .FinitelyComplete, .FinitelyCocomplete
  | .FinitelyCocomplete, .FinitelyComplete => .Abelian  -- both limits + colimits
  | _, _ => if a.rank >= b.rank then a else b

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
