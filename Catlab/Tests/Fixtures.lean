/-
  CatLab — Test Fixtures

  Canonical instances of complex input types for use in category-C tests.
  Each fixture is the simplest valid value for its type.
-/

import Catlab.Core.Theory
import Catlab.Operators.Monad
import Catlab.Operators.Ultrapower
import Catlab.Operators.Fractions
import Catlab.Operators.Skolem
import Catlab.Operators.Grothendieck
import Catlab.Operators.Kan
import Catlab.Operators.Localize
import Catlab.Operators.Sheafify
import Catlab.Operators.Quotient
import Catlab.Library.Monoid
import Catlab.Library.Group

namespace CatLab.Tests.Fixtures

open CatLab CatLab.Library

-- ============================================================
-- UltrafilterSpec — generic non-principal ultrafilter on ℕ
-- ============================================================

def ultrafilterN : UltrafilterSpec :=
  { name := "U", indexSet := gid "ℕ" }

-- ============================================================
-- MonadData — identity monad T = Id on a theory
-- ============================================================

/-- Identity monad on an arbitrary theory: T(A) = A, η = id, μ = id. -/
def identityMonad (t : Theory) : MonadData :=
  { functor := id
    unit    := gid "η_id"
    mult    := gid "μ_id"
    base    := t }

-- ============================================================
-- ComonadData — identity comonad on a theory
-- ============================================================

def identityComonad (t : Theory) : ComonadData :=
  { functor := id
    counit  := gid "ε_id"
    comult  := gid "δ_id"
    base    := t }

-- ============================================================
-- OreData — trivial (empty fraction class) and group (all morphisms)
-- ============================================================

/-- No fractions selected — trivial localization that changes nothing. -/
def oreEmpty (t : Theory) : OreData :=
  { theory := t, rightFractions := [] }

/-- All morphisms as fractions — suitable for group-like theories. -/
def oreAll (t : Theory) : OreData :=
  { theory := t, rightFractions := t.morphisms.map (·.id) }

-- ============================================================
-- ExistentialAxiom — trivial existential (bound variable, atom body)
-- ============================================================

/-- Trivial existential: ∃ y, P where P is the first object atom.
    Falls back to a dummy atom when the theory has no objects. -/
def trivialExistential (t : Theory) : ExistentialAxiom :=
  let bodyAtom : Expr := match t.objects.head? with
    | some o => .atom o.id
    | none   => .atom (gid "dummy")
  { name     := gid "ex_trivial"
    boundVar := "y"
    body     := bodyAtom
    context  := [] }

-- ============================================================
-- IndexedCategory — constant fibration: every fiber is the same theory
-- ============================================================

/-- Constant indexed category: every object of `base` indexes a copy of `fiber`. -/
def constantIndexed (base fiber : Theory) : IndexedCategory :=
  { base    := base
    fiber   := fun _ => fiber
    reindex := fun _ => [] }

-- ============================================================
-- TheoryFunctor — identity functor on a theory
-- ============================================================

def identityFunctor (t : Theory) : TheoryFunctor :=
  { name        := s!"Id({t.name})"
    source      := t
    target      := t
    onObjects   := { entries := t.objects.foldl (fun m o =>
                      m.insert o.id (.atom o.id)) {} }
    onMorphisms := { entries := t.morphisms.foldl (fun m f =>
                      m.insert f.id (.atom f.id)) {} } }

-- ============================================================
-- WeakEquivalences — trivial (no morphisms inverted)
-- ============================================================

def trivialWeakEquivalences (t : Theory) : WeakEquivalences :=
  { theory := t, morphisms := [] }

-- ============================================================
-- GrothendieckTopology — trivial topology (maximal coverage: each object covers itself)
-- ============================================================

def trivialTopology : GrothendieckTopology :=
  { covers := fun _ => [] }

-- ============================================================
-- Congruence — trivial (no identifications)
-- ============================================================

def trivialCongruence : Congruence :=
  { equations := [], description := "trivial" }

end CatLab.Tests.Fixtures
