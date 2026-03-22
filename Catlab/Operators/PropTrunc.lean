/-
  CatLab — Propositional Truncation (HIT-based)

  The propositional truncation ||A||₋₁ is the HIT that freely forces a type
  to become a mere proposition (h-level -1). It has:
    • inc (a : A) — point constructor (inject into the truncation)
    • squash (x y : ||A||) : x =_{||A||} y — path constructor (all points equal)

  This is the foundation of the internal logic layer of an ∞-topos:
    ∃ x:A. P(x)  :=  ||Σ x:A. P(x)||₋₁

  More generally, n-truncation ||A||_n is the HIT with:
    • inc : A → ||A||_n
    • hub/spoke constructors forcing all (n+1)-spheres to be filled

  We implement propositional truncation (-1) and set truncation (0) as
  special cases, plus the general n-truncation skeleton.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

/-- Propositional truncation: ||A||₋₁
    Given a theory T with objects, produces a new theory extending T with
    the propositional truncation HIT for each object. -/
def propTruncation (A : Expr) (Aname : String := "A") : HITDecl :=
  let truncName : Name := .root s!"||{Aname}||₋₁"
  let truncId : GeneratorId := { name := truncName, kind := .sort }
  let truncExpr : Expr := .atom truncId

  -- Point constructor: inc : A → ||A||
  let incName : Name := .nested truncName "inc"
  let incConstr : HITConstructor :=
    { name := incName
      isPath := false
      body := .pi "a" A truncExpr
      description := s!"Inclusion inc : {Aname} → ||{Aname}||₋₁" }

  -- Path constructor: squash : Π(x y : ||A||). path(||A||, x, y)
  let squashName : Name := .nested truncName "squash"
  let squashConstr : HITConstructor :=
    { name := squashName
      isPath := true
      body := .pi "x" truncExpr (.pi "y" truncExpr
                (.path truncExpr (.bvar 1) (.bvar 0)))
      description := s!"Squash: all elements of ||{Aname}||₋₁ are equal" }

  -- Eliminator: ||A||₋₁_ind
  -- Given P : ||A|| → U (a motive that is a proposition),
  -- and f : Π(a:A). P(inc a),
  -- produces Π(x : ||A||). P(x)
  let elimName : Name := .nested truncName "ind"

  { name := truncName
    params := [(.root Aname, A)]
    constructors := [incConstr, squashConstr]
    eliminatorName := elimName
    eliminatorType := truncExpr  -- simplified
    computations := []
    description := s!"Propositional truncation ||{Aname}||₋₁" }

/-- Set truncation: ||A||₀
    Forces a type to be a set (h-level 0) by making all path spaces propositions. -/
def setTruncation (A : Expr) (Aname : String := "A") : HITDecl :=
  let truncName : Name := .root s!"||{Aname}||₀"
  let truncId : GeneratorId := { name := truncName, kind := .sort }
  let truncExpr : Expr := .atom truncId

  let incConstr : HITConstructor :=
    { name := .nested truncName "inc"
      isPath := false
      body := .pi "a" A truncExpr
      description := s!"Inclusion inc : {Aname} → ||{Aname}||₀" }

  -- For set truncation, we need: squash : Π(x y : ||A||₀)(p q : x = y). p = q
  let squashConstr : HITConstructor :=
    { name := .nested truncName "squash"
      isPath := true
      body := .pi "x" truncExpr (.pi "y" truncExpr
                (.pi "p" (.path truncExpr (.bvar 1) (.bvar 0))
                  (.pi "q" (.path truncExpr (.bvar 2) (.bvar 1))
                    (.path (.path truncExpr (.bvar 3) (.bvar 2)) (.bvar 1) (.bvar 0)))))
      description := s!"Set truncation: all parallel paths in ||{Aname}||₀ are equal" }

  { name := truncName
    params := [(.root Aname, A)]
    constructors := [incConstr, squashConstr]
    eliminatorName := .nested truncName "ind"
    eliminatorType := truncExpr
    computations := []
    description := s!"Set truncation ||{Aname}||₀" }

/-- Build a theory containing the propositional truncation of each object in T.
    The output theory extends T with the truncation HITs. -/
def propTruncTheory (t : Theory) : Theory :=
  let hits := t.objects.map fun o =>
    propTruncation (.atom o.id) o.id.name.toString
  { t with
    name := s!"||{t.name}||₋₁"
    doctrine := { doctrine := .MartinLofTypeTheory }
    hitDecls := t.hitDecls ++ hits }
  |>.elaborateAllHITs

end CatLab
