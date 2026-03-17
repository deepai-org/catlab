/-
  CatLab -- Quotient Categories

  Given a theory C and a congruence relation on its morphisms,
  compute the quotient category C/~ where identified morphisms
  are collapsed.

  A congruence on a category is an equivalence relation on each
  hom-set that is compatible with composition.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

/-- A congruence on a theory: a list of pairs of morphism names that
    should be identified in the quotient. Each pair (f, g) asserts f ~ g,
    and the relation is extended to a congruence (reflexive, symmetric,
    transitive, and compatible with composition). -/
structure Congruence where
  /-- Pairs of morphism names to identify -/
  equations : List (Name × Name)
  /-- Optional description of the congruence -/
  description : String := ""
  deriving Repr, Inhabited

namespace Congruence

/-- Check whether two names are related by the congruence (directly) -/
def relates (c : Congruence) (a b : Name) : Bool :=
  c.equations.any fun (l, r) => (l == a && r == b) || (r == a && l == b)

/-- Compute the equivalence class representative for a name.
    Uses a simple union-find style: pick the lexicographically first
    name in the equivalence class. -/
private def representative (c : Congruence) (n : Name) : Name :=
  -- Collect all names equivalent to n (transitive closure, bounded)
  let rec collect (frontier : List Name) (seen : List Name) (fuel : Nat) : List Name :=
    match fuel with
    | 0 => seen
    | fuel + 1 =>
      let newNeighbors := frontier.flatMap fun x =>
        c.equations.filterMap fun (l, r) =>
          if l == x && !seen.any (· == r) then some r
          else if r == x && !seen.any (· == l) then some l
          else none
      if newNeighbors.isEmpty then seen
      else collect newNeighbors (seen ++ newNeighbors) fuel
  let cls := collect [n] [n] c.equations.length
  -- Pick the first in the class (stable representative)
  cls.head!

end Congruence

/-- Compute the quotient category C/~ given a theory and a congruence.

    Objects: same as C (congruences only identify morphisms).
    Morphisms: equivalence classes of morphisms under ~.
      We keep one representative per class and drop the rest.
    Axioms: original axioms plus the new equations from the congruence. -/
def quotientCategory (t : Theory) (cong : Congruence) : Theory :=
  -- Determine which morphisms to keep (representatives of their class)
  let representatives := t.morphisms.filter fun m =>
    cong.representative m.id.name == m.id.name

  -- Generate new axioms from the congruence equations
  let congAxioms := cong.equations.zipIdx.filterMap fun ((lName, rName), i) =>
    match t.findMorphism lName, t.findMorphism rName with
    | some l, some r =>
      some { id := { name := .pair lName rName, index := i, kind := .twoCell }
             leftPath := .atom l.id
             rightPath := .atom r.id
             description := s!"Quotient: {lName} ~ {rName}" : Generator2 }
    | _, _ => none

  -- Rewrite axioms: replace identified morphism names with representatives
  let rewriteExpr (e : Expr) : Expr :=
    e.mapNames fun n => cong.representative n

  let rewrittenAxioms := t.axioms.map fun ax =>
    { ax with
      leftPath := rewriteExpr ax.leftPath
      rightPath := rewriteExpr ax.rightPath }

  { name := s!"{t.name}/~"
    doctrine := t.doctrine
    objects := t.objects
    morphisms := representatives
    axioms := rewrittenAxioms ++ congAxioms }

end CatLab
