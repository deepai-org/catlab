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

/-- A purely functional Union-Find structure over categorical Names. -/
structure UnionFind where
  parent : List (Name × Name)
  rank : List (Name × Nat)
  deriving Repr, Inhabited

namespace UnionFind

def empty : UnionFind := ⟨[], []⟩

/-- Find the representative of a Name. -/
partial def find (uf : UnionFind) (x : Name) : Name :=
  match uf.parent.lookup x with
  | some p =>
    if p == x then x
    else uf.find p
  | none => x

/-- Union two equivalence classes, using union-by-rank. -/
def union (uf : UnionFind) (x y : Name) : UnionFind :=
  let rootX := uf.find x
  let rootY := uf.find y
  if rootX == rootY then uf
  else
    let rankX := uf.rank.lookup rootX |>.getD 0
    let rankY := uf.rank.lookup rootY |>.getD 0
    if rankX < rankY then
      { uf with parent := (rootX, rootY) :: uf.parent }
    else if rankX > rankY then
      { uf with parent := (rootY, rootX) :: uf.parent }
    else
      { parent := (rootY, rootX) :: uf.parent,
        rank := (rootX, rankX + 1) :: uf.rank }

end UnionFind

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

/-- Compile the list of equations into a Union-Find structure. -/
def compile (c : Congruence) : UnionFind :=
  c.equations.foldl (fun uf (lhs, rhs) => uf.union lhs rhs) UnionFind.empty

/-- Get the stable equivalence class representative for a name. -/
def representative (c : Congruence) (n : Name) : Name :=
  c.compile.find n

end Congruence

/-- Compute the quotient category C/~ given a theory and a congruence.

    Objects: same as C (congruences only identify morphisms).
    Morphisms: equivalence classes of morphisms under ~.
      We keep one representative per class and drop the rest.
    Axioms: original axioms plus the new equations from the congruence. -/
def quotientCategory (t : Theory) (cong : Congruence) : Theory :=
  -- Build the Union-Find once, then use it for all lookups
  let uf := cong.compile
  let rep (n : Name) : Name := uf.find n

  -- Determine which morphisms to keep (representatives of their class)
  let representatives := t.morphisms.filter fun m =>
    rep m.id.name == m.id.name

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
    e.mapNames fun n => rep n

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
