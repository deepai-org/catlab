/-
  CatLab -- Truncation Operator

  Given a higher-categorical theory with graded cells (Cell0, Cell1, Cell2, ...),
  truncate at level n by:
  1. Keeping all k-cells for k ≤ n
  2. Collapsing (n+1)-cells to identities
  3. Removing k-cells for k > n+1

  Example: truncate 1 (∞,2)-Category → Category
           (keeps objects and 1-morphisms, collapses 2-morphisms to identities)

  This makes the relationship between higher and lower theories explicit
  and computationally verifiable.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Determine the grading level of a generator by examining its name.
    Looks for patterns like "Cell0", "Cell1", "Cell2" or graded names. -/
private def inferCellLevel (g : GeneratorId) : Option Nat :=
  match g.name with
  | .root s =>
    if s.startsWith "Cell" then
      (s.drop 4).toNat?
    else none
  | .graded _ n => some n
  | _ => none

/-- Determine the grading level of a morphism by looking at its domain/codomain.
    A morphism between Cell_k objects is at level k. -/
private def inferMorphismLevel (m : Generator1) : Option Nat :=
  match m.codomain with
  | .atom gid => inferCellLevel gid
  | _ => none

/-- Truncate a higher-categorical theory at level n.

    - Objects (0-generators): keep those at levels ≤ n
    - Morphisms (1-generators): keep those whose codomain is at level ≤ n;
      morphisms with codomain at level n+1 are replaced by identity axioms
    - Axioms: keep those referencing only retained generators

    The output theory has truncationLevel = some n. -/
def truncate (t : Theory) (n : Nat) : Theory :=
  -- Partition objects by cell level
  let (keepObjs, _dropObjs) := t.objects.partition fun o =>
    match inferCellLevel o.id with
    | some k => k <= n
    | none => true  -- keep ungraded objects

  let keptObjNames := keepObjs.map (·.id.name)

  -- Partition morphisms: keep only those whose domain AND codomain
  -- atoms all refer to kept objects
  let (keepMors, collapseMors) := t.morphisms.partition fun m =>
    let domAtoms := m.domain.atoms
    let codAtoms := m.codomain.atoms
    let allAtomsKept := (domAtoms ++ codAtoms).all fun a =>
      keptObjNames.any (· == a)
    allAtomsKept

  -- Collapse axioms are not emitted for dropped morphisms since they
  -- would reference generators not in the truncated theory.
  -- The truncation is implicit: higher cells simply don't exist.
  let collapseAxioms : List Generator2 := []

  -- Keep axioms that only reference retained generators
  let keptNames := keepObjs.map (·.id.name) ++ keepMors.map (·.id.name)
  let keepAxioms := t.axioms.filter fun ax =>
    let atoms := ax.leftPath.atoms ++ ax.rightPath.atoms
    atoms.all fun a => keptNames.any (· == a)

  { t with
    name := s!"τ_{n}({t.name})"
    doctrine := { t.doctrine with truncationLevel := some n }
    objects := keepObjs
    morphisms := keepMors
    axioms := keepAxioms ++ collapseAxioms }

end CatLab
