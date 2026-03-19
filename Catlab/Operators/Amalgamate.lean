/-
  CatLab — Amalgamation: Sort Identification

  The missing combinator that unlocks multi-sorted theories from single-sorted ones.

  amalgamateOver t1 t2 identifications
    Merges two theories by identifying named object-sorts:
    - identifications: List (t2SortName × canonicalName)
      For each pair, t2's sort `t2SortName` is fused with `canonicalName` —
      its object is dropped, all morphism domains/codomains and axiom paths
      referring to `t2SortName` are rewritten to `canonicalName`.
    - Non-identified t2 sorts, morphisms, and axioms are all preserved.
    The result has t1's objects plus any unrenamed t2 objects, with all
    structure from both theories.

  renameSort t oldName newName
    Renames an object sort throughout a theory — objects, morphism
    domains/codomains, and axiom paths.

  Derivation examples:
    Ring base = amalgamateOver additiveAbelianGroup TheoryOfMonoids [("M", "R")]
      where additiveAbelianGroup = renameSort(renameGenerator(AbelianGroup,...)) "G" "R"
    Then: TheoryOfRings = addDistributivity ringBase "μ" "add"
-/

import Catlab.Core.Theory

namespace CatLab

-- ============================================================
-- renameSort
-- ============================================================

/-- Rename an object sort throughout a theory.
    Rewrites the sort name in objects, morphism domains/codomains, and axiom paths.
    Does NOT rename morphism/axiom IDs — use `renameGenerator` for that. -/
def renameSort (t : Theory) (oldName newName : Name) : Theory :=
  let f : Name → Name := fun n => if n == oldName then newName else n
  { t with
    objects   := t.objects.map   fun o => { o with id := { o.id with name := f o.id.name } }
    morphisms := t.morphisms.map fun m =>
      { m with domain := m.domain.mapNames f, codomain := m.codomain.mapNames f }
    axioms    := t.axioms.map    fun ax =>
      { ax with leftPath := ax.leftPath.mapNames f, rightPath := ax.rightPath.mapNames f } }

-- ============================================================
-- amalgamateOver
-- ============================================================

/-- Merge two theories by identifying named object-sorts.

    `identifications` is a list of  (t2SortName, canonicalName)  pairs where:
    - `t2SortName` is an object name in `t2`
    - `canonicalName` is the name that will be used in the merged theory
      (usually an existing name in t1, so t2's sort is absorbed into t1's)

    Effect:
    - t2 objects whose name appears in identifications are dropped (absorbed)
    - All references to `t2SortName` in t2's morphisms and axioms are rewritten
      to `canonicalName`
    - t2 objects NOT in identifications are kept (with their names unchanged)
    - All morphisms and axioms from both theories are included in the result

    Use `renameSort` and `renameGenerator` before calling to set up correct
    canonical names.  The result doctrine comes from t1. -/
def amalgamateOver (t1 t2 : Theory) (identifications : List (Name × Name)) : Theory :=
  -- Build rename function for t2 sort references
  let renameT2 : Name → Name := fun n =>
    match identifications.find? (fun (t2Name, _) => n == t2Name) with
    | some (_, canonical) => canonical
    | none                => n
  -- t2 objects that are identified are dropped; others are kept
  let identifiedSorts := identifications.map Prod.fst
  let extraT2Objects := t2.objects.filterMap fun o =>
    if identifiedSorts.any (· == o.id.name) then none
    else some { o with id := { o.id with name := renameT2 o.id.name } }
  -- Rewrite t2 morphisms
  let renamedT2Mors := t2.morphisms.map fun m =>
    { m with
      domain   := m.domain.mapNames renameT2
      codomain := m.codomain.mapNames renameT2 }
  -- Rewrite t2 axioms, prefixing IDs that collide with t1
  let t1AxNames := t1.axioms.map (·.id.name)
  let renamedT2Axs := t2.axioms.map fun ax =>
    let axName := if t1AxNames.any (· == ax.id.name)
      then .nested (.root t2.name) ax.id.name.toString  -- prefix with t2 theory name
      else ax.id.name
    { ax with
      id        := { ax.id with name := axName }
      leftPath  := ax.leftPath.mapNames renameT2
      rightPath := ax.rightPath.mapNames renameT2 }
  { name     := s!"{t1.name}⊕{t2.name}"
    doctrine := t1.doctrine
    objects  := t1.objects ++ extraT2Objects
    morphisms := t1.morphisms ++ renamedT2Mors
    axioms   := t1.axioms ++ renamedT2Axs
    functors := t1.functors ++ t2.functors
    natTrans := t1.natTrans ++ t2.natTrans }

end CatLab
