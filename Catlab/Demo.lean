/-
  CatLab -- Demonstrations

  Runnable examples showing the CAS in action.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Catlab.Core.Validate
import Catlab.Core.PrettyPrint
import Catlab.Core.Pipeline
import Catlab.Operators.Mirror
import Catlab.Operators.DayConvolution
import Catlab.Operators.Limits
import Catlab.Operators.Decategorify
import Catlab.Library.Monoid
import Catlab.Library.Group
import Catlab.Library.Ring
import Catlab.Library.BooleanAlgebra
import Catlab.Library.Basic

namespace CatLab.Demo

open CatLab.Library

-- ============================================================
-- Example A: Tensor(Monoids, AbelianGroups) → Rings
-- ============================================================

def exampleA : Theory := tensorTheories TheoryOfMonoids TheoryOfAbelianGroups

#eval do
  let t := exampleA
  IO.println s!"=== Example A: Tensor Product of Theories ==="
  IO.println s!"Input:  {TheoryOfMonoids.name} ⊗ {TheoryOfAbelianGroups.name}"
  IO.println s!"Output: {t.name}"
  IO.println s!"  Objects:   {t.objects.length}"
  IO.println s!"  Morphisms: {t.morphisms.length}"
  IO.println s!"  Axioms:    {t.axioms.length}"
  IO.println ""
  IO.println "Morphisms:"
  for mor in t.morphisms do
    IO.println s!"  • {mor.pp}"
  IO.println ""
  IO.println "Interchange axioms (Eckmann-Hilton):"
  for ax in t.axioms.filter (fun (a : Generator2) =>
    match a.id.name with
    | .root s => s.startsWith "interchange"
    | .nested (.root "interchange") _ => true
    | _ => false) do
    IO.println s!"  • {ax.pp}"

-- ============================================================
-- Example B: Mirror(BooleanAlgebra) → Stone Spaces
-- ============================================================

#eval do
  let t := mirror Library.TheoryOfBooleanAlgebra
  IO.println s!"\n=== Example B: Stone Duality ==="
  IO.println s!"Input:  Mirror(BooleanAlgebra)"
  IO.println s!"Output: {t.name}"
  IO.println ""
  IO.println "Key duality transformations:"
  IO.println "  Logic          →  Geometry"
  IO.println "  ∧ (AND)        →  ∧ᵒᵖ (intersection of open sets)"
  IO.println "  ∨ (OR)         →  ∨ᵒᵖ (union of open sets)"
  IO.println "  ⊤ (TRUE)       →  ⊤ᵒᵖ (empty space, initial object)"
  IO.println "  ⊥ (FALSE)      →  ⊥ᵒᵖ (whole space, terminal object)"
  IO.println ""
  IO.println "Morphisms (arrows reversed):"
  for mor in t.morphisms do
    IO.println s!"  • {mor.pp}"

-- ============================================================
-- Example C: Validation
-- ============================================================

#eval do
  IO.println s!"\n=== Example C: Theory Validation ==="
  IO.println (validationReport TheoryOfMonoids)
  IO.println (validationReport TheoryOfGroups)
  IO.println (validationReport TheoryOfRings)
  IO.println (validationReport TheoryOfCategories)

-- ============================================================
-- Example D: Pretty-printed theories
-- ============================================================

#eval do
  IO.println s!"\n=== Example D: Pretty Printing ==="
  IO.println (TheoryOfMonoids.pp)
  IO.println ""
  IO.println (TheoryOfCategories.pp)

-- ============================================================
-- Example E: Operator Pipeline
-- ============================================================

#eval do
  IO.println s!"\n=== Example E: Operator Pipeline ==="
  let pipeline : Pipeline := [
    .tensor TheoryOfAbelianGroups,  -- Monoid ⊗ AbelianGroup
    .mirror,                         -- then take opposite
    .decategorify .isoClasses        -- then decategorify
  ]
  IO.println (pipelineReport TheoryOfMonoids pipeline true)

-- ============================================================
-- Example F: Theory isomorphism checking
-- ============================================================

#eval do
  IO.println s!"\n=== Example F: Isomorphism Checking ==="
  -- Signature comparison
  let tensorResult := tensorTheories TheoryOfMonoids TheoryOfAbelianGroups
  IO.println s!"Tensor(Monoid, AbelianGroup) signature matches Ring?"
  IO.println s!"  Tensor:  {tensorResult.objects.length} obj, {tensorResult.morphisms.length} mor, {tensorResult.axioms.length} ax"
  IO.println s!"  Ring:    {TheoryOfRings.objects.length} obj, {TheoryOfRings.morphisms.length} mor, {TheoryOfRings.axioms.length} ax"
  IO.println s!"  Signature match: {tensorResult.signatureMatch TheoryOfRings}"
  IO.println ""
  -- Mirror involution
  let boolOp := mirror Library.TheoryOfBooleanAlgebra
  let boolOpOp := mirror boolOp
  IO.println s!"Mirror(Mirror(BooleanAlgebra)) signature matches BooleanAlgebra?"
  IO.println s!"  Match: {boolOpOp.signatureMatch Library.TheoryOfBooleanAlgebra}"

-- ============================================================
-- Example G: Pullback + Pushout
-- ============================================================

#eval do
  IO.println s!"\n=== Example G: Universal Constructions ==="
  let f : Generator1 := { id := gid "f", domain := .atom (gid "A"), codomain := .atom (gid "C") }
  let g : Generator1 := { id := gid "g", domain := .atom (gid "B"), codomain := .atom (gid "C") }
  let pb := computePullback f g
  IO.println s!"Pullback of f : A → C and g : B → C"
  IO.println s!"  Object: {pb.object.id.name}"
  for mor in pb.morphisms do IO.println s!"  {mor.pp}"
  for ax in pb.axioms do IO.println s!"  {ax.pp}"
  IO.println ""
  let po := computePushout f g
  IO.println s!"Pushout of f : A → C and g : B → C"
  IO.println s!"  Object: {po.object.id.name}"
  for mor in po.morphisms do IO.println s!"  {mor.pp}"
  for ax in po.axioms do IO.println s!"  {ax.pp}"

end CatLab.Demo
