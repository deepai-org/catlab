/-
  CatLab — Inverse Problem Framework Tests

  Exercises computeStructuralDiff, solveInverse, and evaluateAll with
  hand-crafted candidates, mocking what the LLM would propose.

  Test strategy (Step 2 of the build order — no LLM yet):
    - Construct known-correct and known-wrong candidates by hand
    - Verify that the diff correctly identifies what's missing/wrong
    - Verify that solveInverse finds the correct candidate
    - Verify that Timeout fires correctly for the rewriting cycle trap
-/

import Catlab.Tests.TestCore
import Catlab.Core.InverseProblem
import Catlab.Operators.Decategorify

namespace CatLab.Tests.InverseProblem

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- VerificationStatus display and BEq
-- ============================================================

#eval do
  IO.println "\n=== VerificationStatus display ==="
  let s1 : VerificationStatus := .Success
  let s2 : VerificationStatus := .Failed "missing unit"
  let s3 : VerificationStatus := .Timeout 200
  check "Success toString"   ((toString s1) == "✓ Success")
  check "Failed toString"    ((toString s2).startsWith "✗")
  check "Timeout toString"   ((toString s3).startsWith "⏱")
  check "Success BEq self"   (s1 == VerificationStatus.Success)
  check "Failed != Success"  (s2 != VerificationStatus.Success)

-- ============================================================
-- boundedNormalize: no rules → identity
-- ============================================================

#eval do
  IO.println "\n=== boundedNormalize: no rules → identity ==="
  for (name, t) in allLibTheories do
    for m in t.morphisms do
      let (norm, depth) := boundedNormalize [] m.domain 100
      check    s!"no-rules({name},{m.id.name}).unchanged" (norm == m.domain)
      assertEq s!"no-rules({name},{m.id.name}).depth"     depth 0

-- ============================================================
-- boundedNormalize: closed axiom fires
-- ============================================================

#eval do
  IO.println "\n=== boundedNormalize: closed axiom fires ==="
  let f  : GeneratorId := gid "f"  0 .morphism
  let g  : GeneratorId := gid "g"  0 .morphism
  let h  : GeneratorId := gid "h"  0 .morphism
  let lhs : Expr := Expr.comp (Expr.atom f) (Expr.atom g)
  let rhs : Expr := Expr.atom h
  let ax : Generator2 := {
    id        := gid "fg_eq_h" 0 .twoCell
    leftPath  := lhs
    rightPath := rhs }
  let (norm, depth) := boundedNormalize [ax] lhs 10
  check    "closed axiom fires: LHS→RHS" (norm == rhs)
  assertEq "closed axiom depth"          depth 1

-- ============================================================
-- boundedNormalize: quantified axiom skipped (word problem)
-- ============================================================

#eval do
  IO.println "\n=== boundedNormalize: quantified axiom skipped ==="
  let f : GeneratorId := gid "f" 0 .morphism
  let ax : Generator2 := {
    id          := gid "schema" 0 .twoCell
    quantifiers := [{ name := "x", kind := .morphism }]
    leftPath    := Expr.atom f
    rightPath   := Expr.var "x" }
  let (norm, depth) := boundedNormalize [ax] (Expr.atom f) 100
  check    "quantified axiom skipped: unchanged" (norm == Expr.atom f)
  assertEq "quantified axiom skipped: depth"     depth 0

-- ============================================================
-- boundedNormalize: Timeout on cycle
-- ============================================================

#eval do
  IO.println "\n=== boundedNormalize: Timeout on cycle ==="
  -- f → g → f → g ... (two left-to-right axioms create a cycle)
  let f : GeneratorId := gid "f" 0 .morphism
  let g : GeneratorId := gid "g" 0 .morphism
  let ax1 : Generator2 := {
    id := gid "loop1" 0 .twoCell
    leftPath  := Expr.atom f
    rightPath := Expr.atom g }
  let ax2 : Generator2 := {
    id := gid "loop2" 0 .twoCell
    leftPath  := Expr.atom g
    rightPath := Expr.atom f }
  let (_, depth) := boundedNormalize [ax1, ax2] (Expr.atom f) 20
  assertEq "cycle Timeout: depth at limit" depth 20

-- ============================================================
-- computeStructuralDiff: identical theory → verified (all 34)
-- Covers the quantified-axiom fast-path fix:
-- quantified axioms are "directly present" in produced and pass without rewriting
-- ============================================================

#eval do
  IO.println "\n=== computeStructuralDiff: identical theories → verified ==="
  for (name, t) in allLibTheories do
    let result := computeStructuralDiff t t t
    check s!"diff(id/{name}).verified"   result.verified
    check s!"diff(id/{name}).noMissing"  result.missingSignatures.isEmpty
    check s!"diff(id/{name}).noUnmapped" result.unmappedObjects.isEmpty

-- ============================================================
-- computeStructuralDiff: missing morphism detected by shape
-- ============================================================

#eval do
  IO.println "\n=== computeStructuralDiff: missing morphism detected ==="
  let target := TheoryOfMonoids
  let stripped : Theory := { target with
    name      := "StrippedMonoid"
    morphisms := target.morphisms.filter fun m => m.id.name != Name.root "η" }
  let result := computeStructuralDiff stripped stripped target
  check    "missing η: not verified"          (!result.verified)
  assertGe "missing η: missingSignatures ≥ 1" result.missingSignatures.length 1

-- ============================================================
-- computeStructuralDiff: rename survives (structural alias trap)
-- ============================================================

#eval do
  IO.println "\n=== computeStructuralDiff: rename survives ==="
  let target := TheoryOfMonoids
  -- Rename every generator by nesting its name: "M" becomes "M.LLM"
  let ns (n : Name) : Name := Name.nested n "LLM"
  let renamedObjs : List Generator0 := target.objects.map fun (o : Generator0) =>
    let newId : GeneratorId := { name := ns o.id.name, index := o.id.index, kind := o.id.kind }
    ({ id := newId, description := o.description, tags := o.tags } : Generator0)
  let renamedMorphs : List Generator1 := target.morphisms.map fun (m : Generator1) =>
    let newId : GeneratorId := { name := ns m.id.name, index := m.id.index, kind := m.id.kind }
    ({ id := newId, domain := m.domain.mapNames ns, codomain := m.codomain.mapNames ns,
       description := m.description, tags := m.tags } : Generator1)
  let renamed : Theory := { target with
    name      := "RenamedMonoid"
    objects   := renamedObjs
    morphisms := renamedMorphs }
  let result := computeStructuralDiff renamed renamed target
  -- All morphism shapes match by structural position — no missing signatures
  check "rename survives: missingSignatures empty" result.missingSignatures.isEmpty

-- ============================================================
-- computeStructuralDiff: surplus objects detected
-- ============================================================

#eval do
  IO.println "\n=== computeStructuralDiff: surplus objects flagged ==="
  let target := TheoryOfMonoids
  let ghost : Generator0 := { id := gid "Ghost" }
  let bloated : Theory := { target with
    name    := "BloatedMonoid"
    objects := target.objects ++ [ghost] }
  let result := computeStructuralDiff bloated bloated target
  assertGe "surplus object flagged" result.unmappedObjects.length 1

-- ============================================================
-- solveInverse: mock LLM loop — three-candidate search
-- Simulates: Proposal 1 fails, Proposal 2 fails, Proposal 3 succeeds
-- ============================================================

#eval do
  IO.println "\n=== solveInverse: three-candidate mock loop ==="
  let target := TheoryOfMonoids
  let prop1 : Theory := { target with
    name      := "Prop1_NoMul"
    morphisms := target.morphisms.filter fun m => m.id.name != Name.root "μ" }
  let ghost : Generator0 := { id := gid "Ghost" }
  let prop2 : Theory := { target with
    name    := "Prop2_Bloated"
    objects := target.objects ++ [ghost] }
  let prop3 : Theory := { target with name := "Prop3_Correct" }

  let forward : Theory → Option Theory := fun c => some c
  match solveInverse target forward [prop1, prop2, prop3] with
  | none              => throw (IO.userError "[FAIL] solveInverse: no candidate passed")
  | some (winner, r) =>
    check "winner is Prop3"  (winner.name == "Prop3_Correct")
    check "result.verified"  r.verified
    check "status = Success" (r.status == VerificationStatus.Success)

-- ============================================================
-- evaluateAll: structured diffs for all three proposals
-- Verifies that failing results carry actionable diff information
-- ============================================================

#eval do
  IO.println "\n=== evaluateAll: structured diffs for all proposals ==="
  let target := TheoryOfMonoids
  let prop1 : Theory := { target with
    name      := "Prop1_NoMul"
    morphisms := target.morphisms.filter fun m => m.id.name != Name.root "μ" }
  let ghost : Generator0 := { id := gid "Ghost" }
  let prop2 : Theory := { target with
    name    := "Prop2_Bloated"
    objects := target.objects ++ [ghost] }
  let prop3 : Theory := { target with name := "Prop3_Correct" }

  let results := evaluateAll target (fun c => some c) [prop1, prop2, prop3]
  assertEq "3 results" results.length 3

  let r1 := results[0]!
  check    "prop1: not verified"           (!r1.verified)
  assertGe "prop1: has missing signatures" r1.missingSignatures.length 1

  let r2 := results[1]!
  check    "prop2: not verified"           (!r2.verified)
  assertGe "prop2: has unmapped objects"   r2.unmappedObjects.length 1

  let r3 := results[2]!
  check "prop3: verified"            r3.verified
  check "prop3: no missing sigs"     r3.missingSignatures.isEmpty
  check "prop3: no unmapped objects" r3.unmappedObjects.isEmpty

-- ============================================================
-- solveInverse + decategorify: all 34 library theories
-- T is a trivially-correct candidate for decategorify(T) as target
-- ============================================================

#eval do
  IO.println "\n=== solveInverse + decategorify (all 34 theories) ==="
  for (name, t) in allLibTheories do
    let target  := decategorify t .isoClasses
    let forward : Theory → Option Theory := fun c => some (decategorify c .isoClasses)
    match solveInverse target forward [t] with
    | none          => throw (IO.userError s!"[FAIL] decat-inverse({name}): no winner")
    | some (_, res) => check s!"decat-inverse({name}): verified" res.verified

end CatLab.Tests.InverseProblem
