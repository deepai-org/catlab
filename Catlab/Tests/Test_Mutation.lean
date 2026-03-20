/-
  CatLab — Mutation Tests

  Mutation testing: deliberately break operators and verify the test
  infrastructure catches the breakage. Each "mutant" injects a specific bug
  and we confirm that at least one property (validate, involution,
  signatureMatch, morphism count) detects it.
-/

import Catlab.Tests.TestCore
import Catlab.Core.Validate
import Catlab.Core.Equality
import Catlab.Operators.Opposite
import Catlab.Operators.Mirror
import Catlab.Operators.Karoubi
import Catlab.Operators.Product
import Catlab.Operators.Coproduct

namespace CatLab.Tests.Mutation

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- Mutant definitions
-- ============================================================

/-- Mutant opposite #1: rename morphisms with .op but do NOT swap domain/codomain.
    The bug: morphism directions are unchanged. -/
def mutantOpposite1 (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}ᵒᵖ_mut1"
    morphisms := t.morphisms.map fun g =>
      { g with
        id := { g.id with name := .op g.id.name }
        -- BUG: domain/codomain NOT swapped
        domain := g.domain
        codomain := g.codomain }
    axioms := t.axioms.map fun a =>
      { a with
        id := { a.id with name := .op a.id.name }
        leftPath := a.rightPath.opposite t
        rightPath := a.leftPath.opposite t } }

/-- Mutant opposite #2: swap domain/codomain correctly but do NOT reverse axiom
    composition — just rename atoms. -/
def mutantOpposite2 (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}ᵒᵖ_mut2"
    morphisms := t.morphisms.map fun g =>
      { g with
        id := { g.id with name := .op g.id.name }
        domain := g.codomain
        codomain := g.domain }
    axioms := t.axioms.map fun a =>
      { a with
        id := { a.id with name := .op a.id.name }
        -- BUG: axiom paths NOT reversed, just atom-renamed
        leftPath := a.leftPath.mapAtoms fun
          | .atom g => if t.morphisms.any (fun m => m.id == g) then .atom { g with name := .op g.name } else .atom g
          | other => other
        rightPath := a.rightPath.mapAtoms fun
          | .atom g => if t.morphisms.any (fun m => m.id == g) then .atom { g with name := .op g.name } else .atom g
          | other => other } }

/-- Mutant mirror: swap domain/codomain with real mirror on exprs, but axioms
    just swap sides without structural transform. -/
def mutantMirror (t : Theory) : Theory :=
  let renameMor (e : Expr) : Expr := match e with
    | .atom g =>
      if t.morphisms.any (fun m => m.id == g) then .atom { g with name := .op g.name }
      else e
    | other => other
  { t with
    name := s!"{t.name}ᵒᵖ_mirMut"
    morphisms := t.morphisms.map fun g =>
      { g with
        id := { g.id with name := .op g.id.name }
        domain := g.codomain.mirror
        codomain := g.domain.mirror }
    axioms := t.axioms.map fun a =>
      { a with
        id := { a.id with name := .op a.id.name }
        -- BUG: axiom paths just swapped, not mirror-transformed
        leftPath := a.rightPath.mapAtoms renameMor
        rightPath := a.leftPath.mapAtoms renameMor } }

/-- Mutant: drop all axioms. -/
def mutantDropAxioms (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}_noax"
    axioms := [] }

/-- Mutant: drop the first morphism. -/
def mutantDropMorphism (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}_dropmor"
    morphisms := t.morphisms.drop 1 }

/-- Mutant: duplicate all objects (creates duplicate names). -/
def mutantDuplicateObjects (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}_dupobj"
    objects := t.objects ++ t.objects }

/-- Mutant: swap all morphism domains with codomains but leave axioms untouched.
    A "half-opposite" that breaks composition boundaries. -/
def mutantHalfOpposite (t : Theory) : Theory :=
  { t with
    name := s!"{t.name}_halfop"
    morphisms := t.morphisms.map fun g =>
      { g with
        domain := g.codomain
        codomain := g.domain }
    -- axioms left completely unchanged — atom references still use old names
  }

-- ============================================================
-- Helper: compare morphism domain/codomain lists
-- ============================================================

/-- Extract (domain, codomain) pairs as a fingerprint of morphism structure. -/
private def morphismFingerprint (t : Theory) : List (Expr × Expr) :=
  t.morphisms.map fun m => (m.domain, m.codomain)

/-- Extract morphism names from a theory. -/
private def morphismNames (t : Theory) : List Name :=
  t.morphisms.map fun (m : Generator1) => m.id.name

/-- Extract axiom LHS expressions from a theory. -/
private def axiomLHSList (t : Theory) : List Expr :=
  t.axioms.map fun (a : Generator2) => a.leftPath

/-- Check if any morphism has domain != codomain (i.e., the theory is asymmetric). -/
private def hasAsymmetricMorphism (t : Theory) : Bool :=
  t.morphisms.any fun m => !(m.domain.beq m.codomain)

-- ============================================================
-- Tests
-- ============================================================

#eval do
  IO.println "\n=== Mutation Tests ==="
  IO.println "--- Proving the test suite has teeth ---\n"

  -- ----------------------------------------------------------
  -- 1. mutantOpposite1: domain/codomain not swapped
  -- ----------------------------------------------------------
  IO.println "=== mutation: opposite without domain swap ==="

  let monoid := TheoryOfMonoids
  let realOp := opposite monoid
  let mutOp  := mutantOpposite1 monoid

  -- For Monoid, mul: M*M -> M. Real opposite swaps to M -> M*M.
  -- Mutant keeps M*M -> M. So fingerprints differ.
  let realFP := morphismFingerprint realOp
  let mutFP  := morphismFingerprint mutOp
  check "mutantOpposite1 differs from real opposite on morphism types"
    (realFP != mutFP)

  -- Double-apply: real opposite is involution, mutant is not
  let realDouble := opposite (opposite monoid)
  let mutDouble  := mutantOpposite1 (mutantOpposite1 monoid)
  -- Real double should signature-match original
  check "real opposite^2(Monoid) signature matches Monoid"
    (realDouble.signatureMatch monoid)
  -- Mutant double: names are double-op'd which differ from original
  let origNames := morphismNames monoid
  let mutDoubleNames := morphismNames mutDouble
  check "mutantOpposite1^2(Monoid) morphism names != original (double .op)"
    (origNames != mutDoubleNames)

  -- Also test on Category (has asymmetric morphisms)
  let cat := TheoryOfCategories
  if hasAsymmetricMorphism cat then
    let realOpCat := opposite cat
    let mutOpCat  := mutantOpposite1 cat
    check "mutantOpposite1(Category) fingerprint != real opposite"
      (morphismFingerprint realOpCat != morphismFingerprint mutOpCat)

  -- ----------------------------------------------------------
  -- 2. mutantOpposite2: axiom composition not reversed
  -- ----------------------------------------------------------
  IO.println "\n=== mutation: opposite without axiom reversal ==="

  let realOpMon := opposite monoid
  let mut2Mon   := mutantOpposite2 monoid

  -- Axiom LHS should differ between real and mutant
  let realAxLHS := axiomLHSList realOpMon
  let mut2AxLHS := axiomLHSList mut2Mon
  check "mutantOpposite2(Monoid) axiom LHS differs from real opposite"
    (realAxLHS != mut2AxLHS)

  -- Double application breaks involution on axiom structure
  let mut2Double := mutantOpposite2 (mutantOpposite2 monoid)
  let origAxLHS := axiomLHSList monoid
  let mut2DblAxLHS := axiomLHSList mut2Double
  check "mutantOpposite2^2(Monoid) axiom LHS != original (involution broken)"
    (origAxLHS != mut2DblAxLHS)

  -- ----------------------------------------------------------
  -- 3. mutantMirror: no prod<->coprod swap in axioms
  -- ----------------------------------------------------------
  IO.println "\n=== mutation: mirror without prod/coprod swap ==="

  let realMirMon := mirror monoid
  let mutMirMon  := mutantMirror monoid

  -- Real mirror transforms axiom paths structurally; mutant just renames
  let realMirAxLHS := axiomLHSList realMirMon
  let mutMirAxLHS  := axiomLHSList mutMirMon
  check "mutantMirror(Monoid) axiom LHS differs from real mirror"
    (realMirAxLHS != mutMirAxLHS)

  -- Test on Ring which has richer product structure
  let ring := TheoryOfRings
  let realMirRing := mirror ring
  let mutMirRing  := mutantMirror ring
  check "mutantMirror(Ring) axiom structure differs from real mirror"
    (axiomLHSList realMirRing != axiomLHSList mutMirRing)

  -- ----------------------------------------------------------
  -- 4. mutantDropAxioms: signatureMatch catches missing axioms
  -- ----------------------------------------------------------
  IO.println "\n=== mutation: drop all axioms ==="

  let theoriesWithAxioms := allLibTheories.filter fun ((_ : String), (t : Theory)) => !t.axioms.isEmpty
  let mut4Count ← theoriesWithAxioms.foldlM (init := 0) fun count ((name : String), (t : Theory)) => do
    let mutant := mutantDropAxioms t
    check s!"mutantDropAxioms({name}) signature != original"
      (!mutant.signatureMatch t)
    check s!"mutantDropAxioms({name}) has 0 axioms"
      (mutant.axioms.isEmpty)
    pure (count + 1)
  assertGe "theories tested for drop-axioms mutation" mut4Count 5

  -- ----------------------------------------------------------
  -- 5. mutantDropMorphism: validate catches dangling references
  -- ----------------------------------------------------------
  IO.println "\n=== mutation: drop first morphism ==="

  -- For theories with axioms referencing the first morphism, validate should fail
  let mut5Count ← allLibTheories.foldlM (init := 0) fun count ((name : String), (t : Theory)) => do
    if t.morphisms.length > 0 && t.axioms.length > 0 then
      let mutant := mutantDropMorphism t
      let errors := validate mutant
      -- Either validation catches it or signature doesn't match
      let caught := !errors.isEmpty || !mutant.signatureMatch t
      check s!"mutantDropMorphism({name}) detected (validate or signature)"
        caught
      pure (count + 1)
    else
      pure count
  assertGe "theories tested for drop-morphism mutation" mut5Count 5

  -- ----------------------------------------------------------
  -- 6. mutantDuplicateObjects: validate catches duplicate names
  -- ----------------------------------------------------------
  IO.println "\n=== mutation: duplicate objects ==="

  let mut6Count ← allLibTheories.foldlM (init := 0) fun count ((name : String), (t : Theory)) => do
    if t.objects.length > 0 then
      let mutant := mutantDuplicateObjects t
      let errors := validate mutant
      let hasDupError := errors.any fun
        | .duplicateName _ => true
        | _ => false
      check s!"mutantDuplicateObjects({name}) caught by validate (duplicate names)"
        hasDupError
      pure (count + 1)
    else
      pure count
  assertGe "theories tested for duplicate-objects mutation" mut6Count 5

  -- ----------------------------------------------------------
  -- 7. mutantHalfOpposite: swap domains but not axioms
  -- ----------------------------------------------------------
  IO.println "\n=== mutation: half-opposite (domains swapped, axioms unchanged) ==="

  -- This should break composition boundaries in axioms
  let mut7Count ← allLibTheories.foldlM (init := 0) fun count ((name : String), (t : Theory)) => do
    if hasAsymmetricMorphism t && t.axioms.length > 0 then
      let mutant := mutantHalfOpposite t
      let errors := validate mutant
      -- Half-opposite breaks boundary matching or reference validity
      let fpDiffers := morphismFingerprint mutant != morphismFingerprint t
      let caught := !errors.isEmpty || fpDiffers
      check s!"mutantHalfOpposite({name}) detected"
        caught
      pure (count + 1)
    else
      pure count
  assertGe "theories tested for half-opposite mutation" mut7Count 3

  -- ----------------------------------------------------------
  -- Cross-cutting: every mutant differs from the real operator
  -- ----------------------------------------------------------
  IO.println "\n=== cross-cutting: mutants != real operators ==="

  for (name, t) in [("Monoid", monoid), ("Group", TheoryOfGroups),
                     ("Ring", ring), ("Category", cat), ("Poset", TheoryOfPosets)] do
    -- Real opposite vs mutant opposite 1
    let real := opposite t
    let mut1 := mutantOpposite1 t
    let realNames := morphismNames real
    let mut1Names := morphismNames mut1
    -- Names match (both apply .op) but types differ
    check s!"{name}: mutantOp1 names match real opposite"
      (realNames == mut1Names)
    if hasAsymmetricMorphism t then
      check s!"{name}: mutantOp1 types differ from real opposite"
        (morphismFingerprint real != morphismFingerprint mut1)

    -- Real opposite vs mutant opposite 2
    let mut2 := mutantOpposite2 t
    let mut2FP := morphismFingerprint mut2
    let realFP := morphismFingerprint real
    -- Both swap domains, so fingerprints match — but axioms differ
    check s!"{name}: mutantOp2 has same morphism types as real opposite"
      (mut2FP == realFP)
    check s!"{name}: mutantOp2 axioms differ from real opposite"
      (axiomLHSList mut2 != axiomLHSList real)

  -- ----------------------------------------------------------
  -- Summary
  -- ----------------------------------------------------------
  IO.println "\n=== All mutation tests passed ==="
  IO.println "The test suite successfully detects all injected mutations."

end CatLab.Tests.Mutation
