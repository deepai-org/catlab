/-
  CatLab — Roundtrip & Morphism Law Tests

  Tests JSON serialization roundtrips for Expr, Doctrine, and Theory,
  plus basic TheoryMorphism composition laws.
-/

import Catlab.Tests.TestCore
import Catlab.Repl.Protocol
import Catlab.Core.Equality
import Catlab.Operators.Opposite
import Catlab.Operators.Mirror
import Catlab.Operators.Karoubi
import Catlab.Operators.Morita

namespace CatLab.Tests

open CatLab
open CatLab.Repl
open CatLab.Library

-- ============================================================
-- 1. Expr JSON roundtrip (JSON-level stability)
-- ============================================================

/-- Test that exprToJson → exprFromJson → exprToJson produces the same JSON string. -/
private def exprJsonRoundtrip (label : String) (e : Expr) : IO Unit := do
  let j1 := exprToJson e
  match exprFromJson j1 with
  | .error msg => throw (IO.userError s!"[FAIL] Expr roundtrip {label}: parse error: {msg}")
  | .ok e' =>
    let j2 := exprToJson e'
    assertEq s!"Expr roundtrip {label}" j2.compress j1.compress

#eval do
  IO.println "── Expr JSON roundtrip ──"
  let x := Expr.atom (gid "X" 0 .sort)
  let y := Expr.atom (gid "Y" 0 .sort)
  let f := Expr.atom (gid "f" 0 .morphism)
  let g := Expr.atom (gid "g" 0 .morphism)

  exprJsonRoundtrip "atom" x
  exprJsonRoundtrip "unit" .unit
  exprJsonRoundtrip "terminal" .terminal
  exprJsonRoundtrip "initial" .initial
  exprJsonRoundtrip "comp" (.comp f g)
  exprJsonRoundtrip "prod" (.prod x y)
  exprJsonRoundtrip "coprod" (.coprod x y)
  exprJsonRoundtrip "hom" (.hom x y)
  exprJsonRoundtrip "tensor" (.tensor x y)
  exprJsonRoundtrip "id" (.id x)
  -- Nested expressions
  let a := Expr.atom (gid "a" 0 .sort)
  let b := Expr.atom (gid "b" 0 .sort)
  let c := Expr.atom (gid "c" 0 .sort)
  exprJsonRoundtrip "nested comp" (.comp (.comp f g) f)
  exprJsonRoundtrip "nested prod-tensor" (.prod (.tensor a b) c)
  exprJsonRoundtrip "id of comp" (.id (.comp f g))
  exprJsonRoundtrip "comp of id" (.comp (.id x) f)

-- ============================================================
-- 2. Doctrine roundtrip
-- ============================================================

private def allDoctrines : List Doctrine :=
  [ .Category, .CartesianCategory, .CartesianClosed
  , .MonoidalCategory, .BraidedMonoidal, .SymmetricMonoidal
  , .SymmetricMonoidalClosed, .FinitelyComplete, .FinitelyCocomplete
  , .Abelian, .Topos, .GrothendieckTopos, .LawvereTheory
  , .StableCategory, .ElementaryTopos, .MartinLofTypeTheory
  , .PresentableInfinityCategory, .ModelCategory, .Derivator
  , .InfinityNCategory, .Operad, .CubicalTypeTheory
  , .LinearLogic, .GeometricLogic, .CohesiveHomotopyTypeTheory
  , .EnrichedCategory, .TriangulatedCategory, .Locale
  , .DifferentialGraded ]

#eval do
  IO.println "── Doctrine roundtrip ──"
  for d in allDoctrines do
    let s := doctrineToStr d
    match doctrineFromStr s with
    | .ok d' => assertEq s!"Doctrine roundtrip {s}" (d' == d) true
    | .error msg => throw (IO.userError s!"[FAIL] Doctrine roundtrip {s}: {msg}")
  IO.println s!"[PASS] All {allDoctrines.length} doctrine roundtrips"

-- ============================================================
-- 3. Theory JSON roundtrip for all library theories
-- ============================================================

private def theoryJsonRoundtrip (label : String) (t : Theory) : IO Unit := do
  let j := theoryToJson t
  match theoryFromJson j with
  | .error msg => throw (IO.userError s!"[FAIL] Theory roundtrip {label}: {msg}")
  | .ok t' => do
    assertEq s!"Theory roundtrip {label} name" t'.name t.name
    assertEq s!"Theory roundtrip {label} #objects" t'.objects.length t.objects.length
    assertEq s!"Theory roundtrip {label} #morphisms" t'.morphisms.length t.morphisms.length
    assertEq s!"Theory roundtrip {label} #axioms" t'.axioms.length t.axioms.length
    -- Check second roundtrip is stable (idempotent on JSON level)
    let j' := theoryToJson t'
    match theoryFromJson j' with
    | .error msg => throw (IO.userError s!"[FAIL] Theory roundtrip² {label}: {msg}")
    | .ok t'' =>
      let j'' := theoryToJson t''
      assertEq s!"Theory roundtrip² {label} JSON stable" j''.compress j'.compress

#eval do
  IO.println "── Theory JSON roundtrip (all library theories) ──"
  for (name, t) in allLibTheories do
    theoryJsonRoundtrip name t
  IO.println s!"[PASS] All {allLibTheories.length} theory roundtrips"

-- ============================================================
-- 4. Theory JSON roundtrip for operator outputs
-- ============================================================

#eval do
  IO.println "── Theory JSON roundtrip (operator outputs) ──"
  theoryJsonRoundtrip "opposite(Monoid)" (opposite TheoryOfMonoids)
  theoryJsonRoundtrip "mirror(Category)" (mirror TheoryOfCategories)
  theoryJsonRoundtrip "karoubi(Monoid)" (karoubiEnvelope TheoryOfMonoids)

-- ============================================================
-- 5. TheoryMorphism identity: preservesTyping
-- ============================================================

#eval do
  IO.println "── TheoryMorphism identity ──"
  for (name, t) in allLibTheories do
    let m := TheoryMorphism.id t
    assertEq s!"id({name}).source.name" m.source.name t.name
    assertEq s!"id({name}).target.name" m.target.name t.name
    -- Identity morphism should preserve typing
    check s!"id({name}).preservesTyping" m.preservesTyping
  IO.println s!"[PASS] All {allLibTheories.length} identity morphisms"

-- ============================================================
-- 6. TheoryMorphism composition: id ∘ f == f, f ∘ id == f
-- ============================================================

#eval do
  IO.println "── TheoryMorphism composition laws ──"
  let f := TheoryMorphism.inclusion TheoryOfMonoids TheoryOfGroups
  let idMon := TheoryMorphism.id TheoryOfMonoids
  let idGrp := TheoryMorphism.id TheoryOfGroups

  -- id ∘ f should have same source as f
  let lComp := TheoryMorphism.comp idMon f
  assertEq "comp(id(Mon), incl).source" lComp.source.name f.source.name
  assertEq "comp(id(Mon), incl).target" lComp.target.name f.target.name

  -- f ∘ id should have same target as f
  let rComp := TheoryMorphism.comp f idGrp
  assertEq "comp(incl, id(Grp)).source" rComp.source.name f.source.name
  assertEq "comp(incl, id(Grp)).target" rComp.target.name f.target.name

-- ============================================================
-- 7. Inclusion self-inclusion
-- ============================================================

#eval do
  IO.println "── Self-inclusion ──"
  for (name, t) in allLibTheories do
    let inc := TheoryMorphism.inclusion t t
    assertEq s!"inclusion({name},{name}).source" inc.source.name t.name
    assertEq s!"inclusion({name},{name}).target" inc.target.name t.name
  IO.println s!"[PASS] All {allLibTheories.length} self-inclusions"

-- ============================================================
-- 8. signatureMatch is reflexive
-- ============================================================

#eval do
  IO.println "── signatureMatch reflexive ──"
  for (name, t) in allLibTheories do
    check s!"sigMatch({name},{name})" (Theory.signatureMatch t t)
  IO.println s!"[PASS] All {allLibTheories.length} reflexive signature matches"

-- ============================================================
-- 9. signatureMatch detects differences
-- ============================================================

#eval do
  IO.println "── signatureMatch detects differences ──"
  check "sigMatch(Monoid,Category)=false"
    (!Theory.signatureMatch TheoryOfMonoids TheoryOfCategories)
  check "sigMatch(Poset,Ring)=false"
    (!Theory.signatureMatch TheoryOfPosets TheoryOfRings)
  check "sigMatch(Group,Lattice)=false"
    (!Theory.signatureMatch TheoryOfGroups TheoryOfLattices)

end CatLab.Tests
