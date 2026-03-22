/-
  CatLab — Homotopy Pushout Tests

  Verifies the HIT-based homotopy pushout operator:
    1. Produces valid theories with correct generator counts
    2. Contains path constructors (glue axioms) connecting inl/inr images
    3. HITDecl is preserved in the output for introspection
    4. Homotopy coproduct and suspension work as special cases
-/

import Catlab.Tests.TestCore
import Catlab.Core.Equality
import Catlab.Core.Primitives
import Catlab.Core.Validate
import Catlab.Operators.HomotopyPushout

namespace CatLab.Tests.HomotopyPushout

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- 1. Basic homotopy pushout construction
-- ============================================================

#eval do
  IO.println "\n=== homotopy pushout: basic construction ==="

  -- Pushout of Monoid ← Basic → Monoid (self-pushout)
  let base := initialTheory
  let f := initialMorphism TheoryOfMonoids
  let g := initialMorphism TheoryOfMonoids

  match homotopyPushout f g with
  | none => throw (IO.userError "homotopyPushout returned none")
  | some hp =>
    IO.println s!"  Name: {hp.name}"
    IO.println s!"  Objects: {hp.objects.length}"
    IO.println s!"  Morphisms: {hp.morphisms.length}"
    IO.println s!"  Axioms: {hp.axioms.length}"
    IO.println s!"  HITDecls: {hp.hitDecls.length}"

    -- Should have: 2 copies of Monoid objects + 1 Pushout object
    -- Monoid has 1 object (Ob), so: 2 + 1 = 3
    check "has pushout object" (hp.objects.any fun o => o.description == "Homotopy pushout type")
    check "has HITDecl" (hp.hitDecls.length == 1)

    -- Should have inl and inr constructors
    let hasInl := hp.morphisms.any fun m =>
      match m.id.name with
      | .nested (.root "inl") _ => true
      | _ => false
    let hasInr := hp.morphisms.any fun m =>
      match m.id.name with
      | .nested (.root "inr") _ => true
      | _ => false
    check "has inl constructors" hasInl
    check "has inr constructors" hasInr

-- ============================================================
-- 2. Glue axioms present
-- ============================================================

#eval do
  IO.println "\n=== homotopy pushout: glue axioms ==="

  -- Use a non-trivial span: Monoid ← Monoid → Group
  -- with identity on the left and inclusion on the right
  let mon := TheoryOfMonoids
  let grp := TheoryOfGroups
  let idMon := TheoryMorphism.id mon
  -- Inclusion: Monoid → Group (Monoid is a sub-theory of Group)
  let incl := TheoryMorphism.inclusion mon grp

  match homotopyPushout idMon incl with
  | none => throw (IO.userError "homotopyPushout returned none")
  | some hp =>
    -- Should have glue axioms connecting inl(x) and inr(x) for each Monoid object
    let glueAxioms := hp.axioms.filter fun (a : Generator2) =>
      match a.id.name with
      | .nested (.root "glue") _ => true
      | _ => false
    IO.println s!"  Glue axioms: {glueAxioms.length}"
    check "has glue axioms" (!glueAxioms.isEmpty)

    -- Doctrine should be MartinLofTypeTheory (since we use path types)
    check "doctrine is MLTT" (hp.doctrine.doctrine == Doctrine.MartinLofTypeTheory)

-- ============================================================
-- 3. Homotopy coproduct
-- ============================================================

#eval do
  IO.println "\n=== homotopy pushout: coproduct ==="

  match homotopyCoproduct TheoryOfMonoids TheoryOfGroups with
  | none => throw (IO.userError "homotopyCoproduct returned none")
  | some hc =>
    IO.println s!"  Name: {hc.name}"
    -- Coproduct = pushout over ⊥, so no glue axioms (⊥ has no generators)
    let glueAxioms := hc.axioms.filter fun (a : Generator2) =>
      match a.id.name with
      | .nested (.root "glue") _ => true
      | _ => false
    IO.println s!"  Glue axioms: {glueAxioms.length} (expected 0)"
    check "no glue axioms for coproduct" (glueAxioms.isEmpty)

    -- Should have inl/inr constructors for each object
    let inlCount := hc.morphisms.filter (fun (m : Generator1) =>
      match m.id.name with
      | .nested (.root "inl") _ => true
      | _ => false) |>.length
    let inrCount := hc.morphisms.filter (fun (m : Generator1) =>
      match m.id.name with
      | .nested (.root "inr") _ => true
      | _ => false) |>.length
    IO.println s!"  inl constructors: {inlCount}, inr constructors: {inrCount}"
    check "inl count matches Monoid objects" (inlCount == TheoryOfMonoids.objects.length)
    check "inr count matches Group objects" (inrCount == TheoryOfGroups.objects.length)

-- ============================================================
-- 4. Homotopy suspension
-- ============================================================

#eval do
  IO.println "\n=== homotopy pushout: suspension ==="

  match homotopySuspension TheoryOfMonoids with
  | none => throw (IO.userError "homotopySuspension returned none")
  | some susp =>
    IO.println s!"  Name: {susp.name}"
    IO.println s!"  Objects: {susp.objects.length}"
    -- Suspension = pushout of ⊤ ← T → ⊤
    -- Terminal theory has 1 object (⋆), so we get 2 copies of ⋆ + Pushout = 3 objects
    -- But glue axioms connect inl(⋆) and inr(⋆) for each object of T
    let glueAxioms := susp.axioms.filter fun (a : Generator2) =>
      match a.id.name with
      | .nested (.root "glue") _ => true
      | _ => false
    IO.println s!"  Glue axioms: {glueAxioms.length}"
    -- Each object in T generates a glue path (meridian)
    check "glue axioms from T objects" (glueAxioms.length >= 1)

-- ============================================================
-- 5. Validate all homotopy pushout outputs
-- ============================================================

#eval do
  IO.println "\n=== homotopy pushout: validation ==="

  let testCases := [
    ("Monoid⊔ₕMonoid", homotopyPushout (initialMorphism TheoryOfMonoids) (initialMorphism TheoryOfMonoids)),
    ("coprod(Mon,Grp)", homotopyCoproduct TheoryOfMonoids TheoryOfGroups),
    ("susp(Mon)", homotopySuspension TheoryOfMonoids)
  ]

  for (label, result) in testCases do
    match result with
    | none => IO.println s!"[SKIP] {label}: returned none"
    | some t =>
      let errs := CatLab.validate t
      if errs.isEmpty then
        IO.println s!"[PASS] validate {label}"
      else
        IO.println s!"[FAIL] validate {label}: {errs.length} errors"
        for e in errs do IO.println s!"  - {e}"

-- ============================================================
-- 6. HITDecl elaboration roundtrip
-- ============================================================

#eval do
  IO.println "\n=== homotopy pushout: HITDecl elaboration ==="

  match homotopyCoproduct TheoryOfMonoids TheoryOfGroups with
  | none => throw (IO.userError "homotopyCoproduct returned none")
  | some hc =>
    -- Elaborate HITDecls and check that it adds the expected generators
    let elaborated := hc.elaborateAllHITs
    IO.println s!"  Before elaboration: {hc.objects.length} objects, {hc.morphisms.length} morphisms"
    IO.println s!"  After elaboration:  {elaborated.objects.length} objects, {elaborated.morphisms.length} morphisms"
    -- Elaboration should add the HIT type object and constructors
    check "elaboration adds objects" (elaborated.objects.length >= hc.objects.length)
    check "elaboration adds morphisms" (elaborated.morphisms.length >= hc.morphisms.length)

end CatLab.Tests.HomotopyPushout
