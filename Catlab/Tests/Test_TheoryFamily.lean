/-
  CatLab — TheoryFamily Tests
-/

import Catlab.Tests.TestCore
import Catlab.Core.Equality
import Catlab.Operators.TheoryFamily
import Catlab.Library.Ring
import Catlab.Library.Module

namespace CatLab.Tests.TheoryFamily

open CatLab CatLab.Tests CatLab.Library

-- ============================================================
-- 1. SyntacticModel: expression substitution
-- ============================================================

#eval do
  IO.println "\n=== theoryFamily: syntactic model substitution ==="
  let base : Theory := {
    name := "Base"
    doctrine := { doctrine := .Category }
    objects := [{ id := gid "A" }]
    morphisms := [{ id := gid "f" 0 .morphism
                    domain := Expr.atom (gid "A")
                    codomain := Expr.atom (gid "A") }]
    axioms := []
  }
  let model : SyntacticModel := {
    theory := base
    onObjects := GeneratorMap.ofList [(gid "A", Expr.atom (gid "ℤ"))]
    onMorphisms := GeneratorMap.ofList [(gid "f" 0 .morphism, Expr.atom (gid "succ" 0 .morphism))]
  }
  let expr := Expr.atom (gid "A")
  let result := model.applyToExpr expr
  check "subst A → ℤ" (result == Expr.atom (gid "ℤ"))
  let pairExpr := Expr.prod (Expr.atom (gid "A")) (Expr.atom (gid "A"))
  let pairResult := model.applyToExpr pairExpr
  check "subst (A×A) → (ℤ×ℤ)" (pairResult == Expr.prod (Expr.atom (gid "ℤ")) (Expr.atom (gid "ℤ")))
  IO.println "  ✓ syntactic model substitution"

-- ============================================================
-- 2. TheoryFamily: generic fiber
-- ============================================================

#eval do
  IO.println "\n=== theoryFamily: generic fiber ==="
  let base : Theory := {
    name := "Carrier"
    doctrine := { doctrine := .Category }
    objects := [{ id := gid "R" }]
    morphisms := []
    axioms := []
  }
  let family : CatLab.TheoryFamily := {
    base := base
    name := "PointedSet"
    fiberOf := fun model =>
      let carrier := model.onObjects.apply (gid "R")
      { name := "Pointed"
        doctrine := { doctrine := .LawvereTheory }
        objects := [{ id := gid "X" }]
        morphisms := [{ id := gid "pt" 0 .morphism
                        domain := carrier
                        codomain := Expr.atom (gid "X") }]
        axioms := [] }
  }
  let generic := family.genericFiber
  check "generic fiber has 1 object" (generic.objects.length == 1)
  check "generic fiber has 1 morphism" (generic.morphisms.length == 1)
  let ptMor := generic.morphisms[0]!
  check "pt domain is R" (ptMor.domain == Expr.atom (gid "R"))
  IO.println "  ✓ generic fiber preserves base references"

-- ============================================================
-- 3. Flatten with concrete model
-- ============================================================

#eval do
  IO.println "\n=== theoryFamily: flatten ==="
  let base : Theory := {
    name := "Carrier"
    doctrine := { doctrine := .Category }
    objects := [{ id := gid "R" }]
    morphisms := []
    axioms := []
  }
  let family : CatLab.TheoryFamily := {
    base := base
    name := "PointedSet"
    fiberOf := fun model =>
      let carrier := model.onObjects.apply (gid "R")
      { name := "Pointed"
        doctrine := { doctrine := .LawvereTheory }
        objects := [{ id := gid "X" }]
        morphisms := [{ id := gid "pt" 0 .morphism
                        domain := carrier
                        codomain := Expr.atom (gid "X") }]
        axioms := [] }
  }
  let model : SyntacticModel := {
    theory := base
    onObjects := GeneratorMap.ofList [(gid "R", Expr.atom (gid "ℤ"))]
    onMorphisms := GeneratorMap.empty
  }
  let flat := family.flatten model
  let ptMor := flat.morphisms[0]!
  check "flattened pt domain is ℤ" (ptMor.domain == Expr.atom (gid "ℤ"))
  IO.println "  ✓ flatten substitutes base generators"

-- ============================================================
-- 4. extractFamily: Module over Ring
-- ============================================================

#eval do
  IO.println "\n=== theoryFamily: extract Module family ==="
  let ring := TheoryOfRings
  let modTheory := TheoryOfModules "R"
  let family := extractFamily ring modTheory "Module"
  let generic := family.genericFiber
  let fiberObjNames := generic.objects.map fun o => toString (Generator0.id o).name
  let fiberMorNames := generic.morphisms.map fun m => toString (Generator1.id m).name
  check "fiber has M" (generic.objects.any fun (o : Generator0) => o.id.name == Name.root "M")
  check "fiber lacks R" (!(generic.objects.any fun (o : Generator0) => o.id.name == Name.root "R"))
  check "fiber has add" (generic.morphisms.any fun (m : Generator1) => m.id.name == Name.root "add")
  check "fiber has smul" (generic.morphisms.any fun (m : Generator1) => m.id.name == Name.root "smul")
  IO.println s!"  fiber objects: {fiberObjNames}"
  IO.println s!"  fiber morphisms: {fiberMorNames}"
  IO.println "  ✓ extractFamily separates base from fiber"

-- ============================================================
-- 5. totalTheory: merge base + fiber
-- ============================================================

#eval do
  IO.println "\n=== theoryFamily: total theory ==="
  let ring := TheoryOfRings
  let modTheory := TheoryOfModules "R"
  let family := extractFamily ring modTheory "Module"
  let total := family.totalTheory
  check "total has R" (total.objects.any fun (o : Generator0) => o.id.name == Name.root "R")
  check "total has M" (total.objects.any fun (o : Generator0) => o.id.name == Name.root "M")
  check "total has mul" (total.morphisms.any fun (m : Generator1) => m.id.name == Name.root "mul")
  check "total has smul" (total.morphisms.any fun (m : Generator1) => m.id.name == Name.root "smul")
  IO.println s!"  total: {total.objects.length} objects, {total.morphisms.length} morphisms, {total.axioms.length} axioms"
  IO.println "  ✓ totalTheory merges base and fiber"

-- ============================================================
-- 6. Instantiate ℤ-Module
-- ============================================================

#eval do
  IO.println "\n=== theoryFamily: instantiate ℤ-Module ==="
  let ring := TheoryOfRings
  let modTheory := TheoryOfModules "R"
  let family := extractFamily ring modTheory "Module"
  let model : SyntacticModel := {
    theory := ring
    onObjects := GeneratorMap.ofList [(gid "R", Expr.atom (gid "ℤ"))]
    onMorphisms := GeneratorMap.ofList [
      (gid "add" 0 .morphism, Expr.atom (gid "int_add" 0 .morphism)),
      (gid "mul" 0 .morphism, Expr.atom (gid "int_mul" 0 .morphism)),
      (gid "zero" 0 .morphism, Expr.atom (gid "int_zero" 0 .morphism)),
      (gid "one" 0 .morphism, Expr.atom (gid "int_one" 0 .morphism)),
      (gid "neg" 0 .morphism, Expr.atom (gid "int_neg" 0 .morphism))
    ]
  }
  let intMod := family.instantiate "ℤ" model
  check "name is Module(ℤ)" (intMod.name == "Module(ℤ)")
  let smulOpt := intMod.morphisms.find? fun (m : Generator1) => m.id.name == Name.root "smul"
  match smulOpt with
  | some smul =>
    let domAtoms := smul.domain.atoms
    check "smul domain references ℤ" (domAtoms.any (· == Name.root "ℤ"))
    check "smul domain no R" (!(domAtoms.any (· == Name.root "R")))
    IO.println s!"  smul domain: {smul.domain.toName}"
  | none => IO.println "  ✗ smul not found"
  IO.println s!"  {intMod.name}: {intMod.objects.length} objects, {intMod.morphisms.length} morphisms"
  IO.println "  ✓ ℤ-Module instantiated correctly"

end CatLab.Tests.TheoryFamily
