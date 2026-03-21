/**
 * Integration test: runs the full Lean/Mathlib elaboration pipeline.
 * Requires: `lake exe cache get` (Mathlib oleans downloaded)
 */

import { elaborate, theoryToLean, shouldRouteToRzk } from "../src/lean-elaborator";
import type { TheoryJson } from "../src/types";

const PROJECT_ROOT = "/Users/kevin/Desktop/catlab";
const opts = { projectRoot: PROJECT_ROOT, timeoutMs: 120000, keepFile: true };

async function main() {
  let passed = 0;
  let failed = 0;

  async function test(name: string, fn: () => Promise<void>) {
    try {
      await fn();
      console.log(`  ✓ ${name}`);
      passed++;
    } catch (e: unknown) {
      const msg = e instanceof Error ? e.message : String(e);
      console.log(`  ✗ ${name}: ${msg}`);
      failed++;
    }
  }

  console.log("\n── Lean Elaborator: Integration Tests ──\n");

  // Test 1: Valid category theory — should compile
  await test("Valid category with composable morphisms compiles", async () => {
    const theory: TheoryJson = {
      name: "ValidCategory",
      doctrine: "Category",
      objects: [{ name: "X" }, { name: "Y" }, { name: "Z" }],
      morphisms: [
        { name: "f", domain: "X", codomain: "Y" },
        { name: "g", domain: "Y", codomain: "Z" },
      ],
      axioms: [],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    console.log(`    Diagnostics: ${result.diagnostics}`);
    if (result.status !== "success") {
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  // Test 2: Bad composition — Lean should catch type mismatch
  await test("Invalid composition caught by Lean type checker", async () => {
    const theory: TheoryJson = {
      name: "BadComp",
      doctrine: "Category",
      objects: [{ name: "A" }, { name: "B" }, { name: "D" }],
      morphisms: [
        { name: "f", domain: "A", codomain: "B" },
        { name: "g", domain: "D", codomain: "A" },
      ],
      axioms: [
        {
          name: "bad_comp",
          lhs: { comp: [{ atom: "f" }, { atom: "g" }] },
          rhs: { atom: "f" },
          description: "f ≫ g where cod(f)=B ≠ dom(g)=D",
        },
      ],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    console.log(`    Diagnostics: ${result.diagnostics}`);
    if (result.status !== "semantic_error") {
      throw new Error(`Expected semantic_error, got ${result.status}`);
    }
    // Check that the error is attributed to the right axiom
    const fatalErrors = result.errors.filter(e => e.severity === "fatal");
    if (fatalErrors.length === 0) {
      throw new Error("Expected at least one fatal error");
    }
  });

  // Test 3: Monoidal category context
  await test("Monoidal category context compiles", async () => {
    const theory: TheoryJson = {
      name: "MonoidalTest",
      doctrine: "MonoidalCategory",
      objects: [{ name: "X" }, { name: "Y" }],
      morphisms: [
        { name: "f", domain: "X", codomain: "Y" },
      ],
      axioms: [],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    console.log(`    Diagnostics: ${result.diagnostics}`);
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  // Test 4: CartesianClosed doctrine compiles
  await test("CartesianClosed doctrine compiles", async () => {
    const theory: TheoryJson = {
      name: "CCCTest",
      doctrine: "CartesianClosed",
      objects: [{ name: "A" }, { name: "B" }],
      morphisms: [
        { name: "f", domain: "A", codomain: "B" },
      ],
      axioms: [],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  // Test 5: FinitelyComplete doctrine compiles
  await test("FinitelyComplete doctrine compiles", async () => {
    const theory: TheoryJson = {
      name: "FinLimTest",
      doctrine: "FinitelyComplete",
      objects: [{ name: "X" }, { name: "Y" }],
      morphisms: [
        { name: "f", domain: "X", codomain: "Y" },
      ],
      axioms: [],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  // Test 6: Rzk routing for higher-categorical theories
  await test("Higher-categorical theory routes to Rzk stub", async () => {
    const theory: TheoryJson = {
      name: "HoTTTest",
      doctrine: "CubicalTypeTheory",
      objects: [{ name: "Type" }],
      morphisms: [],
      axioms: [],
    };
    if (!shouldRouteToRzk(theory)) {
      throw new Error("Expected shouldRouteToRzk to return true for CubicalTypeTheory");
    }
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    console.log(`    Diagnostics: ${result.diagnostics}`);
    if (!result.diagnostics.includes("Rzk")) {
      throw new Error("Expected Rzk routing message in diagnostics");
    }
  });

  // Test 7: Name remapping — object named "C" doesn't shadow category type
  await test("Object named C gets remapped to avoid shadowing", async () => {
    const theory: TheoryJson = {
      name: "ShadowTest",
      doctrine: "Category",
      objects: [{ name: "A" }, { name: "C" }],
      morphisms: [
        { name: "f", domain: "A", codomain: "C" },
      ],
      axioms: [],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
    // Verify the generated source uses C₀ not C
    const { source } = theoryToLean(theory);
    if (!source.includes("C₀")) {
      throw new Error("Expected C₀ in generated source for object named C");
    }
  });

  // Test 8: Coproduct expression translation
  await test("Coproduct domain/codomain compiles", async () => {
    const theory: TheoryJson = {
      name: "CoprodTest",
      doctrine: "Category",
      objects: [{ name: "A" }, { name: "B" }, { name: "X" }],
      morphisms: [
        { name: "f", domain: "A", codomain: "X" },
        { name: "g", domain: "B", codomain: "X" },
      ],
      axioms: [],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  // Test 9: Functor category — operator-specialized elaboration
  await test("Functor category operator elaboration compiles", async () => {
    const theory: TheoryJson = {
      name: "FunctorCategory",
      doctrine: "Category",
      objects: [
        { name: "F", description: "Functor F" },
        { name: "G", description: "Functor G" },
        { name: "H", description: "Functor H" },
      ],
      morphisms: [
        { name: "α", domain: "F", codomain: "G", description: "Natural transformation" },
        { name: "β", domain: "G", codomain: "H", description: "Natural transformation" },
      ],
      axioms: [
        { name: "naturality_α", lhs: { comp: [{ atom: "α" }, { atom: "G" }] }, rhs: { comp: [{ atom: "F" }, { atom: "α" }] }, description: "Naturality of α" },
        { name: "vcomp", lhs: { atom: "βα" }, rhs: { comp: [{ atom: "α" }, { atom: "β" }] }, description: "Vertical composition" },
      ],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    if (result.leanSource) {
      // Verify it used the specialized functor category elaboration
      if (!result.leanSource.includes("C ⥤ D")) {
        throw new Error("Expected specialized functor category elaboration with C ⥤ D");
      }
      if (!result.leanSource.includes("α.naturality")) {
        throw new Error("Expected naturality proof in generated source");
      }
    }
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  // Test 10: Grothendieck construction — operator-specialized elaboration
  await test("Grothendieck construction operator elaboration compiles", async () => {
    const theory: TheoryJson = {
      name: "Grothendieck_F",
      doctrine: "Category",
      objects: [
        { name: "(X, x)", description: "Total object" },
        { name: "(Y, y)", description: "Total object" },
      ],
      morphisms: [
        { name: "π", domain: "(X, x)", codomain: "X", description: "Projection" },
      ],
      axioms: [
        { name: "proj_comp", lhs: { comp: [{ atom: "π" }, { atom: "f" }] }, rhs: { atom: "π" }, description: "Projection naturality" },
      ],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    if (result.leanSource) {
      if (!result.leanSource.includes("F.Elements")) {
        throw new Error("Expected Grothendieck elaboration using F.Elements");
      }
    }
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  // Test 11: Comma category — operator-specialized elaboration
  await test("Comma category operator elaboration compiles", async () => {
    const theory: TheoryJson = {
      name: "Comma_L_R",
      doctrine: "Category",
      objects: [
        { name: "(a, b, h)", description: "Comma object" },
      ],
      morphisms: [
        { name: "(f, g)", domain: "(a, b, h)", codomain: "(a, b, h)", description: "Comma morphism" },
      ],
      axioms: [
        { name: "comm_square", lhs: { comp: [{ atom: "f" }, { atom: "h" }] }, rhs: { comp: [{ atom: "h" }, { atom: "g" }] }, description: "Commutativity square" },
      ],
    };
    const result = await elaborate(theory, opts);
    console.log(`    Status: ${result.status}`);
    if (result.leanSource) {
      if (!result.leanSource.includes("Comma L R")) {
        throw new Error("Expected Comma category elaboration");
      }
    }
    if (result.status !== "success") {
      console.log(`    Generated Lean:\n${result.leanSource}`);
      throw new Error(`Expected success, got ${result.status}: ${result.diagnostics}`);
    }
  });

  console.log(`\n── Results: ${passed} passed, ${failed} failed ──\n`);
  if (failed > 0) process.exit(1);
}

main().catch(e => { console.error(e); process.exit(1); });
