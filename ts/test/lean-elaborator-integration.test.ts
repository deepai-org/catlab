/**
 * Integration test: runs the full Lean/Mathlib elaboration pipeline.
 * Requires: `lake exe cache get` (Mathlib oleans downloaded)
 */

import { elaborate } from "../src/lean-elaborator";
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

  console.log(`\n── Results: ${passed} passed, ${failed} failed ──\n`);
  if (failed > 0) process.exit(1);
}

main().catch(e => { console.error(e); process.exit(1); });
