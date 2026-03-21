/**
 * Tests for the Lean/Mathlib elaboration pipeline.
 *
 * Unit tests verify AST→Lean translation without needing Lean installed.
 * Integration tests (marked) require `lake build` to have been run.
 */

import { theoryToLean, elaborate, formatElaborationFeedback } from "../src/lean-elaborator";
import type { TheoryJson } from "../src/types";
import { strict as assert } from "assert";

// ── Test theories ─────────────────────────────────────────────────────────────

const MONOID_THEORY: TheoryJson = {
  name: "Monoid",
  doctrine: "LawvereTheory",
  objects: [{ name: "M" }],
  morphisms: [
    { name: "μ", domain: { prod: ["M", "M"] }, codomain: "M", description: "Multiplication" },
    { name: "η", domain: "terminal", codomain: "M", description: "Unit" },
  ],
  axioms: [
    {
      name: "assoc",
      lhs: { comp: [{ prod: [{ atom: "μ" }, { id: "M" }] }, { atom: "μ" }] },
      rhs: { comp: [{ prod: [{ id: "M" }, { atom: "μ" }] }, { atom: "μ" }] },
      description: "Associativity: μ(μ×id) = μ(id×μ)",
    },
  ],
};

const CATEGORY_THEORY: TheoryJson = {
  name: "SimpleCategory",
  doctrine: "Category",
  objects: [{ name: "X" }, { name: "Y" }, { name: "Z" }],
  morphisms: [
    { name: "f", domain: "X", codomain: "Y" },
    { name: "g", domain: "Y", codomain: "Z" },
  ],
  axioms: [],
};

const BAD_COMPOSITION: TheoryJson = {
  name: "BadComposition",
  doctrine: "Category",
  objects: [{ name: "A" }, { name: "B" }, { name: "C" }],
  morphisms: [
    { name: "f", domain: "A", codomain: "B" },
    { name: "g", domain: "C", codomain: "A" }, // domain mismatch for f ≫ g
  ],
  axioms: [
    {
      name: "bad_comp",
      lhs: { comp: [{ atom: "f" }, { atom: "g" }] },  // f : A→B, g : C→A — can't compose
      rhs: { atom: "f" },
      description: "This should fail: f ≫ g requires cod(f) = dom(g)",
    },
  ],
};

const MONOIDAL_THEORY: TheoryJson = {
  name: "MonoidalTest",
  doctrine: "MonoidalCategory",
  objects: [{ name: "X" }, { name: "Y" }],
  morphisms: [
    { name: "f", domain: "X", codomain: "Y" },
  ],
  axioms: [],
};

// ── Unit tests (no Lean needed) ───────────────────────────────────────────────

let passed = 0;
let failed = 0;

function test(name: string, fn: () => void) {
  try {
    fn();
    console.log(`  ✓ ${name}`);
    passed++;
  } catch (e: unknown) {
    const msg = e instanceof Error ? e.message : String(e);
    console.log(`  ✗ ${name}: ${msg}`);
    failed++;
  }
}

console.log("\n── Lean Elaborator: Translation Tests ──\n");

test("Monoid generates valid Lean structure", () => {
  const { source } = theoryToLean(MONOID_THEORY);

  // Should have Mathlib imports
  assert.ok(source.includes("import Mathlib.CategoryTheory.Category.Basic"), "missing Category import");
  assert.ok(source.includes("import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts"), "missing products import for LawvereTheory");
  assert.ok(source.includes("import Mathlib.CategoryTheory.Limits.Shapes.Terminal"), "missing terminal import");

  // Should open CategoryTheory
  assert.ok(source.includes("open CategoryTheory"), "missing open CategoryTheory");

  // Should declare universe
  assert.ok(source.includes("universe v u"), "missing universe");

  // Should have category variable
  assert.ok(source.includes("variable {C : Type u} [Category.{v} C]"), "missing category variable");

  // Should have products instance (for LawvereTheory)
  assert.ok(source.includes("Limits.HasBinaryProducts"), "missing HasBinaryProducts for LawvereTheory");
  assert.ok(source.includes("Limits.HasTerminal"), "missing HasTerminal for LawvereTheory");

  // Should declare objects
  assert.ok(source.includes("variable (M : C)"), "missing object variable M");

  // Should declare morphisms with proper types
  assert.ok(source.includes("⟶"), "missing morphism arrow");
});

test("Category theory generates morphism variables", () => {
  const { source } = theoryToLean(CATEGORY_THEORY);

  assert.ok(source.includes("variable (X Y Z : C)"), "missing object variables");
  assert.ok(source.includes("variable (f : X ⟶ Y)"), "missing morphism f");
  assert.ok(source.includes("variable (g : Y ⟶ Z)"), "missing morphism g");
});

test("Axioms generate lemmas with aesop_cat", () => {
  const { source } = theoryToLean(MONOID_THEORY);

  assert.ok(source.includes("lemma assoc"), "missing axiom lemma");
  assert.ok(source.includes("aesop_cat"), "missing aesop_cat tactic");
  assert.ok(source.includes(":= by"), "missing := by");
});

test("Monoidal doctrine adds correct instances", () => {
  const { source } = theoryToLean(MONOIDAL_THEORY);

  assert.ok(source.includes("[MonoidalCategory C]"), "missing MonoidalCategory instance");
});

test("Bad composition produces a composable expression anyway (Lean catches the error)", () => {
  const { source } = theoryToLean(BAD_COMPOSITION);

  // The translation should still produce syntactically valid Lean
  // Lean's type checker will catch the domain mismatch
  assert.ok(source.includes("f ≫ g"), "should still generate composition syntax");
  assert.ok(source.includes("lemma bad_comp"), "should still generate the lemma");
});

test("Source map tracks object, morphism, and axiom lines", () => {
  const { sourceMap } = theoryToLean(CATEGORY_THEORY);

  // Source map should have entries
  const objEntry = sourceMap.lookup(100); // Should find something
  assert.ok(objEntry !== undefined, "source map should have entries");
});

test("Namespace uses sanitized theory name", () => {
  const theory: TheoryJson = {
    name: "My Theory-2",
    doctrine: "Category",
    objects: [{ name: "X" }],
    morphisms: [],
    axioms: [],
  };
  const { source } = theoryToLean(theory);
  assert.ok(source.includes("namespace CatLab.Elaboration.My_Theory_2"), "should sanitize namespace");
  assert.ok(source.includes("end CatLab.Elaboration.My_Theory_2"), "should close namespace");
});

test("Product expressions use Mathlib syntax", () => {
  const { source } = theoryToLean(MONOID_THEORY);
  // Product domain should use ⨯
  assert.ok(source.includes("⨯"), "should use Mathlib product notation ⨯");
});

test("Terminal domain uses Mathlib syntax", () => {
  const { source } = theoryToLean(MONOID_THEORY);
  assert.ok(source.includes("⊤_ C"), "should use Mathlib terminal object notation");
});

test("Composition uses diagrammatic order ≫", () => {
  const { source } = theoryToLean(MONOID_THEORY);
  assert.ok(source.includes("≫"), "should use Mathlib diagrammatic composition ≫");
});

test("formatElaborationFeedback handles success", () => {
  const result = formatElaborationFeedback({
    status: "success",
    errors: [],
    diagnostics: "All types and axioms verified by Lean/Mathlib.",
  });
  assert.ok(result.includes("✓"), "success should have checkmark");
});

test("formatElaborationFeedback handles semantic error", () => {
  const result = formatElaborationFeedback({
    status: "semantic_error",
    errors: [{ astNodeId: "morphism:f", leanLine: 10, message: "type mismatch", severity: "fatal" }],
    diagnostics: "[SEMANTIC ERROR in morphism:f] type mismatch",
  });
  assert.ok(result.includes("✗"), "error should have X mark");
  assert.ok(result.includes("morphism:f"), "should reference the AST node");
});

test("formatElaborationFeedback handles unverified axiom", () => {
  const result = formatElaborationFeedback({
    status: "unverified_axiom",
    errors: [{ astNodeId: "axiom:assoc", leanLine: 15, message: "aesop failed", severity: "warning" }],
    diagnostics: "[UNVERIFIED in axiom:assoc] aesop failed",
  });
  assert.ok(result.includes("⚠"), "warning should have ⚠");
  assert.ok(result.includes("break them into smaller"), "should suggest alternatives");
});

// ── Dialectica / Inequality tests ──────────────────────────────────────────────

test("Inequality axioms generate ≤ instead of =", () => {
  const theory: TheoryJson = {
    name: "DialecticaTest",
    doctrine: "Dialectica",
    objects: [{ name: "A" }, { name: "B" }],
    morphisms: [
      { name: "f", domain: "A", codomain: "B" },
      { name: "g", domain: "B", codomain: "A" },
    ],
    axioms: [
      {
        name: "adjunction_ineq",
        lhs: { comp: [{ atom: "f" }, { atom: "g" }] },
        rhs: { atom: "f" },
        relation: "ineq",
        description: "f ≫ g ≤ f (adjunction inequality)",
      },
    ],
  };
  const { source } = theoryToLean(theory);
  assert.ok(source.includes("≤"), "should use ≤ for inequality axioms");
  assert.ok(!source.includes("lemma adjunction_ineq : (f ≫ g) = f"), "should NOT use = for inequality axioms");
  assert.ok(source.includes("[MonoidalCategory C]"), "Dialectica should have MonoidalCategory");
  assert.ok(source.includes("Preorder"), "Dialectica should have Preorder on Hom types");
});

test("Equality axioms still use = when relation is not set", () => {
  const { source } = theoryToLean(MONOID_THEORY);
  assert.ok(source.includes("lemma assoc : "), "should have equality lemma");
  assert.ok(!source.includes("≤"), "should not have ≤ in non-Dialectica theory");
});

// ── Realizability detection test ──────────────────────────────────────────────

test("Realizability theory detected by operator elaborator", () => {
  const theory: TheoryJson = {
    name: "Asm_A",
    doctrine: "Category",
    objects: [
      { name: "Assembly_X", description: "Assembly over PCA" },
      { name: "Assembly_Y", description: "Assembly over PCA" },
    ],
    morphisms: [
      { name: "track_f", domain: "Assembly_X", codomain: "Assembly_Y", description: "Tracking morphism" },
    ],
    axioms: [],
  };
  const { source } = theoryToLean(theory);
  assert.ok(source.includes("PCA"), "should generate PCA typeclass");
  assert.ok(source.includes("Assembly"), "should generate Assembly structure");
  assert.ok(source.includes("tracker"), "should include tracker field");
});

// ── Print generated Lean for inspection ───────────────────────────────────────

console.log("\n── Generated Lean source for Monoid ──\n");
const { source: monoidSource } = theoryToLean(MONOID_THEORY);
console.log(monoidSource);

console.log("\n── Generated Lean source for BadComposition ──\n");
const { source: badSource } = theoryToLean(BAD_COMPOSITION);
console.log(badSource);

// ── Summary ───────────────────────────────────────────────────────────────────

console.log(`\n── Results: ${passed} passed, ${failed} failed ──\n`);

if (failed > 0) process.exit(1);
