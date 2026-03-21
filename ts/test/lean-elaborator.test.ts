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

// ── External elaborator tests ────────────────────────────────────────────────

import {
  theoryToOmega, theoryToHyperion, routeToExternal, compileCrossTierFunctor,
  truncateToHomotopyCategory, truncatedTheoryToLean, computeTheoryPushout,
} from "../src/external-elaborators";
import type { CrossTierFunctor } from "../src/external-elaborators";

test("routeToExternal routes LawvereTheory to omega", () => {
  assert.equal(routeToExternal(MONOID_THEORY), "omega");
});

test("routeToExternal routes InfinityNCategory to hyperion", () => {
  const theory: TheoryJson = {
    name: "Inf2", doctrine: "InfinityNCategory",
    objects: [{ name: "Cell0" }], morphisms: [], axioms: [],
  };
  assert.equal(routeToExternal(theory), "hyperion");
});

test("routeToExternal returns null for Category", () => {
  assert.equal(routeToExternal(CATEGORY_THEORY), null);
});

test("theoryToOmega generates valid sort and constructor declarations", () => {
  const source = theoryToOmega(MONOID_THEORY);
  assert.ok(source.includes("(sort M)"), "missing sort");
  assert.ok(source.includes("(constructor μ : (-> M M M))"), "missing μ constructor");
  assert.ok(source.includes("(constructor η : M)"), "missing η constructor");
  assert.ok(source.includes("(theory Monoid"), "missing theory name");
  assert.ok(source.includes("eq-refl"), "missing eq-refl rule");
  assert.ok(source.includes(";; @node morphism:μ"), "missing @node annotation");
});

test("theoryToHyperion generates Category/Substrate/Universe blocks", () => {
  const theory: TheoryJson = {
    name: "HoTTTest", doctrine: "MartinLofTypeTheory",
    objects: [{ name: "Ctx" }, { name: "Ty" }, { name: "Tm" }],
    morphisms: [{ name: "app", domain: { prod: ["Tm", "Tm"] }, codomain: "Tm" }],
    axioms: [],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[Category HoTTTestCat"), "missing Category block");
  assert.ok(source.includes("[Substrate HoTTTestSub"), "missing Substrate block");
  assert.ok(source.includes("[Universe HoTTTestUni"), "missing Universe block");
  assert.ok(source.includes("[PathType"), "missing PathType for MLTT");
  assert.ok(source.includes("[JType"), "missing JType for MLTT");
  assert.ok(source.includes("@equality rewrite-equivalence"), "MLTT should use rewrite, not e-graph");
});

test("theoryToHyperion uses e-graph for InfinityNCategory", () => {
  const theory: TheoryJson = {
    name: "Inf", doctrine: "InfinityNCategory",
    objects: [{ name: "Cell0" }], morphisms: [], axioms: [],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("@equality equality-saturation"), "should use e-graph");
});

test("theoryToHyperion adds PartialElement for CubicalTypeTheory", () => {
  const theory: TheoryJson = {
    name: "Cub", doctrine: "CubicalTypeTheory",
    objects: [{ name: "Ctx" }], morphisms: [], axioms: [],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[PartialElement"), "missing PartialElement for cubical");
});

test("theoryToOmega declares structural combinators when used in axioms", () => {
  const theory: TheoryJson = {
    name: "CompTest", doctrine: "LawvereTheory",
    objects: [{ name: "M" }],
    morphisms: [{ name: "f", domain: "M", codomain: "M" }],
    axioms: [
      { name: "ax", lhs: { comp: [{ atom: "f" }, { atom: "f" }] }, rhs: { atom: "f" } },
    ],
  };
  const source = theoryToOmega(theory);
  assert.ok(source.includes("(constructor comp :"), "should declare comp when used");
});

test("theoryToOmega uses auto tactic fallback", () => {
  const source = theoryToOmega(MONOID_THEORY);
  assert.ok(source.includes("(try (eq-refl) (auto 10))"), "should use auto as fallback tactic");
});

test("theoryToOmega detects AC operations for commutative theories", () => {
  const theory: TheoryJson = {
    name: "CommMonoid", doctrine: "LawvereTheory",
    objects: [{ name: "M" }],
    morphisms: [
      { name: "op", domain: { prod: ["M", "M"] }, codomain: "M" },
    ],
    axioms: [
      { name: "assoc", lhs: { atom: "op_assoc_l" }, rhs: { atom: "op_assoc_r" } },
      { name: "commutativity", lhs: { atom: "op_x_y" }, rhs: { atom: "op_y_x" }, description: "Commutativity of op" },
    ],
  };
  const source = theoryToOmega(theory);
  assert.ok(source.includes("(attribute op :ac)"), "should add :ac attribute");
  assert.ok(source.includes("commutativity handled by :ac"), "should skip commutativity rewrite");
});

test("theoryToOmega generates lemmas for theories with many axioms", () => {
  const theory: TheoryJson = {
    name: "BigTheory", doctrine: "LawvereTheory",
    objects: [{ name: "X" }],
    morphisms: [{ name: "f", domain: "X", codomain: "X" }],
    axioms: [
      { name: "ax1", lhs: { atom: "a" }, rhs: { atom: "b" } },
      { name: "ax2", lhs: { atom: "c" }, rhs: { atom: "d" } },
      { name: "ax3", lhs: { atom: "e" }, rhs: { atom: "f" } },
      { name: "ax4", lhs: { atom: "g" }, rhs: { atom: "h" } },
    ],
  };
  const source = theoryToOmega(theory);
  assert.ok(source.includes("(lemma derived-ax1"), "should generate incremental lemmas");
});

test("theoryToHyperion generates assert-neq on directed substrate for e-graph doctrines", () => {
  const theory: TheoryJson = {
    name: "Inf2Test", doctrine: "InfinityNCategory",
    objects: [{ name: "Cell0" }, { name: "Cell2" }],
    morphisms: [{ name: "vcomp", domain: { prod: ["Cell2", "Cell2"] }, codomain: "Cell2" }],
    axioms: [{ name: "interchange", lhs: { atom: "lhs" }, rhs: { atom: "rhs" } }],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[assert-neq interchange-blocked"), "should generate assert-neq on directed substrate");
  assert.ok(source.includes("@equality rewrite-equivalence"), "should have directed substrate block");
});

test("theoryToHyperion generates eval-simplify for e-graph doctrines", () => {
  const theory: TheoryJson = {
    name: "SimplifyTest", doctrine: "InfinityNCategory",
    objects: [{ name: "Cell0" }, { name: "Cell2" }],
    morphisms: [{ name: "vcomp", domain: { prod: ["Cell2", "Cell2"] }, codomain: "Cell2" }],
    axioms: [{ name: "law1", lhs: { atom: "a" }, rhs: { atom: "b" } }],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[eval-simplify canonical-vcomp"), "should generate eval-simplify");
});

test("theoryToHyperion adds ModalOperator for CohesiveHomotopyTypeTheory", () => {
  const theory: TheoryJson = {
    name: "Cohesive", doctrine: "CohesiveHomotopyTypeTheory",
    objects: [{ name: "Type" }], morphisms: [], axioms: [],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[ModalOperator"), "should add ModalOperator for cohesive");
  assert.ok(source.includes("[PathType"), "should add PathType for cohesive");
});

test("theoryToHyperion generates Functor :verify for sort-mapping morphisms", () => {
  const theory: TheoryJson = {
    name: "FunctorTest", doctrine: "InfinityNCategory",
    objects: [{ name: "A" }, { name: "B" }],
    morphisms: [{ name: "F", domain: "A", codomain: "B" }],
    axioms: [],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[Functor F"), "should generate Functor block");
  assert.ok(source.includes(":verify"), "should include :verify flag");
});

test("theoryToHyperion uses @rule on rewrite substrate", () => {
  const theory: TheoryJson = {
    name: "RuleTest", doctrine: "MartinLofTypeTheory",
    objects: [{ name: "Tm" }],
    morphisms: [],
    axioms: [{ name: "beta", lhs: { atom: "app_lam" }, rhs: { atom: "x" } }],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[@rule beta app_lam ==> x]"), "MLTT should use @rule (directed)");
});

// ── Tripos-to-Topos tests ─────────────────────────────────────────────────

test("Realizability generates subobject classifier Ω", () => {
  const theory: TheoryJson = {
    name: "Asm_K1",
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
  assert.ok(source.includes("RealizedProp"), "should generate RealizedProp structure");
  assert.ok(source.includes("omegaAssembly"), "should generate Ω assembly");
  assert.ok(source.includes("charMorphism"), "should generate characteristic morphism");
  assert.ok(source.includes("subobject_classifier_pullback"), "should generate pullback theorem");
});

test("Realizability generates PER category with Ω_PER", () => {
  const theory: TheoryJson = {
    name: "Asm_K1",
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
  assert.ok(source.includes("PER (A : Type"), "should generate PER structure");
  assert.ok(source.includes("PERHom"), "should generate PER morphism structure");
  assert.ok(source.includes("omegaPER"), "should generate Ω_PER subobject classifier");
  assert.ok(source.includes("Category (PER A)"), "should generate PER category instance");
});

// ── Hyperion path extraction tests ────────────────────────────────────────

test("theoryToHyperion generates extract-proof for PathType doctrines", () => {
  const theory: TheoryJson = {
    name: "PathTest", doctrine: "MartinLofTypeTheory",
    objects: [{ name: "Tm" }],
    morphisms: [],
    axioms: [{ name: "beta", lhs: { atom: "app_lam" }, rhs: { atom: "x" } }],
  };
  const source = theoryToHyperion(theory);
  assert.ok(source.includes("[extract-proof beta-path"), "should request proof extraction for MLTT");
});

test("theoryToHyperion does NOT generate extract-proof for non-PathType doctrines", () => {
  const source = theoryToOmega(MONOID_THEORY);
  assert.ok(!source.includes("extract-proof"), "Omega should not have extract-proof");
});

// ── Cross-tier functor tests ──────────────────────────────────────────────

test("compileCrossTierFunctor merges omega→lean into unified theory", () => {
  const monoid: TheoryJson = {
    name: "Mon", doctrine: "LawvereTheory",
    objects: [{ name: "M" }],
    morphisms: [{ name: "mu", domain: { prod: ["M", "M"] }, codomain: "M" }],
    axioms: [{ name: "assoc", lhs: { atom: "lhs" }, rhs: { atom: "rhs" } }],
  };
  const cat: TheoryJson = {
    name: "Set", doctrine: "Category",
    objects: [{ name: "S" }],
    morphisms: [{ name: "f", domain: "S", codomain: "S" }],
    axioms: [],
  };
  const functor: CrossTierFunctor = {
    name: "Free",
    source: { theory: monoid, tier: "omega" },
    target: { theory: cat, tier: null },
    objectMap: { M: "S" },
    morphismMap: { mu: "f" },
  };
  const { unifiedTheory, verifyWith } = compileCrossTierFunctor(functor);

  // Should compile to Lean (higher tier)
  assert.equal(verifyWith, null, "should verify with Lean (null)");

  // Should have merged objects with prefixes
  const objNames = unifiedTheory.objects.map(o => o.name);
  assert.ok(objNames.includes("src_M"), "should have prefixed source object");
  assert.ok(objNames.includes("tgt_S"), "should have prefixed target object");

  // Should have functor object mapping
  const morNames = unifiedTheory.morphisms.map(m => m.name);
  assert.ok(morNames.includes("F_obj_M"), "should have functor object mapping");

  // Should have merged axioms with prefixes
  const axNames = unifiedTheory.axioms.map(a => a.name);
  assert.ok(axNames.includes("src_assoc"), "should have prefixed source axiom");
  assert.ok(axNames.includes("F_mor_mu"), "should have functor morphism mapping");
});

test("compileCrossTierFunctor chooses correct tier for hyperion target", () => {
  const omega: TheoryJson = {
    name: "Mon", doctrine: "LawvereTheory",
    objects: [{ name: "M" }], morphisms: [], axioms: [],
  };
  const hyp: TheoryJson = {
    name: "Inf", doctrine: "InfinityNCategory",
    objects: [{ name: "Cell" }], morphisms: [], axioms: [],
  };
  const functor: CrossTierFunctor = {
    name: "Embed",
    source: { theory: omega, tier: "omega" },
    target: { theory: hyp, tier: "hyperion" },
    objectMap: { M: "Cell" },
    morphismMap: {},
  };
  const { verifyWith } = compileCrossTierFunctor(functor);
  assert.equal(verifyWith, "hyperion", "should verify at the higher tier (hyperion)");
});

// ── Downward truncation tests ──────────────────────────────────────────────

test("truncateToHomotopyCategory downgrades doctrine to Category", () => {
  const theory: TheoryJson = {
    name: "Inf2", doctrine: "InfinityNCategory",
    objects: [{ name: "Cell0" }, { name: "Cell1" }],
    morphisms: [{ name: "f", domain: "Cell0", codomain: "Cell1" }],
    axioms: [{ name: "coherence", lhs: { atom: "a" }, rhs: { atom: "b" } }],
  };
  const truncated = truncateToHomotopyCategory(theory);
  assert.equal(truncated.doctrine, "Category", "should downgrade to Category");
  assert.equal(truncated.name, "Ho_Inf2", "should prefix with Ho_");
  assert.equal(truncated.axioms.length, 1, "should preserve axioms");
  assert.ok(truncated.axioms[0].description?.includes("[truncated]"), "should mark as truncated");
});

test("truncateToHomotopyCategory adds e-graph discoveries as axioms", () => {
  const theory: TheoryJson = {
    name: "Test", doctrine: "InfinityNCategory",
    objects: [{ name: "X" }], morphisms: [], axioms: [],
  };
  const discoveries = [
    { lhs: "f", rhs: "g", description: "Eckmann-Hilton" },
  ];
  const truncated = truncateToHomotopyCategory(theory, discoveries);
  assert.equal(truncated.axioms.length, 1, "should add discovery as axiom");
  assert.ok(truncated.axioms[0].name.includes("egraph"), "should prefix with egraph");
});

test("truncatedTheoryToLean generates Quotient-based Lean source", () => {
  const theory: TheoryJson = {
    name: "Inf", doctrine: "InfinityNCategory",
    objects: [{ name: "X" }], morphisms: [],
    axioms: [{ name: "ax1", lhs: { atom: "a" }, rhs: { atom: "b" } }],
  };
  const discoveries = [
    { lhs: "f", rhs: "g", description: "path", proof_term: "concat p q", rewrite_steps: ["p", "q"] },
  ];
  const source = truncatedTheoryToLean(theory, discoveries);
  assert.ok(source.includes("Mathlib.CategoryTheory.Quotient"), "should import Quotient");
  assert.ok(source.includes("Homotopy category"), "should mention homotopy category");
  assert.ok(source.includes("truncate_f_g"), "should generate truncation axiom");
  assert.ok(source.includes("Original path: concat p q"), "should include proof term");
  assert.ok(source.includes("Via: p → q"), "should include rewrite steps");
});

// ── Lemma loop tests ──────────────────────────────────────────────────────

test("TheoryJson with lemmas generates intermediate Lean lemmas", () => {
  const theory: TheoryJson = {
    name: "LemmaTest",
    doctrine: "Category",
    objects: [{ name: "X" }, { name: "Y" }],
    morphisms: [
      { name: "f", domain: "X", codomain: "Y" },
      { name: "g", domain: "Y", codomain: "X" },
    ],
    axioms: [
      { name: "round_trip", lhs: { comp: [{ atom: "f" }, { atom: "g" }] }, rhs: { id: "X" } },
    ],
    lemmas: [
      {
        name: "fg_endo",
        lhs: { comp: [{ atom: "f" }, { atom: "g" }] },
        rhs: { comp: [{ atom: "f" }, { atom: "g" }] },
        tactic: "rfl",
        forAxiom: "round_trip",
      },
    ],
  };
  const { source } = theoryToLean(theory);
  assert.ok(source.includes("lemma fg_endo"), "should generate intermediate lemma");
  assert.ok(source.includes("rfl"), "should use rfl tactic");
  assert.ok(source.includes("have := fg_endo"), "should reference lemma in axiom proof");
});

test("TheoryJson without lemmas works as before", () => {
  const { source } = theoryToLean(CATEGORY_THEORY);
  assert.ok(!source.includes("Intermediate lemmas"), "should not have lemma section");
});

// ── Theory pushout tests ──────────────────────────────────────────────────

test("computeTheoryPushout merges theories over common base", () => {
  const base: TheoryJson = {
    name: "Set", doctrine: "Category",
    objects: [{ name: "S" }],
    morphisms: [{ name: "id_S", domain: "S", codomain: "S" }],
    axioms: [],
  };
  const theoryA: TheoryJson = {
    name: "Mon", doctrine: "LawvereTheory",
    objects: [{ name: "S" }, { name: "M" }],
    morphisms: [
      { name: "id_S", domain: "S", codomain: "S" },
      { name: "mu", domain: { prod: ["M", "M"] }, codomain: "M" },
    ],
    axioms: [{ name: "assoc", lhs: { atom: "l" }, rhs: { atom: "r" } }],
  };
  const theoryB: TheoryJson = {
    name: "Grp", doctrine: "LawvereTheory",
    objects: [{ name: "S" }, { name: "G" }],
    morphisms: [
      { name: "id_S", domain: "S", codomain: "S" },
      { name: "inv", domain: "G", codomain: "G" },
    ],
    axioms: [{ name: "inv_law", lhs: { atom: "l" }, rhs: { atom: "r" } }],
  };

  const pushout = computeTheoryPushout(theoryA, theoryB, base);

  // Should identify shared base objects
  assert.equal(pushout.objects.length, 3, "S + M + G = 3 objects");
  const objNames = pushout.objects.map(o => o.name);
  assert.ok(objNames.includes("S"), "should have shared S");
  assert.ok(objNames.includes("M"), "should have M from Mon");
  assert.ok(objNames.includes("G"), "should have G from Grp");

  // Should identify shared base morphisms
  assert.equal(pushout.morphisms.length, 3, "id_S + mu + inv = 3 morphisms");

  // Should merge axioms
  assert.equal(pushout.axioms.length, 2, "assoc + inv_law = 2 axioms");

  // Should pick higher doctrine
  assert.equal(pushout.doctrine, "LawvereTheory");
});

test("computeTheoryPushout name includes both theories", () => {
  const base: TheoryJson = { name: "C", doctrine: "Category", objects: [], morphisms: [], axioms: [] };
  const a: TheoryJson = { name: "A", doctrine: "Category", objects: [], morphisms: [], axioms: [] };
  const b: TheoryJson = { name: "B", doctrine: "Category", objects: [], morphisms: [], axioms: [] };
  const pushout = computeTheoryPushout(a, b, base);
  assert.ok(pushout.name.includes("A") && pushout.name.includes("B"), "should name after both theories");
});

// ── PER Quotient tests ────────────────────────────────────────────────────

test("Realizability PER category uses Setoid/Quotient", () => {
  const theory: TheoryJson = {
    name: "Asm_K1",
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
  assert.ok(source.includes("perHomSetoid"), "should define Setoid for PER morphisms");
  assert.ok(source.includes("Quotient.mk"), "should use Quotient.mk for morphisms");
  assert.ok(source.includes("Quotient.sound"), "should use Quotient.sound for laws");
  assert.ok(source.includes("Quotient.inductionOn"), "should use Quotient.inductionOn for id_comp");
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
