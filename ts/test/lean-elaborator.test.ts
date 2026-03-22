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
  theoryToOmega, theoryToHyperion, routeToExternal,
  morphismToHyperion, adjunctionToHyperion,
} from "../src/external-elaborators";
import type { TheoryMorphismJson } from "../src/types";
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
  assert.ok(source.includes("charMorphismTrue"), "should generate characteristic morphism");
  assert.ok(source.includes("charPred"), "should generate characteristic predicate");
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

// ── Geometric morphism elaboration tests ─────────────────────────────────

test("morphismToHyperion generates Functor block with object/morphism mappings", () => {
  const source: TheoryJson = {
    name: "A", doctrine: "InfinityNCategory",
    objects: [{ name: "X" }],
    morphisms: [{ name: "f", domain: "X", codomain: "X" }],
    axioms: [],
  };
  const target: TheoryJson = {
    name: "B", doctrine: "InfinityNCategory",
    objects: [{ name: "Y" }],
    morphisms: [{ name: "g", domain: "Y", codomain: "Y" }],
    axioms: [],
  };
  const morphism: TheoryMorphismJson = {
    name: "F",
    source: "A",
    target: "B",
    onObjects: [{ source: "X", target: { atom: "Y" } }],
    onMorphisms: [{ source: "f", target: { atom: "g" } }],
  };

  const hyp = morphismToHyperion(morphism, source, target);
  assert.ok(hyp.includes("[Functor F"), "should generate Functor block");
  assert.ok(hyp.includes("[on-object X Y]"), "should map objects");
  assert.ok(hyp.includes("[on-morphism f g]"), "should map morphisms");
  assert.ok(hyp.includes(":preserve-paths true"), "should preserve paths for ∞-categories");
  assert.ok(hyp.includes(":verify true"), "should request verification");
});

test("morphismToHyperion skips path preservation for non-PathType doctrines", () => {
  const source: TheoryJson = {
    name: "A", doctrine: "Category",
    objects: [{ name: "X" }], morphisms: [], axioms: [],
  };
  const target: TheoryJson = {
    name: "B", doctrine: "Category",
    objects: [{ name: "Y" }], morphisms: [], axioms: [],
  };
  const morphism: TheoryMorphismJson = {
    name: "F", source: "A", target: "B",
    onObjects: [{ source: "X", target: { atom: "Y" } }],
    onMorphisms: [],
  };

  const hyp = morphismToHyperion(morphism, source, target);
  assert.ok(!hyp.includes(":preserve-paths"), "should not preserve paths for plain Category");
});

test("adjunctionToHyperion generates adjoint pair with verification", () => {
  const source: TheoryJson = {
    name: "E", doctrine: "InfinityNCategory",
    objects: [{ name: "A" }], morphisms: [], axioms: [],
  };
  const target: TheoryJson = {
    name: "F", doctrine: "InfinityNCategory",
    objects: [{ name: "B" }], morphisms: [], axioms: [],
  };
  const inverseImage: TheoryMorphismJson = {
    name: "f_star", source: "F", target: "E",
    onObjects: [{ source: "B", target: { atom: "A" } }],
    onMorphisms: [],
  };
  const directImage: TheoryMorphismJson = {
    name: "f_lower", source: "E", target: "F",
    onObjects: [{ source: "A", target: { atom: "B" } }],
    onMorphisms: [],
  };

  const hyp = adjunctionToHyperion("geom_f", inverseImage, directImage, source, target);
  assert.ok(hyp.includes("[Adjunction geom_f"), "should generate Adjunction block");
  assert.ok(hyp.includes(":left geom_f_star"), "should reference left adjoint");
  assert.ok(hyp.includes(":right geom_f_lower"), "should reference right adjoint");
  assert.ok(hyp.includes("[Functor geom_f_star"), "should emit inverse image functor");
  assert.ok(hyp.includes("[Functor geom_f_lower"), "should emit direct image functor");
  assert.ok(hyp.includes(":preserve-paths true"), "inverse image should preserve paths");
});

// ── ∞-Topos integration tests ─────────────────────────────────────────────
// These tests verify the full pipeline: define two ∞-topoi with higher-categorical
// structure (object classifier, descent, mapping spaces), construct a geometric
// morphism between them, and verify that Hyperion elaboration correctly:
//   1. Emits PathType + e-graph structures for both topoi
//   2. The inverse image functor preserves paths (finite limit preservation)
//   3. The adjunction is declared with :verify true
//   4. The object classifier (univalent universe) appears in the generated source

test("∞-topos geometric morphism: Spaces → Sh(X) with object classifier", () => {
  // ∞-topos of spaces (the terminal ∞-topos)
  const spaces: TheoryJson = {
    name: "Spaces",
    doctrine: "PresentableInfinityCategory",
    objects: [
      { name: "Ob", description: "Objects (spaces)" },
      { name: "Map", description: "Morphisms (continuous maps)" },
      { name: "Spc", description: "Mapping spaces (∞-groupoids)" },
    ],
    morphisms: [
      { name: "src", domain: "Map", codomain: "Ob" },
      { name: "tgt", domain: "Map", codomain: "Ob" },
      { name: "id_map", domain: "Ob", codomain: "Map" },
      { name: "hom_space", domain: { prod: ["Ob", "Ob"] }, codomain: "Spc" },
      { name: "U_obj", domain: "terminal", codomain: "Ob", description: "Universe object" },
      { name: "U_tilde", domain: "terminal", codomain: "Ob", description: "Pointed universe" },
      { name: "univ_fib", domain: "terminal", codomain: "Map", description: "Universal fibration p : Ũ → U" },
      { name: "colim", domain: "Spc", codomain: "Ob" },
      { name: "lim", domain: "Spc", codomain: "Ob" },
    ],
    axioms: [
      {
        name: "univ_fib_src",
        lhs: { comp: [{ atom: "univ_fib" }, { atom: "src" }] },
        rhs: { atom: "U_tilde" },
        description: "src(univ_fib) = Ũ",
      },
      {
        name: "univ_fib_tgt",
        lhs: { comp: [{ atom: "univ_fib" }, { atom: "tgt" }] },
        rhs: { atom: "U_obj" },
        description: "tgt(univ_fib) = U",
      },
      {
        name: "descent_axiom",
        lhs: { comp: [{ atom: "colim" }, { atom: "lim" }] },
        rhs: { id: "Spc" },
        description: "Colimits are universal (descent)",
      },
    ],
  };

  // ∞-topos of sheaves on a space X
  const shX: TheoryJson = {
    name: "ShX",
    doctrine: "PresentableInfinityCategory",
    objects: [
      { name: "ShOb", description: "Sheaf objects" },
      { name: "ShMap", description: "Sheaf morphisms" },
      { name: "ShSpc", description: "Sheaf mapping spaces" },
    ],
    morphisms: [
      { name: "sh_src", domain: "ShMap", codomain: "ShOb" },
      { name: "sh_tgt", domain: "ShMap", codomain: "ShOb" },
      { name: "sh_id", domain: "ShOb", codomain: "ShMap" },
      { name: "sh_hom", domain: { prod: ["ShOb", "ShOb"] }, codomain: "ShSpc" },
      { name: "ShU", domain: "terminal", codomain: "ShOb", description: "Sheaf universe" },
      { name: "ShU_tilde", domain: "terminal", codomain: "ShOb" },
      { name: "sh_univ_fib", domain: "terminal", codomain: "ShMap" },
      { name: "sh_colim", domain: "ShSpc", codomain: "ShOb" },
      { name: "sh_lim", domain: "ShSpc", codomain: "ShOb" },
    ],
    axioms: [
      {
        name: "sh_descent",
        lhs: { comp: [{ atom: "sh_colim" }, { atom: "sh_lim" }] },
        rhs: { id: "ShSpc" },
      },
    ],
  };

  // Geometric morphism f : Sh(X) → Spaces
  // f* : Spaces → Sh(X) (inverse image = constant sheaf functor)
  const inverseImage: TheoryMorphismJson = {
    name: "const_sheaf", source: "Spaces", target: "ShX",
    onObjects: [
      { source: "Ob", target: { atom: "ShOb" } },
      { source: "Map", target: { atom: "ShMap" } },
      { source: "Spc", target: { atom: "ShSpc" } },
    ],
    onMorphisms: [
      { source: "src", target: { atom: "sh_src" } },
      { source: "tgt", target: { atom: "sh_tgt" } },
      { source: "id_map", target: { atom: "sh_id" } },
      { source: "colim", target: { atom: "sh_colim" } },
      { source: "lim", target: { atom: "sh_lim" } },
    ],
  };

  // f_* : Sh(X) → Spaces (direct image = global sections functor)
  const directImage: TheoryMorphismJson = {
    name: "global_sections", source: "ShX", target: "Spaces",
    onObjects: [
      { source: "ShOb", target: { atom: "Ob" } },
      { source: "ShMap", target: { atom: "Map" } },
      { source: "ShSpc", target: { atom: "Spc" } },
    ],
    onMorphisms: [
      { source: "sh_src", target: { atom: "src" } },
      { source: "sh_tgt", target: { atom: "tgt" } },
      { source: "sh_id", target: { atom: "id_map" } },
    ],
  };

  const hyp = adjunctionToHyperion("f", inverseImage, directImage, spaces, shX);

  // ── Structural checks ──────────────────────────────────────────────────

  // Both theories should appear as full Hyperion Category blocks with PathType
  assert.ok(hyp.includes("[Category SpacesCat"), "should emit Spaces category");
  assert.ok(hyp.includes("[Category ShXCat"), "should emit ShX category");

  // PathType must be injected for PresentableInfinityCategory doctrine
  const pathTypeCount = (hyp.match(/\[PathType/g) || []).length;
  assert.ok(pathTypeCount >= 2, `should have PathType in both theories, got ${pathTypeCount}`);

  // E-graph equality saturation (needed for ∞-categorical coherence)
  assert.ok(hyp.includes("equality-saturation"), "should use e-graph for ∞-categories");

  // Object classifier / universe should appear in the generated source
  assert.ok(hyp.includes("U_obj"), "should include universe object");
  assert.ok(hyp.includes("univ_fib"), "should include universal fibration");

  // ── Functor checks ─────────────────────────────────────────────────────

  // Inverse image: f* must preserve paths (finite limits)
  assert.ok(hyp.includes("[Functor f_star"), "should emit inverse image functor");
  assert.ok(hyp.includes("[Functor f_lower"), "should emit direct image functor");

  // The inverse image functor must have :preserve-paths true
  // (this is what makes it a geometric morphism, not just any adjunction)
  const fStarStart = hyp.indexOf("[Functor f_star");
  const fStarBlock = hyp.slice(fStarStart, fStarStart + 500);
  assert.ok(fStarBlock.includes(":preserve-paths true"), "f* must preserve paths (finite limits)");

  // ── Adjunction checks ──────────────────────────────────────────────────

  assert.ok(hyp.includes("[Adjunction f"), "should declare adjunction");
  assert.ok(hyp.includes(":left f_star"), "f* should be left adjoint");
  assert.ok(hyp.includes(":right f_lower"), "f_* should be right adjoint");
  assert.ok(hyp.includes(":verify true"), "adjunction should request verification");

  // ── Descent axiom should appear in proofs ──────────────────────────────

  assert.ok(hyp.includes("descent_axiom"), "should include descent axiom");
  assert.ok(hyp.includes("[assert-eq"), "should generate assertion blocks");

  // ── Extract-proof for higher paths ─────────────────────────────────────
  // For PathType doctrines, Hyperion must extract proof terms (paths/2-cells),
  // not just check boolean equality. This is the key ∞-categorical requirement.
  assert.ok(hyp.includes("[extract-proof"), "should extract proof terms for PathType doctrine");
});

test("∞-topos univalence: Equiv(A,B) ≃ (A = B) in object classifier", () => {
  // A minimal ∞-topos with the univalence axiom encoded
  const univalentTopos: TheoryJson = {
    name: "UnivalentTopos",
    doctrine: "PresentableInfinityCategory",
    objects: [
      { name: "Type", description: "Objects (types/spaces)" },
      { name: "Equiv", description: "Equivalences between types" },
      { name: "Path", description: "Identity paths" },
    ],
    morphisms: [
      { name: "src_eq", domain: "Equiv", codomain: "Type" },
      { name: "tgt_eq", domain: "Equiv", codomain: "Type" },
      { name: "src_path", domain: "Path", codomain: "Type" },
      { name: "tgt_path", domain: "Path", codomain: "Type" },
      // The univalence map: paths → equivalences
      { name: "idtoequiv", domain: "Path", codomain: "Equiv", description: "Identity induces equivalence" },
      // The inverse: equivalences → paths (univalence)
      { name: "ua", domain: "Equiv", codomain: "Path", description: "Univalence axiom" },
    ],
    axioms: [
      {
        name: "ua_section",
        lhs: { comp: [{ atom: "ua" }, { atom: "idtoequiv" }] },
        rhs: { id: "Equiv" },
        description: "ua ∘ idtoequiv = id (univalence section)",
      },
      {
        name: "ua_retraction",
        lhs: { comp: [{ atom: "idtoequiv" }, { atom: "ua" }] },
        rhs: { id: "Path" },
        description: "idtoequiv ∘ ua = id (univalence retraction)",
      },
    ],
  };

  const hyp = theoryToHyperion(univalentTopos);

  // The univalence axiom should appear as laws in the e-graph
  assert.ok(hyp.includes("ua_section"), "should include ua section axiom");
  assert.ok(hyp.includes("ua_retraction"), "should include ua retraction axiom");

  // PathType must be present for the univalent universe
  assert.ok(hyp.includes("[PathType"), "univalent topos needs PathType");

  // E-graph saturation should detect that ua and idtoequiv are inverses
  assert.ok(hyp.includes("@law"), "should use @law (bidirectional) for e-graph saturation");

  // extract-proof: the proof that ua ∘ idtoequiv = id should be extractable
  // as a path in the identity type, not just a boolean
  assert.ok(hyp.includes("extract-proof"), "should extract proof paths for univalence");

  // The Hyperion output should verify both directions of the equivalence
  assert.ok(hyp.includes("[assert-eq ua_section"), "should assert ua section");
  assert.ok(hyp.includes("[assert-eq ua_retraction"), "should assert ua retraction");
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
// ── Expanded tactic tests ─────────────────────────────────────────────────

test("LemmaJson with rw tactic generates rewrite steps", () => {
  const theory: TheoryJson = {
    name: "RwTest", doctrine: "Category",
    objects: [{ name: "X" }],
    morphisms: [{ name: "f", domain: "X", codomain: "X" }],
    axioms: [{ name: "idem", lhs: { comp: [{ atom: "f" }, { atom: "f" }] }, rhs: { atom: "f" } }],
    lemmas: [{
      name: "step1",
      lhs: { comp: [{ atom: "f" }, { atom: "f" }] },
      rhs: { atom: "f" },
      tactic: "rw",
      tacticSteps: ["rw [Category.comp_id]", "exact h"],
      forAxiom: "idem",
    }],
  };
  const { source } = theoryToLean(theory);
  assert.ok(source.includes("rw [Category.comp_id]"), "should emit rw step");
  assert.ok(source.includes("exact h"), "should emit exact step");
});

test("LemmaJson with steps tactic generates arbitrary tactic sequence", () => {
  const theory: TheoryJson = {
    name: "StepsTest", doctrine: "Category",
    objects: [{ name: "X" }],
    morphisms: [{ name: "f", domain: "X", codomain: "X" }],
    axioms: [{ name: "ax", lhs: { atom: "a" }, rhs: { atom: "b" } }],
    lemmas: [{
      name: "pca_reduce",
      lhs: { atom: "skk_a" },
      rhs: { atom: "a" },
      tactic: "steps",
      tacticSteps: [
        "unfold PCA.skk",
        "rw [PCA.s_app₃]",
        "rw [PCA.k_app₂]",
        "rfl",
      ],
      forAxiom: "ax",
    }],
  };
  const { source } = theoryToLean(theory);
  assert.ok(source.includes("unfold PCA.skk"), "should emit unfold");
  assert.ok(source.includes("rw [PCA.s_app₃]"), "should emit S rewrite");
  assert.ok(source.includes("rw [PCA.k_app₂]"), "should emit K rewrite");
});

test("LemmaJson with apply tactic uses proofTerm", () => {
  const theory: TheoryJson = {
    name: "ApplyTest", doctrine: "Category",
    objects: [{ name: "X" }],
    morphisms: [],
    axioms: [{ name: "ax", lhs: { atom: "a" }, rhs: { atom: "b" } }],
    lemmas: [{
      name: "use_trans",
      lhs: { atom: "a" },
      rhs: { atom: "b" },
      tactic: "apply",
      proofTerm: "S.trans a c b",
      forAxiom: "ax",
    }],
  };
  const { source } = theoryToLean(theory);
  assert.ok(source.includes("apply S.trans a c b"), "should emit apply with proof term");
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

// ── Verification feedback tests ───────────────────────────────────────────

import { formatStructuralDiff } from "../src/llm";
import type { VerificationResult } from "../src/types";

test("formatStructuralDiff shows partial forms and trace on timeout", () => {
  const result: VerificationResult = {
    verified: false,
    candidateName: "TestCandidate",
    verificationStatus: "⏱ Timeout at depth 200",
    missingSignatures: [],
    unmappedObjects: [],
    axiomViolations: [
      {
        sourceAxiom: "assoc",
        status: "⏱ Timeout at depth 200",
        lhsReduced: "comp(prod(μ, id(M)), μ)",
        rhsReduced: "comp(prod(id(M), μ), μ)",
        depthUsed: 200,
        lhsTrace: ["assoc", "unit_l", "assoc", "unit_l", "assoc", "unit_l"],
        rhsTrace: ["unit_r", "assoc"],
      },
    ],
  };
  const feedback = formatStructuralDiff(result);
  // Should show partial normal forms (not hidden behind "circular rewriting loops")
  assert.ok(feedback.includes("comp(prod(μ, id(M)), μ)"), "should show LHS partial form");
  assert.ok(feedback.includes("comp(prod(id(M), μ), μ)"), "should show RHS partial form");
  // Should show rewrite trace
  assert.ok(feedback.includes("assoc → unit_l → assoc"), "should show LHS rewrite trace");
  // Should detect cycling (assoc appears 3+ times)
  assert.ok(feedback.includes("CYCLING DETECTED"), "should detect cycling rules");
  assert.ok(feedback.includes("assoc"), "should name the cycling rule");
});

test("formatStructuralDiff shows doctrine auto-upgrade info", () => {
  const result: VerificationResult = {
    verified: true,
    candidateName: "TestCandidate",
    verificationStatus: "✓ Success",
    missingSignatures: [],
    unmappedObjects: [],
    axiomViolations: [],
    doctrine: "CartesianCategory",
  };
  const feedback = formatStructuralDiff(result);
  assert.ok(feedback.includes("CartesianCategory"), "should mention upgraded doctrine");
  assert.ok(feedback.includes("auto-inferred"), "should explain auto-inference");
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
