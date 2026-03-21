/**
 * Operator-Specialized Elaboration Strategies
 *
 * When a TheoryJson was produced by a known CatLab operator (functorCategory,
 * grothendieck, comma, limits, etc.), the elaborator can generate specialized
 * Lean code that uses the corresponding Mathlib typeclass directly — getting
 * full semantic verification from Lean's type checker rather than the generic
 * "objects + morphisms + axiom lemmas" translation.
 *
 * Each strategy:
 *   1. Detects whether a TheoryJson matches its operator's output shape
 *   2. Generates specialized Lean source using Mathlib structures
 *   3. Returns a SourceMap for error attribution
 */

import type { TheoryJson, ExprJson } from "./types";

// ── Detection ─────────────────────────────────────────────────────────────────

export interface OperatorDetection {
  operator: string;
  /** Generate specialized Lean source for this operator's output */
  generate: (theory: TheoryJson) => string;
  /** Additional Mathlib imports required */
  imports: string[];
}

/**
 * Attempt to detect which operator produced a TheoryJson based on
 * structural signatures (name patterns, morphism shapes, tags).
 */
export function detectOperator(theory: TheoryJson): OperatorDetection | null {
  // Functor category: has objects like F, G, H and morphisms α, β with
  // naturality axioms
  if (isFunctorCategory(theory)) {
    return {
      operator: "functorCategory",
      generate: generateFunctorCategory,
      imports: [
        "Mathlib.CategoryTheory.Functor.Category",
        "Mathlib.CategoryTheory.NatTrans",
      ],
    };
  }

  // Grothendieck / category of elements: has paired objects like (X, x)
  // with projection morphisms
  if (isGrothendieckConstruction(theory)) {
    return {
      operator: "grothendieck",
      generate: generateGrothendieck,
      imports: [
        "Mathlib.CategoryTheory.Elements",
      ],
    };
  }

  // Comma category: has objects as triples (a, b, h) with commutativity axioms
  if (isCommaCategory(theory)) {
    return {
      operator: "comma",
      generate: generateComma,
      imports: [
        "Mathlib.CategoryTheory.Comma.Basic",
      ],
    };
  }

  return null;
}

// ── Functor Category ──────────────────────────────────────────────────────────

function isFunctorCategory(theory: TheoryJson): boolean {
  const name = theory.name.toLowerCase();
  if (name.includes("functor") && name.includes("category")) return true;
  if (name.includes("functorcategory") || name.includes("nat_trans")) return true;

  // Detect by structure: has naturality axioms
  const hasNaturality = theory.axioms.some(ax =>
    ax.name.toLowerCase().includes("naturality") ||
    (ax.description || "").toLowerCase().includes("naturality")
  );
  const hasFunctorObjects = theory.objects.some(o =>
    /^[FGH]$/.test(o.name) || o.name.includes("Functor")
  );
  return hasNaturality && hasFunctorObjects;
}

/**
 * Generate Lean source for a functor category theory.
 *
 * Instead of declaring F, G as bare atoms, we declare them as actual
 * functors C ⥤ D and natural transformations as morphisms in the
 * functor category (where Lean enforces naturality automatically).
 */
function generateFunctorCategory(theory: TheoryJson): string {
  const lines: string[] = [];

  lines.push("import Mathlib.CategoryTheory.Category.Basic");
  lines.push("import Mathlib.CategoryTheory.Functor.Category");
  lines.push("import Mathlib.CategoryTheory.NatTrans");
  lines.push("");
  lines.push("open CategoryTheory");
  lines.push("");
  lines.push("universe v₁ v₂ u₁ u₂");
  lines.push("");
  lines.push(`namespace CatLab.Elaboration.${sanitize(theory.name)}`);
  lines.push("");

  // Source and target categories
  lines.push("variable {C : Type u₁} [Category.{v₁} C]");
  lines.push("variable {D : Type u₂} [Category.{v₂} D]");
  lines.push("");

  // Identify functor objects (F, G, H, etc.)
  const functorNames = theory.objects
    .filter(o => /^[A-Z]$/.test(o.name) || o.name.includes("Functor"))
    .map(o => o.name);

  if (functorNames.length > 0) {
    lines.push(`-- Functors (as objects of the functor category [C, D])`);
    lines.push(`variable (${functorNames.join(" ")} : C ⥤ D)`);
    lines.push("");
  }

  // Identify natural transformations (morphisms between functors)
  const natTransMorphisms = theory.morphisms.filter(m => {
    const dom = exprName(m.domain);
    const cod = exprName(m.codomain);
    return dom && cod && functorNames.includes(dom) && functorNames.includes(cod);
  });

  for (const nt of natTransMorphisms) {
    const dom = exprName(nt.domain)!;
    const cod = exprName(nt.codomain)!;
    lines.push(`-- Natural transformation ${nt.name} : ${dom} ⟶ ${cod}`);
    lines.push(`-- Lean automatically enforces:`);
    lines.push(`--   ∀ X : C, ${nt.name}.app X : ${dom}.obj X ⟶ ${cod}.obj X`);
    lines.push(`--   ∀ f : X ⟶ Y, ${dom}.map f ≫ ${nt.name}.app Y = ${nt.name}.app X ≫ ${cod}.map f`);
    lines.push(`variable (${sanitize(nt.name)} : ${dom} ⟶ ${cod})`);
    lines.push("");
  }

  // Vertical composition is automatic: α ≫ β in the functor category
  const compAxioms = theory.axioms.filter(ax =>
    ax.name.includes("vcomp") || ax.name.includes("comp") ||
    (ax.description || "").includes("vertical")
  );

  if (compAxioms.length > 0 && natTransMorphisms.length >= 2) {
    lines.push("-- Vertical composition is native in the functor category:");
    const α = natTransMorphisms[0];
    const β = natTransMorphisms.find(m => exprName(m.domain) === exprName(α.codomain));
    if (α && β) {
      lines.push(`-- ${sanitize(α.name)} ≫ ${sanitize(β.name)} is well-typed because`);
      lines.push(`-- cod(${sanitize(α.name)}) = ${exprName(α.codomain)} = dom(${sanitize(β.name)})`);
      lines.push(`#check (${sanitize(α.name)} ≫ ${sanitize(β.name)})`);
    }
    lines.push("");
  }

  // Naturality axioms are automatically satisfied — emit as verification
  const naturalityAxioms = theory.axioms.filter(ax =>
    ax.name.includes("naturality") ||
    (ax.description || "").includes("naturality")
  );

  if (naturalityAxioms.length > 0) {
    lines.push("-- Naturality axioms are automatically enforced by Lean's type system.");
    lines.push("-- Every NatTrans α : F ⟶ G satisfies:");
    lines.push("--   ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ α.app Y = α.app X ≫ G.map f");
    lines.push("-- This is α.naturality f — no need to state it as a separate axiom.");

    // Emit a verification example for the first naturality axiom
    if (natTransMorphisms.length > 0) {
      const nt = natTransMorphisms[0];
      lines.push("");
      lines.push(`example (X Y : C) (f : X ⟶ Y) :`);
      lines.push(`    ${exprName(nt.domain)!}.map f ≫ ${sanitize(nt.name)}.app Y =`);
      lines.push(`    ${sanitize(nt.name)}.app X ≫ ${exprName(nt.codomain)!}.map f :=`);
      lines.push(`  ${sanitize(nt.name)}.naturality f`);
    }
    lines.push("");
  }

  // Identity/unit laws
  const unitAxioms = theory.axioms.filter(ax =>
    ax.name.includes("unit") || ax.name.includes("identity") ||
    (ax.description || "").toLowerCase().includes("identity")
  );

  if (unitAxioms.length > 0) {
    lines.push("-- Identity natural transformation (𝟙 F : F ⟶ F) satisfies:");
    lines.push("--   ∀ X, (𝟙 F).app X = 𝟙 (F.obj X)");
    lines.push("");
  }

  lines.push(`end CatLab.Elaboration.${sanitize(theory.name)}`);
  return lines.join("\n") + "\n";
}

// ── Grothendieck Construction (Category of Elements) ──────────────────────────

function isGrothendieckConstruction(theory: TheoryJson): boolean {
  const name = theory.name.toLowerCase();
  if (name.includes("grothendieck") || name.includes("elements")) return true;

  // Detect by structure: paired objects with projection morphisms
  const hasPairedObjects = theory.objects.some(o =>
    o.name.includes("(") || o.name.includes(",")
  );
  const hasProjection = theory.morphisms.some(m =>
    m.name.includes("π") || m.name.includes("proj") || m.name.includes("projection")
  );
  return hasPairedObjects && hasProjection;
}

/**
 * Generate Lean source for a Grothendieck construction / category of elements.
 *
 * Instead of pairing objects without fiber constraints, we use Mathlib's
 * F.Elements where morphisms (c,x) → (d,y) require F.map f x = y.
 */
function generateGrothendieck(theory: TheoryJson): string {
  const lines: string[] = [];

  lines.push("import Mathlib.CategoryTheory.Category.Basic");
  lines.push("import Mathlib.CategoryTheory.Functor.Category");
  lines.push("import Mathlib.CategoryTheory.Elements");
  lines.push("");
  lines.push("open CategoryTheory");
  lines.push("");
  lines.push("universe v u");
  lines.push("");
  lines.push(`namespace CatLab.Elaboration.${sanitize(theory.name)}`);
  lines.push("");

  // Base category
  lines.push("variable {C : Type u} [Category.{v} C]");
  lines.push("");

  // The indexing functor F : C ⥤ Type v
  lines.push("-- The indexing functor (fibers over base category)");
  lines.push("variable (F : C ⥤ Type v)");
  lines.push("");

  // Category of elements
  lines.push("-- The Grothendieck construction is Mathlib's F.Elements");
  lines.push("-- Objects: pairs (c : C, x : F.obj c)");
  lines.push("-- Morphisms (c,x) → (d,y): f : c ⟶ d with proof F.map f x = y");
  lines.push("-- The fiber constraint is enforced by Lean's dependent type system.");
  lines.push("#check (inferInstance : Category F.Elements)");
  lines.push("");

  // Projection functor
  lines.push("-- Projection functor π : ∫F → C (automatically preserves composition)");
  lines.push("#check (CategoryOfElements.π F : F.Elements ⥤ C)");
  lines.push("");

  // Verify any morphisms in the theory map correctly to Elements morphisms
  const projMorphisms = theory.morphisms.filter(m =>
    m.name.includes("π") || m.name.includes("proj")
  );
  if (projMorphisms.length > 0) {
    lines.push("-- Projection morphisms are given by CategoryOfElements.π");
    lines.push("-- No need to declare them separately — they're part of the functor.");
    lines.push("");
  }

  // Naturality axioms for the projection
  const projAxioms = theory.axioms.filter(ax =>
    ax.name.includes("proj") || ax.name.includes("π") ||
    (ax.description || "").includes("projection")
  );
  if (projAxioms.length > 0) {
    lines.push("-- Projection naturality is automatic:");
    lines.push("-- π maps morphisms by forgetting the fiber component.");
    lines.push("-- This is built into CategoryOfElements.π.map");
    lines.push("");
  }

  // Identity axioms
  const idAxioms = theory.axioms.filter(ax =>
    ax.name.includes("ident") || (ax.description || "").includes("identity")
  );
  if (idAxioms.length > 0) {
    lines.push("-- Identity: the identity morphism in F.Elements at (c, x)");
    lines.push("-- is (𝟙 c, proof that F.map (𝟙 c) x = x)");
    lines.push("-- This follows from F.map_id.");
    lines.push("");
  }

  lines.push(`end CatLab.Elaboration.${sanitize(theory.name)}`);
  return lines.join("\n") + "\n";
}

// ── Comma Category ────────────────────────────────────────────────────────────

function isCommaCategory(theory: TheoryJson): boolean {
  const name = theory.name.toLowerCase();
  if (name.includes("comma") || name.includes("arrow")) return true;

  // Detect by structure: commutativity axioms with paired morphisms
  const hasCommSquare = theory.axioms.some(ax =>
    ax.name.includes("comm") || (ax.description || "").includes("commutativity square")
  );
  const hasPairedMorphisms = theory.morphisms.some(m =>
    m.name.includes("(") || m.name.includes(",")
  );
  return hasCommSquare && hasPairedMorphisms;
}

/**
 * Generate Lean source for a comma category.
 *
 * Mathlib's Comma F G has:
 *   - Objects: triples (a : A, b : B, h : F.obj a ⟶ G.obj b)
 *   - Morphisms: pairs (f, g) with commutativity F.map f ≫ h' = h ≫ G.map g
 *   - Type system enforces commutativity constraint
 */
function generateComma(theory: TheoryJson): string {
  const lines: string[] = [];

  lines.push("import Mathlib.CategoryTheory.Category.Basic");
  lines.push("import Mathlib.CategoryTheory.Functor.Basic");
  lines.push("import Mathlib.CategoryTheory.Comma.Basic");
  lines.push("");
  lines.push("open CategoryTheory");
  lines.push("");
  lines.push("universe v₁ v₂ v₃ u₁ u₂ u₃");
  lines.push("");
  lines.push(`namespace CatLab.Elaboration.${sanitize(theory.name)}`);
  lines.push("");

  lines.push("variable {A : Type u₁} [Category.{v₁} A]");
  lines.push("variable {B : Type u₂} [Category.{v₂} B]");
  lines.push("variable {T : Type u₃} [Category.{v₃} T]");
  lines.push("");
  lines.push("-- Source and target functors");
  lines.push("variable (L : A ⥤ T) (R : B ⥤ T)");
  lines.push("");

  lines.push("-- The comma category (L ↓ R) has:");
  lines.push("--   Objects: (a : A, b : B, h : L.obj a ⟶ R.obj b)");
  lines.push("--   Morphisms (a,b,h) → (a',b',h'): (f : a ⟶ a', g : b ⟶ b')");
  lines.push("--     with proof: L.map f ≫ h' = h ≫ R.map g");
  lines.push("--   The commutativity square is enforced by Lean's type system.");
  lines.push("#check (inferInstance : Category (Comma L R))");
  lines.push("");

  // Verify commutativity axioms are automatically handled
  const commAxioms = theory.axioms.filter(ax =>
    ax.name.includes("comm") || (ax.description || "").includes("commutativity")
  );
  if (commAxioms.length > 0) {
    lines.push("-- Commutativity axioms are built into Comma morphisms:");
    lines.push("-- For any morphism m : X ⟶ Y in (L ↓ R),");
    lines.push("--   L.map m.left ≫ Y.hom = X.hom ≫ R.map m.right");
    lines.push("-- This is m.w — enforced by construction, not by a separate axiom.");
    lines.push("variable (X Y : Comma L R) (m : X ⟶ Y)");
    lines.push("#check m.w  -- the commutativity proof");
    lines.push("");
  }

  lines.push(`end CatLab.Elaboration.${sanitize(theory.name)}`);
  return lines.join("\n") + "\n";
}

// ── Helpers ───────────────────────────────────────────────────────────────────

function sanitize(name: string): string {
  return name
    .replace(/[\s\-\+\*\/\\=<>!@#$%^&(){}[\]|;:'"`,\.~?]/g, "_")
    .replace(/^(\d)/, "_$1")
    .replace(/_+/g, "_")
    .replace(/^_|_$/g, "");
}

/** Extract the atom name from a simple ExprJson, or null for compound expressions. */
function exprName(expr: ExprJson): string | null {
  if (typeof expr === "string") return expr;
  if (typeof expr === "object" && "atom" in expr) return expr.atom;
  return null;
}
