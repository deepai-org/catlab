/**
 * Lean/Mathlib Elaboration Pipeline
 *
 * Translates TheoryJson → .lean source file → runs Lean compiler → maps errors
 * back to AST node IDs for structured LLM feedback.
 *
 * This is the "deep path" verifier: it catches semantic errors (type mismatches,
 * invalid compositions, unsatisfiable universal properties) that the fast-path
 * structural checker misses.
 */

import { spawn } from "child_process";
import { writeFile, unlink, mkdtemp } from "fs/promises";
import { join } from "path";
import { tmpdir } from "os";
import type { TheoryJson, ExprJson, MorphismJson, AxiomJson } from "./types";

// ── Result types ──────────────────────────────────────────────────────────────

export type ElaborationStatus =
  | "success" // Fully typed, all axioms proven
  | "structural_error" // Failed fast path (shouldn't reach here)
  | "semantic_error" // Type mismatch, invalid composition, etc.
  | "unverified_axiom"; // Well-typed but aesop_cat couldn't prove it

export interface SourceMappedError {
  astNodeId: string;
  leanLine: number;
  message: string;
  severity: "fatal" | "warning";
}

export interface ElaborationResult {
  status: ElaborationStatus;
  errors: SourceMappedError[];
  diagnostics: string; // Human-readable summary for LLM
  leanSource?: string; // Generated .lean file (for debugging)
}

// ── Source Map ────────────────────────────────────────────────────────────────

interface SourceMapEntry {
  line: number;
  nodeId: string;
  kind: "object" | "morphism" | "axiom" | "header";
}

class SourceMap {
  private entries: SourceMapEntry[] = [];

  add(line: number, nodeId: string, kind: SourceMapEntry["kind"]) {
    this.entries.push({ line, nodeId, kind });
  }

  lookup(line: number): SourceMapEntry | undefined {
    // Find the closest entry at or before this line
    let best: SourceMapEntry | undefined;
    for (const e of this.entries) {
      if (e.line <= line) {
        if (!best || e.line > best.line) best = e;
      }
    }
    return best;
  }
}

// ── Doctrine → Mathlib imports mapping ────────────────────────────────────────

function doctrineImports(doctrine: string): string[] {
  const base = [
    "Mathlib.CategoryTheory.Category.Basic",
    "Mathlib.CategoryTheory.Functor.Basic",
  ];

  const extra: Record<string, string[]> = {
    Category: [],
    MonoidalCategory: [
      "Mathlib.CategoryTheory.Monoidal.Category",
    ],
    BraidedMonoidal: [
      "Mathlib.CategoryTheory.Monoidal.Category",
      "Mathlib.CategoryTheory.Monoidal.Braided",
    ],
    SymmetricMonoidal: [
      "Mathlib.CategoryTheory.Monoidal.Category",
      "Mathlib.CategoryTheory.Monoidal.Braided",
    ],
    CartesianCategory: [
      "Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts",
      "Mathlib.CategoryTheory.Limits.Shapes.Terminal",
    ],
    CartesianClosed: [
      "Mathlib.CategoryTheory.Closed.Cartesian",
    ],
    Abelian: [
      "Mathlib.CategoryTheory.Abelian.Basic",
    ],
    Topos: [
      "Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts",
      "Mathlib.CategoryTheory.Limits.Shapes.Terminal",
      "Mathlib.CategoryTheory.Closed.Cartesian",
    ],
    ElementaryTopos: [
      "Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts",
      "Mathlib.CategoryTheory.Limits.Shapes.Terminal",
      "Mathlib.CategoryTheory.Closed.Cartesian",
    ],
    LawvereTheory: [
      "Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts",
      "Mathlib.CategoryTheory.Limits.Shapes.Terminal",
    ],
    FinitelyComplete: [
      "Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts",
      "Mathlib.CategoryTheory.Limits.Shapes.Equalizers",
      "Mathlib.CategoryTheory.Limits.Shapes.Terminal",
    ],
  };

  return [...new Set([...base, ...(extra[doctrine] || [])])];
}

// ── Expr translation ──────────────────────────────────────────────────────────

/**
 * Translate an ExprJson into a Lean 4 expression string.
 *
 * Context: we're generating expressions in a Lean file where objects are
 * variables of type `C` and morphisms are `X ⟶ Y`. The translation depends
 * on whether we're in a "type" context (object expressions) or a "term"
 * context (morphism expressions).
 */
function exprToLeanType(expr: ExprJson, objects: Set<string>): string {
  if (typeof expr === "string") {
    if (expr === "terminal") return "⊤_ C";
    if (expr === "initial") return "⊥_ C";
    if (expr === "unit") return "𝟙_ C";
    return expr; // atom → variable name
  }
  if ("atom" in expr) return expr.atom;
  if ("prod" in expr) return `(${exprToLeanType(expr.prod[0], objects)} ⨯ ${exprToLeanType(expr.prod[1], objects)})`;
  if ("coprod" in expr) return `(${exprToLeanType(expr.coprod[0], objects)} ⨿ ${exprToLeanType(expr.coprod[1], objects)})`;
  if ("tensor" in expr) return `(${exprToLeanType(expr.tensor[0], objects)} ⊗ ${exprToLeanType(expr.tensor[1], objects)})`;
  if ("hom" in expr) return `(${exprToLeanType(expr.hom[0], objects)} ⟶ ${exprToLeanType(expr.hom[1], objects)})`;
  // Fallback: render as sorry for unhandled cases
  return "sorry";
}

/**
 * Translate a morphism expression (comp, id, atom) into Lean term syntax.
 * In Mathlib, composition is `f ≫ g` (diagrammatic order).
 */
function exprToLeanTerm(expr: ExprJson, objects: Set<string>): string {
  if (typeof expr === "string") {
    if (expr === "unit" || expr === "terminal" || expr === "initial") return `sorry /- ${expr} -/`;
    return expr;
  }
  if ("atom" in expr) return expr.atom;
  if ("comp" in expr) return `(${exprToLeanTerm(expr.comp[0], objects)} ≫ ${exprToLeanTerm(expr.comp[1], objects)})`;
  if ("id" in expr) return `(𝟙 ${exprToLeanType(expr.id, objects)})`;
  if ("prod" in expr) return `CategoryTheory.Limits.prod.lift ${exprToLeanTerm(expr.prod[0], objects)} ${exprToLeanTerm(expr.prod[1], objects)}`;
  if ("tensor" in expr) return `(${exprToLeanTerm(expr.tensor[0], objects)} ⊗ ${exprToLeanTerm(expr.tensor[1], objects)})`;
  return `sorry /- unhandled expr -/`;
}

// ── Doctrine → Lean context ──────────────────────────────────────────────────

interface DoctrineContext {
  /** Extra `variable` or `instance` lines */
  extraContext: string[];
  /** Whether this doctrine uses monoidal tensor */
  hasTensor: boolean;
  /** Whether this doctrine has products */
  hasProducts: boolean;
}

function doctrineToContext(doctrine: string): DoctrineContext {
  const contexts: Record<string, DoctrineContext> = {
    Category: { extraContext: [], hasTensor: false, hasProducts: false },
    MonoidalCategory: {
      extraContext: ["variable [MonoidalCategory C]"],
      hasTensor: true, hasProducts: false,
    },
    BraidedMonoidal: {
      extraContext: [
        "variable [MonoidalCategory C]",
        "variable [BraidedCategory C]",
      ],
      hasTensor: true, hasProducts: false,
    },
    SymmetricMonoidal: {
      extraContext: [
        "variable [MonoidalCategory C]",
        "variable [SymmetricCategory C]",
      ],
      hasTensor: true, hasProducts: false,
    },
    CartesianCategory: {
      extraContext: [
        "variable [Limits.HasBinaryProducts C]",
        "variable [Limits.HasTerminal C]",
      ],
      hasTensor: false, hasProducts: true,
    },
    LawvereTheory: {
      extraContext: [
        "variable [Limits.HasBinaryProducts C]",
        "variable [Limits.HasTerminal C]",
      ],
      hasTensor: false, hasProducts: true,
    },
    Abelian: {
      extraContext: ["variable [Abelian C]"],
      hasTensor: false, hasProducts: true,
    },
  };

  return contexts[doctrine] ?? { extraContext: [], hasTensor: false, hasProducts: false };
}

// ── Main translator ───────────────────────────────────────────────────────────

export interface ElaborationOptions {
  /** Project root containing lakefile.toml. Used to resolve Mathlib imports. */
  projectRoot: string;
  /** Timeout for Lean compilation in ms. Default: 60000 */
  timeoutMs?: number;
  /** Keep generated .lean file for debugging. Default: false */
  keepFile?: boolean;
}

/**
 * Translate a TheoryJson into a Lean 4 source string with Mathlib imports.
 * Returns the source and a source map for error attribution.
 */
export function theoryToLean(theory: TheoryJson): { source: string; sourceMap: SourceMap } {
  const sm = new SourceMap();
  const lines: string[] = [];
  let lineNum = 1;

  function emit(line: string, nodeId?: string, kind?: SourceMapEntry["kind"]) {
    if (nodeId && kind) sm.add(lineNum, nodeId, kind);
    lines.push(line);
    lineNum++;
  }

  function emitBlank() { emit(""); }

  const doctrine = theory.doctrine || "Category";
  const imports = doctrineImports(doctrine);
  const ctx = doctrineToContext(doctrine);

  // ── Header ──────────────────────────────────────────────────────────────
  for (const imp of imports) {
    emit(`import ${imp}`, "header", "header");
  }
  emitBlank();
  emit("open CategoryTheory");
  emitBlank();
  emit("universe v u");
  emitBlank();

  // ── Namespace ───────────────────────────────────────────────────────────
  const ns = sanitizeName(theory.name);
  emit(`namespace CatLab.Elaboration.${ns}`);
  emitBlank();

  // ── Category context ────────────────────────────────────────────────────
  emit("variable {C : Type u} [Category.{v} C]");
  for (const extra of ctx.extraContext) {
    emit(extra);
  }
  emitBlank();

  // ── Objects as variables ────────────────────────────────────────────────
  // Avoid shadowing the category type variable `C`
  const reserved = new Set(["C", "v", "u"]);
  const objectNames = new Set(theory.objects.map(o => {
    const s = sanitizeName(o.name);
    return reserved.has(s) ? s + "₀" : s;
  }));
  const objectNameMap = new Map(theory.objects.map(o => {
    const s = sanitizeName(o.name);
    return [o.name, reserved.has(s) ? s + "₀" : s];
  }));

  if (theory.objects.length > 0) {
    const objVars = [...objectNames].join(" ");
    emit(`variable (${objVars} : C)`, "objects", "object");
    emitBlank();
  }

  // ── Morphisms as variables ──────────────────────────────────────────────
  for (const mor of theory.morphisms) {
    const name = sanitizeName(mor.name);
    const dom = exprToLeanType(mor.domain, objectNames);
    const cod = exprToLeanType(mor.codomain, objectNames);
    emit(`variable (${name} : ${dom} ⟶ ${cod})`, `morphism:${mor.name}`, "morphism");
  }
  if (theory.morphisms.length > 0) emitBlank();

  // ── Axioms as lemmas with aesop_cat ─────────────────────────────────────
  for (const ax of theory.axioms) {
    const name = sanitizeName(ax.name);
    const lhs = exprToLeanTerm(ax.lhs, objectNames);
    const rhs = exprToLeanTerm(ax.rhs, objectNames);

    emit(`-- Axiom: ${ax.description || ax.name}`, `axiom:${ax.name}`, "axiom");
    emit(`lemma ${name} : ${lhs} = ${rhs} := by`);
    emit(`  aesop_cat`);
    emitBlank();
  }

  // ── Close namespace ─────────────────────────────────────────────────────
  emit(`end CatLab.Elaboration.${ns}`);

  return { source: lines.join("\n") + "\n", sourceMap: sm };
}

function sanitizeName(name: string): string {
  // Lean 4 supports Unicode identifiers (Greek letters, math symbols, etc.)
  // Only replace characters that are actually invalid in Lean identifiers:
  // spaces, operators, punctuation that isn't part of identifiers
  return name
    .replace(/[\s\-\+\*\/\\=<>!@#$%^&(){}[\]|;:'"`,\.~?]/g, "_")
    .replace(/^(\d)/, "_$1")
    .replace(/_+/g, "_")        // collapse multiple underscores
    .replace(/^_|_$/g, "");     // trim leading/trailing underscores (if safe)
}

// ── Lean compiler invocation ──────────────────────────────────────────────────

interface LeanDiagnostic {
  fileName: string;
  severity: "error" | "warning" | "information";
  range: {
    start: { line: number; character: number };
    end: { line: number; character: number };
  };
  message: string;
}

/**
 * Run `lean` on a generated .lean file and collect JSON diagnostics.
 *
 * We use `lean --run` with `--json` to get structured error output.
 * The file is placed in a temp directory but imports resolve via the project's
 * lakefile.toml (passed via LEAN_PATH or --threads).
 */
async function runLean(
  source: string,
  opts: ElaborationOptions,
): Promise<{ diagnostics: LeanDiagnostic[]; exitCode: number }> {
  const tmpDir = await mkdtemp(join(tmpdir(), "catlab-elab-"));
  const filePath = join(tmpDir, "Elaboration.lean");
  await writeFile(filePath, source, "utf-8");

  const timeout = opts.timeoutMs ?? 60000;

  // Get LEAN_PATH from lake env
  const leanPath = await getLeanPath(opts.projectRoot);

  return new Promise((resolve) => {
    const diagnostics: LeanDiagnostic[] = [];
    let stderr = "";

    const proc = spawn("lean", ["--json", filePath], {
      cwd: opts.projectRoot,
      env: { ...process.env, LEAN_PATH: leanPath },
      timeout,
    });

    // Lean --json outputs diagnostics to both stdout and stderr
    const handleData = (data: Buffer) => {
      const text = data.toString();
      for (const line of text.split("\n").filter(Boolean)) {
        try {
          const parsed = JSON.parse(line);
          if (parsed.severity) {
            // Normalize: ensure range exists with defaults
            if (!parsed.pos) parsed.pos = { line: 0, column: 0 };
            if (!parsed.endPos) parsed.endPos = parsed.pos;
            // Convert Lean's pos/endPos to range format
            const diag: LeanDiagnostic = {
              fileName: parsed.fileName || filePath,
              severity: parsed.severity,
              range: {
                start: { line: parsed.pos.line, character: parsed.pos.column },
                end: { line: parsed.endPos.line, character: parsed.endPos.column },
              },
              message: parsed.data || parsed.message || JSON.stringify(parsed),
            };
            diagnostics.push(diag);
          }
        } catch {
          // skip non-JSON output
        }
      }
    };

    proc.stdout.on("data", handleData);
    proc.stderr.on("data", handleData);

    proc.on("close", (code) => {
      if (!opts.keepFile) {
        unlink(filePath).catch(() => {});
      }
      resolve({ diagnostics, exitCode: code ?? 1 });
    });

    proc.on("error", (err) => {
      resolve({
        diagnostics: [{
          fileName: filePath,
          severity: "error",
          range: { start: { line: 0, character: 0 }, end: { line: 0, character: 0 } },
          message: `Failed to run lean: ${err.message}`,
        }],
        exitCode: 1,
      });
    });
  });
}

async function getLeanPath(projectRoot: string): Promise<string> {
  return new Promise((resolve) => {
    const proc = spawn("lake", ["env", "bash", "-c", "echo $LEAN_PATH"], {
      cwd: projectRoot,
      timeout: 30000,
    });
    let stdout = "";
    proc.stdout.on("data", (d: Buffer) => { stdout += d.toString(); });
    proc.on("close", () => {
      resolve(stdout.trim());
    });
    proc.on("error", () => resolve(""));
  });
}

// ── Diagnostic classification ─────────────────────────────────────────────────

function classifyDiagnostic(
  diag: LeanDiagnostic,
  sourceMap: SourceMap,
): SourceMappedError {
  const entry = sourceMap.lookup(diag.range.start.line + 1); // Lean uses 0-indexed lines
  const nodeId = entry?.nodeId ?? "unknown";

  // Classify: type mismatch / synthesis failure = fatal semantic error
  //          tactic failure (aesop) = unverified axiom (warning)
  const msg = diag.message;
  const isAesopFailure =
    msg.includes("aesop") ||
    msg.includes("tactic") && msg.includes("failed");
  const isSorry = msg.includes("declaration uses 'sorry'");

  if (isAesopFailure || isSorry) {
    return {
      astNodeId: nodeId,
      leanLine: diag.range.start.line + 1,
      message: `Axiom is well-typed but could not be automatically verified: ${summarizeMessage(msg)}`,
      severity: "warning",
    };
  }

  return {
    astNodeId: nodeId,
    leanLine: diag.range.start.line + 1,
    message: summarizeMessage(msg),
    severity: "fatal",
  };
}

function summarizeMessage(msg: string): string {
  // Truncate long Lean error messages for LLM consumption
  const firstLine = msg.split("\n")[0];
  if (firstLine.length > 200) return firstLine.slice(0, 200) + "…";
  // Include up to 3 lines for context
  const lines = msg.split("\n").slice(0, 3);
  return lines.join(" | ");
}

// ── Public API ────────────────────────────────────────────────────────────────

/**
 * Elaborate a TheoryJson against Lean/Mathlib.
 *
 * 1. Translates TheoryJson → .lean source with source map
 * 2. Invokes the Lean compiler
 * 3. Maps diagnostics back to AST node IDs
 * 4. Returns structured ElaborationResult
 */
export async function elaborate(
  theory: TheoryJson,
  opts: ElaborationOptions,
): Promise<ElaborationResult> {
  // Step 1: Generate Lean source
  const { source, sourceMap } = theoryToLean(theory);

  // Step 2: Run Lean
  const { diagnostics, exitCode } = await runLean(source, opts);

  // Step 3: Classify diagnostics
  const errors: SourceMappedError[] = diagnostics
    .filter(d => d.severity === "error" || d.severity === "warning")
    .map(d => classifyDiagnostic(d, sourceMap));

  const fatalErrors = errors.filter(e => e.severity === "fatal");
  const warnings = errors.filter(e => e.severity === "warning");

  // Step 4: Determine status
  let status: ElaborationStatus;
  if (fatalErrors.length > 0) {
    status = "semantic_error";
  } else if (warnings.length > 0) {
    status = "unverified_axiom";
  } else if (exitCode === 0) {
    status = "success";
  } else {
    status = "semantic_error";
  }

  // Step 5: Build diagnostics string for LLM
  const diagnosticLines: string[] = [];
  if (status === "success") {
    diagnosticLines.push("All types and axioms verified by Lean/Mathlib.");
  }
  for (const err of fatalErrors) {
    diagnosticLines.push(`[SEMANTIC ERROR in ${err.astNodeId}] ${err.message}`);
  }
  for (const warn of warnings) {
    diagnosticLines.push(`[UNVERIFIED in ${warn.astNodeId}] ${warn.message}`);
  }

  return {
    status,
    errors,
    diagnostics: diagnosticLines.join("\n"),
    leanSource: source,
  };
}

/**
 * Format an ElaborationResult into LLM-readable feedback.
 */
export function formatElaborationFeedback(result: ElaborationResult): string {
  if (result.status === "success") {
    return "✓ Deep verification passed: all types and axioms verified by Lean/Mathlib.";
  }

  const parts: string[] = [];

  if (result.status === "semantic_error") {
    parts.push("✗ Deep verification FAILED: Lean/Mathlib found type errors in your theory.\n");
  } else if (result.status === "unverified_axiom") {
    parts.push("⚠ Deep verification PARTIAL: your theory is well-typed, but some axioms could not be automatically proven.\n");
  }

  parts.push(result.diagnostics);

  if (result.status === "unverified_axiom") {
    parts.push("\nYou can either (A) leave unverified axioms as assumptions, or (B) break them into smaller intermediate lemmas.");
  }

  return parts.join("\n");
}
