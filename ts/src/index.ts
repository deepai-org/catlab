#!/usr/bin/env node
/**
 * catlab-solve — CLI entry point for the generalized solver.
 *
 * Supports multiple problem types:
 *   catlab-solve <target> <forwardOp>                              # inverse (default)
 *   catlab-solve --problem inverse --target T --op F               # explicit inverse
 *   catlab-solve --problem pushout-complement --base B --target T
 *   catlab-solve --problem extension --base B --property P
 *   catlab-solve --problem multi --objectives "T1:op1,T2:op2"
 *   catlab-solve --problem fixed-point --target T --op F
 *   catlab-solve list                                              # show theories
 *
 * Set ANTHROPIC_API_KEY in your environment.
 * Output (stdout): final result JSON
 * Logs (stderr):   round-by-round progress
 */

import * as fs from "fs";
import { CatlabClient } from "./client";
import { LLMClient } from "./llm";
import { GenericSolver } from "./solver";
import {
  InverseVerifier,
  PushoutComplementVerifier,
  ExtensionVerifier,
  MultiObjectiveVerifier,
  FixedPointVerifier,
  FactorizationVerifier,
  InterpolationVerifier,
  OptimizationVerifier,
  PullbackComplementVerifier,
  SimplificationVerifier,
  ModelFindingVerifier,
  SubobjectVerifier,
  SynthesisVerifier,
  QuotientVerifier,
  DecompositionVerifier,
  RelaxationVerifier,
  CatalystVerifier,
  ComposeVerifier,
} from "./verifiers";
import type { Verifier, SolverOptions } from "./types";
import { DeepVerifier } from "./deep-verifier";

// ── CLI argument parsing ──────────────────────────────────────────────────────

function usage(): never {
  console.error(`
Usage: catlab-solve <targetTheory> <forwardOp> [options]    (inverse problem shorthand)
       catlab-solve --problem <type> [problem-args] [options]

Problem types:
  inverse               find X such that op(X) ≅ target  (default)
  pushout-complement    find X such that pushout(base, X) ≅ target
  pullback-complement   find X such that pullback(base, X) ≅ target
  extension             find X extending base with property P
  multi                 find X such that op₁(X)≅T₁ ∧ op₂(X)≅T₂
  fixed-point           find X such that op(X) ≅ X
  factorization         find (X,Y) such that X⊗Y ≅ target
  interpolation         find X with base ↪ X → target
  optimization          find X minimizing cost subject to op(X)≅target
  simplify              find minimal X ≅ target
  model-finding         generate a concrete instance of a theory
  subobject             find sub-theory of target satisfying property P
  synthesis             find morphism composition source → target in theory
  quotient              find minimal quotient of base satisfying property P
  decompose             decompose target into independent components
  relax                 find X closest to target satisfying property P
  catalyst              find C such that source⊗C → target⊗C
  compose               find X satisfying ALL constraints simultaneously

Problem arguments:
  --target <name>       Target theory name (or use --target-file)
  --op <name>           Forward operator (for inverse / fixed-point)
  --base <name>         Base theory name (or use --base-file)
  --property <name>     Property to check (for extension / subobject)
  --objectives <spec>   Comma-separated target:op pairs (for multi)
  --constraints <spec>  Plus-separated constraint specs (for compose)
  --source <name>       Source object (for synthesis, or use --source-file)

Theory file arguments (register user-defined theories from JSON files):
  --target-file <path>  Load target theory from a JSON file
  --base-file <path>    Load base theory from a JSON file
  --source-file <path>  Load source theory from a JSON file

General options:
  --style <str>         Style guidance / hints for the LLM
  --rounds <n>          Max LLM rounds (default: 5)
  --timeout <ms>        Per-Lean-request timeout in ms (default: 30000)
  --lean <path>         Path to catlab repo root
  --deep                Enable deep Lean/Mathlib verification (two-tier)
  --deep-timeout <ms>   Lean compilation timeout for deep path (default: 60000)

Environment:
  ANTHROPIC_API_KEY     Required — your Anthropic API key

Examples:
  catlab-solve Monoid identity
  catlab-solve Monoid opposite --style "keep it simple" --rounds 3
  catlab-solve --problem pushout-complement --base Monoid --target Ring
  catlab-solve --problem extension --base Monoid --property "has_inverses"
  catlab-solve --problem multi --objectives "Monoid:opposite,Monoid:mirror"
  catlab-solve --problem fixed-point --target Monoid --op opposite
  catlab-solve --problem compose --constraints "inverse:Monoid:opposite+extension:Monoid:has_inverses"
  catlab-solve list
`);
  process.exit(1);
}

async function listTheories(client: CatlabClient): Promise<void> {
  const res = await client.requestOrThrow({ command: "list_theories" });
  console.log("Available theories:");
  (res.theories ?? []).forEach((name) => console.log(`  ${name}`));
}

/**
 * Parse a single constraint spec like "inverse:Monoid:opposite" into a labeled verifier.
 */
function parseConstraint(spec: string): { label: string; verifier: Verifier } {
  const parts = spec.split(":");
  const type = parts[0];
  switch (type) {
    case "inverse":
      if (parts.length < 3) throw new Error(`inverse needs target:op, got "${spec}"`);
      return { label: `inverse(${parts[1]},${parts[2]})`, verifier: new InverseVerifier(parts[1], parts[2]) };
    case "fixed-point":
      if (parts.length < 3) throw new Error(`fixed-point needs target:op, got "${spec}"`);
      return { label: `fixed-point(${parts[1]},${parts[2]})`, verifier: new FixedPointVerifier(parts[1], parts[2]) };
    case "pushout-complement":
      if (parts.length < 3) throw new Error(`pushout-complement needs base:target, got "${spec}"`);
      return { label: `pc(${parts[1]},${parts[2]})`, verifier: new PushoutComplementVerifier(parts[1], parts[2]) };
    case "pullback-complement":
      if (parts.length < 3) throw new Error(`pullback-complement needs base:target, got "${spec}"`);
      return { label: `pbc(${parts[1]},${parts[2]})`, verifier: new PullbackComplementVerifier(parts[1], parts[2]) };
    case "extension":
      if (parts.length < 3) throw new Error(`extension needs base:property, got "${spec}"`);
      return { label: `ext(${parts[1]},${parts[2]})`, verifier: new ExtensionVerifier(parts[1], parts[2]) };
    case "interpolation":
      if (parts.length < 3) throw new Error(`interpolation needs base:target, got "${spec}"`);
      return { label: `interp(${parts[1]},${parts[2]})`, verifier: new InterpolationVerifier(parts[1], parts[2]) };
    case "simplify":
      if (parts.length < 2) throw new Error(`simplify needs target, got "${spec}"`);
      return { label: `simplify(${parts[1]})`, verifier: new SimplificationVerifier(parts[1]) };
    case "subobject":
      if (parts.length < 3) throw new Error(`subobject needs target:property, got "${spec}"`);
      return { label: `sub(${parts[1]},${parts[2]})`, verifier: new SubobjectVerifier(parts[1], parts[2]) };
    case "quotient":
      if (parts.length < 3) throw new Error(`quotient needs base:property, got "${spec}"`);
      return { label: `quot(${parts[1]},${parts[2]})`, verifier: new QuotientVerifier(parts[1], parts[2]) };
    case "relax":
      if (parts.length < 3) throw new Error(`relax needs target:property, got "${spec}"`);
      return { label: `relax(${parts[1]},${parts[2]})`, verifier: new RelaxationVerifier(parts[1], parts[2]) };
    case "catalyst":
      if (parts.length < 3) throw new Error(`catalyst needs source:target, got "${spec}"`);
      return { label: `catalyst(${parts[1]},${parts[2]})`, verifier: new CatalystVerifier(parts[1], parts[2]) };
    case "decompose":
      if (parts.length < 2) throw new Error(`decompose needs target, got "${spec}"`);
      return { label: `decompose(${parts[1]})`, verifier: new DecompositionVerifier(parts[1]) };
    default:
      throw new Error(`Unknown constraint type: "${type}"`);
  }
}

function buildVerifier(args: string[]): {
  verifier: Verifier;
  solverOpts: SolverOptions;
  repoRoot?: string;
  deep?: boolean;
  deepTimeoutMs?: number;
  theoryFiles: { targetFile?: string; baseFile?: string; sourceFile?: string };
} {
  // Shorthand: catlab-solve <target> <forwardOp> [options]
  if (args.length >= 2 && !args[0].startsWith("--")) {
    const targetName = args[0];
    const forwardOp = args[1];
    const solverOpts: SolverOptions = {};
    let repoRoot: string | undefined;
    let deep = false;
    let deepTimeoutMs: number | undefined;

    for (let i = 2; i < args.length; i++) {
      switch (args[i]) {
        case "--style":        solverOpts.stylePrompt = args[++i]; break;
        case "--rounds":       solverOpts.maxRounds = parseInt(args[++i], 10); break;
        case "--timeout":      solverOpts.leanTimeoutMs = parseInt(args[++i], 10); break;
        case "--lean":         repoRoot = args[++i]; break;
        case "--reflect":      solverOpts.reflect = true; break;
        case "--deep":         deep = true; break;
        case "--deep-timeout": deepTimeoutMs = parseInt(args[++i], 10); break;
        default: console.error(`Unknown option: ${args[i]}`); usage();
      }
    }

    return {
      verifier: new InverseVerifier(targetName, forwardOp),
      solverOpts,
      repoRoot,
      deep,
      deepTimeoutMs,
      theoryFiles: {},
    };
  }

  // Full form: --problem <type> [args]
  let problemType: string | undefined;
  let target: string | undefined;
  let op: string | undefined;
  let base: string | undefined;
  let property: string | undefined;
  let objectivesStr: string | undefined;
  let constraintsStr: string | undefined;
  let source: string | undefined;
  let repoRoot: string | undefined;
  let deep = false;
  let deepTimeoutMs: number | undefined;
  let targetFile: string | undefined;
  let baseFile: string | undefined;
  let sourceFile: string | undefined;
  const solverOpts: SolverOptions = {};

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case "--problem":      problemType = args[++i]; break;
      case "--target":       target = args[++i]; break;
      case "--op":           op = args[++i]; break;
      case "--base":         base = args[++i]; break;
      case "--property":     property = args[++i]; break;
      case "--objectives":   objectivesStr = args[++i]; break;
      case "--constraints":  constraintsStr = args[++i]; break;
      case "--source":       source = args[++i]; break;
      case "--style":        solverOpts.stylePrompt = args[++i]; break;
      case "--rounds":       solverOpts.maxRounds = parseInt(args[++i], 10); break;
      case "--timeout":      solverOpts.leanTimeoutMs = parseInt(args[++i], 10); break;
      case "--lean":         repoRoot = args[++i]; break;
      case "--reflect":      solverOpts.reflect = true; break;
      case "--deep":         deep = true; break;
      case "--deep-timeout": deepTimeoutMs = parseInt(args[++i], 10); break;
      case "--target-file":  targetFile = args[++i]; break;
      case "--base-file":    baseFile = args[++i]; break;
      case "--source-file":  sourceFile = args[++i]; break;
      default: console.error(`Unknown option: ${args[i]}`); usage();
    }
  }

  let verifier: Verifier;
  switch (problemType) {
    case "inverse":
      if (!target || !op) { console.error("--target and --op required for inverse"); usage(); }
      verifier = new InverseVerifier(target, op);
      break;
    case "pushout-complement":
      if (!base || !target) { console.error("--base and --target required for pushout-complement"); usage(); }
      verifier = new PushoutComplementVerifier(base, target);
      break;
    case "extension":
      if (!base || !property) { console.error("--base and --property required for extension"); usage(); }
      verifier = new ExtensionVerifier(base, property);
      break;
    case "multi": {
      if (!objectivesStr) { console.error("--objectives required for multi"); usage(); }
      const objectives = objectivesStr.split(",").map((s) => {
        const [t, o] = s.split(":");
        if (!t || !o) { console.error(`Invalid objective format: "${s}" (expected target:op)`); usage(); }
        return { target: t, forwardOp: o };
      });
      verifier = new MultiObjectiveVerifier(objectives);
      break;
    }
    case "fixed-point":
      if (!target || !op) { console.error("--target and --op required for fixed-point"); usage(); }
      verifier = new FixedPointVerifier(target, op);
      break;
    case "factorization":
      if (!target) { console.error("--target required for factorization"); usage(); }
      verifier = new FactorizationVerifier(target, op ?? "tensor");
      break;
    case "interpolation":
      if (!base || !target) { console.error("--base and --target required for interpolation"); usage(); }
      verifier = new InterpolationVerifier(base, target);
      break;
    case "optimization":
      if (!target || !op || !property) { console.error("--target, --op, and --property required for optimization"); usage(); }
      verifier = new OptimizationVerifier(op, target, property);
      break;
    case "pullback-complement":
      if (!base || !target) { console.error("--base and --target required for pullback-complement"); usage(); }
      verifier = new PullbackComplementVerifier(base, target);
      break;
    case "simplify":
      if (!target) { console.error("--target required for simplify"); usage(); }
      verifier = new SimplificationVerifier(target);
      break;
    case "model-finding":
      if (!target) { console.error("--target required for model-finding"); usage(); }
      verifier = new ModelFindingVerifier(target);
      break;
    case "subobject":
      if (!target || !property) { console.error("--target and --property required for subobject"); usage(); }
      verifier = new SubobjectVerifier(target, property);
      break;
    case "synthesis":
      if (!target || !source || !base) { console.error("--base (theory), --source, and --target required for synthesis"); usage(); }
      verifier = new SynthesisVerifier(base, source, target);
      break;
    case "quotient":
      if (!base || !property) { console.error("--base and --property required for quotient"); usage(); }
      verifier = new QuotientVerifier(base, property);
      break;
    case "decompose":
      if (!target) { console.error("--target required for decompose"); usage(); }
      verifier = new DecompositionVerifier(target);
      break;
    case "relax":
      if (!target || !property) { console.error("--target and --property required for relax"); usage(); }
      verifier = new RelaxationVerifier(target, property);
      break;
    case "catalyst":
      if (!source || !target) { console.error("--source and --target required for catalyst"); usage(); }
      verifier = new CatalystVerifier(source, target);
      break;
    case "compose": {
      if (!constraintsStr) { console.error("--constraints required for compose"); usage(); }
      const constraints = constraintsStr.split("+").map((s) => parseConstraint(s.trim()));
      verifier = new ComposeVerifier(constraints);
      break;
    }
    default:
      console.error(`Unknown problem type: ${problemType}`);
      usage();
  }

  return { verifier, solverOpts, repoRoot, deep, deepTimeoutMs, theoryFiles: { targetFile, baseFile, sourceFile } };
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);

  if (args.length === 0 || args[0] === "--help" || args[0] === "-h") usage();

  if (!process.env.ANTHROPIC_API_KEY) {
    console.error("Error: ANTHROPIC_API_KEY environment variable is not set.");
    process.exit(1);
  }

  // Handle "list" command
  if (args[0] === "list") {
    const client = new CatlabClient();
    await listTheories(client);
    client.kill();
    return;
  }

  const { verifier: baseVerifier, solverOpts, repoRoot, deep, deepTimeoutMs, theoryFiles } = buildVerifier(args);

  // Wrap with deep verification if --deep flag is set
  const projectRoot = repoRoot ?? process.cwd();
  const verifier: Verifier = deep
    ? new DeepVerifier(baseVerifier, {
        deepVerification: true,
        projectRoot,
        leanTimeoutMs: deepTimeoutMs,
      })
    : baseVerifier;

  if (deep) {
    console.error(`[solver:INIT] Deep verification enabled (Lean/Mathlib, timeout=${deepTimeoutMs ?? 60000}ms)`);
  }

  // ── Run the solver ────────────────────────────────────────────────────────
  const catlab = new CatlabClient(repoRoot);

  // Register any file-based theories before solving
  for (const filePath of [theoryFiles.targetFile, theoryFiles.baseFile, theoryFiles.sourceFile]) {
    if (!filePath) continue;
    const raw = fs.readFileSync(filePath, "utf-8");
    const theory = JSON.parse(raw);
    console.error(`[solver:INIT] Registering theory "${theory.name}" from ${filePath}`);
    await catlab.defineTheory(theory);
  }
  const llm = new LLMClient();
  const solver = new GenericSolver(catlab, llm, verifier);

  let exitCode = 0;
  try {
    const result = await solver.solve(solverOpts);
    console.log(JSON.stringify(result, null, 2));

    if (!result.success) {
      console.error(`\n[solver] Failed after ${result.rounds} rounds.`);
      if (result.history.length > 0) {
        const last = result.history[result.history.length - 1];
        const name = (last.payload as Record<string, unknown>)?.name ?? "?";
        console.error(`[solver] Best attempt: "${name}"`);
        console.error(`[solver] Final status: ${last.result.verificationStatus}`);
      }
      exitCode = 1;
    }
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    console.error(`[solver] Fatal error: ${msg}`);
    exitCode = 2;
  } finally {
    catlab.kill();
  }

  process.exit(exitCode);
}

main().catch((err) => {
  console.error(err);
  process.exit(2);
});
