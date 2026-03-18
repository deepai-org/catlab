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
} from "./verifiers";
import type { Verifier, SolverOptions } from "./types";

// ── CLI argument parsing ──────────────────────────────────────────────────────

function usage(): never {
  console.error(`
Usage: catlab-solve <targetTheory> <forwardOp> [options]    (inverse problem shorthand)
       catlab-solve --problem <type> [problem-args] [options]

Problem types:
  inverse               find X such that op(X) ≅ target  (default)
  pushout-complement    find X such that pushout(base, X) ≅ target
  extension             find X extending base with property P
  multi                 find X such that op₁(X)≅T₁ ∧ op₂(X)≅T₂
  fixed-point           find X such that op(X) ≅ X
  factorization         find (X,Y) such that X⊗Y ≅ target
  interpolation         find X with base ↪ X → target
  optimization          find X minimizing cost subject to op(X)≅target

Problem arguments:
  --target <name>       Target theory name
  --op <name>           Forward operator (for inverse / fixed-point)
  --base <name>         Base theory (for pushout-complement / extension)
  --property <name>     Property to check (for extension)
  --objectives <spec>   Comma-separated target:op pairs (for multi)

General options:
  --style <str>         Style guidance / hints for the LLM
  --rounds <n>          Max LLM rounds (default: 5)
  --timeout <ms>        Per-Lean-request timeout in ms (default: 30000)
  --lean <path>         Path to catlab repo root

Environment:
  ANTHROPIC_API_KEY     Required — your Anthropic API key

Examples:
  catlab-solve Monoid identity
  catlab-solve Monoid opposite --style "keep it simple" --rounds 3
  catlab-solve --problem pushout-complement --base Monoid --target Ring
  catlab-solve --problem extension --base Monoid --property "has_inverses"
  catlab-solve --problem multi --objectives "Monoid:opposite,Monoid:mirror"
  catlab-solve --problem fixed-point --target Monoid --op opposite
  catlab-solve list
`);
  process.exit(1);
}

async function listTheories(client: CatlabClient): Promise<void> {
  const res = await client.requestOrThrow({ command: "list_theories" });
  console.log("Available theories:");
  (res.theories ?? []).forEach((name) => console.log(`  ${name}`));
}

function buildVerifier(args: string[]): {
  verifier: Verifier;
  solverOpts: SolverOptions;
  repoRoot?: string;
} {
  // Shorthand: catlab-solve <target> <forwardOp> [options]
  if (args.length >= 2 && !args[0].startsWith("--")) {
    const targetName = args[0];
    const forwardOp = args[1];
    const solverOpts: SolverOptions = {};
    let repoRoot: string | undefined;

    for (let i = 2; i < args.length; i++) {
      switch (args[i]) {
        case "--style":   solverOpts.stylePrompt = args[++i]; break;
        case "--rounds":  solverOpts.maxRounds = parseInt(args[++i], 10); break;
        case "--timeout": solverOpts.leanTimeoutMs = parseInt(args[++i], 10); break;
        case "--lean":    repoRoot = args[++i]; break;
        default: console.error(`Unknown option: ${args[i]}`); usage();
      }
    }

    return {
      verifier: new InverseVerifier(targetName, forwardOp),
      solverOpts,
      repoRoot,
    };
  }

  // Full form: --problem <type> [args]
  let problemType: string | undefined;
  let target: string | undefined;
  let op: string | undefined;
  let base: string | undefined;
  let property: string | undefined;
  let objectivesStr: string | undefined;
  let repoRoot: string | undefined;
  const solverOpts: SolverOptions = {};

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case "--problem":    problemType = args[++i]; break;
      case "--target":     target = args[++i]; break;
      case "--op":         op = args[++i]; break;
      case "--base":       base = args[++i]; break;
      case "--property":   property = args[++i]; break;
      case "--objectives": objectivesStr = args[++i]; break;
      case "--style":      solverOpts.stylePrompt = args[++i]; break;
      case "--rounds":     solverOpts.maxRounds = parseInt(args[++i], 10); break;
      case "--timeout":    solverOpts.leanTimeoutMs = parseInt(args[++i], 10); break;
      case "--lean":       repoRoot = args[++i]; break;
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
    default:
      console.error(`Unknown problem type: ${problemType}`);
      usage();
  }

  return { verifier, solverOpts, repoRoot };
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

  const { verifier, solverOpts, repoRoot } = buildVerifier(args);

  // ── Run the solver ────────────────────────────────────────────────────────
  const catlab = new CatlabClient(repoRoot);
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
