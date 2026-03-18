#!/usr/bin/env node
"use strict";
/**
 * catlab-solve — CLI entry point for the inverse problem solver.
 *
 * Usage:
 *   node dist/index.js <target> <forwardOp> [options]
 *
 * Examples:
 *   node dist/index.js Monoid identity
 *   node dist/index.js Monoid decategorify_iso --style "prefer cobordisms" --rounds 5
 *   node dist/index.js Ring decategorify_iso --rounds 3
 *
 * The Lean REPL is spawned automatically from the catlab repo root.
 * Set ANTHROPIC_API_KEY in your environment.
 *
 * Output (stdout): final result JSON
 * Logs (stderr):   round-by-round progress + Claude streaming text
 */
Object.defineProperty(exports, "__esModule", { value: true });
const client_1 = require("./client");
const llm_1 = require("./llm");
const solver_1 = require("./solver");
// ── CLI argument parsing ──────────────────────────────────────────────────────
function usage() {
    console.error(`
Usage: catlab-solve <targetTheory> <forwardOp> [options]

Arguments:
  targetTheory   Name of the target theory in the CatLab registry
                 Run with "list" to see all available theories
  forwardOp      CAS operator to apply to the candidate:
                   identity           no-op (solve for X ≅ target directly)
                   decategorify_iso   decategorify via isomorphism classes
                   decategorify_K0    decategorify via Grothendieck group
                   decategorify_chi   decategorify via Euler characteristic
                   mirror             apply the Mirror/Stone-duality operator
                   opposite           apply the Opposite functor

Options:
  --style <str>   Style guidance for the LLM (e.g. "prefer cobordisms")
  --rounds <n>    Max LLM rounds (default: 5)
  --timeout <ms>  Per-Lean-request timeout in ms (default: 30000)
  --lean <path>   Path to catlab repo root (default: ../../ relative to ts/src)

Environment:
  ANTHROPIC_API_KEY  Required — your Anthropic API key

Examples:
  catlab-solve Monoid identity
  catlab-solve Ring decategorify_iso --style "use graded vector spaces" --rounds 3
  catlab-solve list     # show available theories
`);
    process.exit(1);
}
async function listTheories(client) {
    const res = await client.requestOrThrow({ command: "list_theories" });
    console.log("Available theories:");
    (res.theories ?? []).forEach((name) => console.log(`  ${name}`));
}
async function main() {
    const args = process.argv.slice(2);
    if (args.length === 0 || args[0] === "--help" || args[0] === "-h")
        usage();
    // Check for ANTHROPIC_API_KEY early
    if (!process.env.ANTHROPIC_API_KEY) {
        console.error("Error: ANTHROPIC_API_KEY environment variable is not set.");
        process.exit(1);
    }
    const targetName = args[0];
    let repoRoot;
    // Handle "list" command
    if (targetName === "list") {
        const client = new client_1.CatlabClient(repoRoot);
        await listTheories(client);
        client.kill();
        return;
    }
    if (args.length < 2)
        usage();
    const forwardOp = args[1];
    // Parse optional flags
    const options = { forwardOp };
    for (let i = 2; i < args.length; i++) {
        switch (args[i]) {
            case "--style":
                options.stylePrompt = args[++i];
                break;
            case "--rounds":
                options.maxRounds = parseInt(args[++i], 10);
                break;
            case "--timeout":
                options.leanTimeoutMs = parseInt(args[++i], 10);
                break;
            case "--lean":
                repoRoot = args[++i];
                break;
            default:
                console.error(`Unknown option: ${args[i]}`);
                usage();
        }
    }
    // ── Run the solver ────────────────────────────────────────────────────────
    const catlab = new client_1.CatlabClient(repoRoot);
    const llm = new llm_1.LLMClient();
    const solver = new solver_1.InverseProblemSolver(catlab, llm);
    let exitCode = 0;
    try {
        const result = await solver.solve(targetName, options);
        // Print the result JSON to stdout for piping / further processing
        console.log(JSON.stringify(result, null, 2));
        if (!result.success) {
            console.error(`\n[solver] Failed after ${result.rounds} rounds.`);
            if (result.history.length > 0) {
                const last = result.history[result.history.length - 1];
                console.error(`[solver] Best attempt: "${last.candidate.name}"`);
                console.error(`[solver] Final status: ${last.result.verificationStatus}`);
            }
            exitCode = 1;
        }
    }
    catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        console.error(`[solver] Fatal error: ${msg}`);
        exitCode = 2;
    }
    finally {
        catlab.kill();
    }
    process.exit(exitCode);
}
main().catch((err) => {
    console.error(err);
    process.exit(2);
});
//# sourceMappingURL=index.js.map