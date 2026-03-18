"use strict";
/**
 * LLMClient — Anthropic API wrapper for theory candidate generation.
 *
 * Drives the proposal side of the LLM ↔ CAS inverse problem loop.
 * Given a target theory, a forward operator, and (on rounds > 1) a structured
 * VerificationResult diff from the CAS, it asks Claude to propose or revise
 * a candidate Theory JSON.
 *
 * Design decisions:
 *   - Claude Opus 4.6 with adaptive thinking: the mathematical reasoning
 *     required for categorification is exactly what extended thinking is for.
 *   - Streaming with finalMessage(): prevents HTTP timeouts on long outputs.
 *   - JSON is extracted from a ```json ... ``` code block in the response,
 *     not via structured outputs, because Expr is a recursive type that's
 *     difficult to express as a static JSON Schema.
 *   - The system prompt is cached (cache_control: ephemeral) since it's
 *     identical across all rounds.
 */
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.LLMClient = void 0;
exports.formatDiff = formatDiff;
const sdk_1 = __importDefault(require("@anthropic-ai/sdk"));
// ── System prompt (sent once, cached) ────────────────────────────────────────
const SYSTEM_PROMPT = `You are a world-class category theorist working with a rigorous Computer Algebra System (CAS) for categorical theories.

Your task is to propose candidate theories in JSON format. The CAS will verify each proposal by applying a forward operator (e.g. decategorification) and checking whether the result matches a target theory. You will receive structured diffs describing exactly what is wrong with your previous proposal.

## Theory JSON Format

\`\`\`json
{
  "name": "MyTheory",
  "doctrine": "MonoidalCategory",
  "objects": [
    { "name": "A", "description": "The carrier object" }
  ],
  "morphisms": [
    { "name": "μ", "domain": {"prod": ["A", "A"]}, "codomain": "A", "description": "multiplication" },
    { "name": "η", "domain": "terminal", "codomain": "A", "description": "unit" }
  ],
  "axioms": [
    {
      "name": "assoc",
      "lhs": {"comp": [{"prod": [{"atom":"μ"}, {"id":"A"}]}, {"atom":"μ"}]},
      "rhs": {"comp": [{"prod": [{"id":"A"}, {"atom":"μ"}]}, {"atom":"μ"}]}
    }
  ]
}
\`\`\`

## Expr JSON Reference

| JSON | Meaning |
|------|---------|
| \`"A"\` | Object atom named A (shorthand) |
| \`{"atom": "f"}\` | Morphism atom named f |
| \`{"comp": [e1, e2]}\` | e1 ∘ e2 |
| \`{"tensor": [e1, e2]}\` | e1 ⊗ e2 |
| \`{"prod": [e1, e2]}\` | e1 × e2 |
| \`{"hom": [e1, e2]}\` | Hom(e1, e2) |
| \`{"id": e}\` | id_e |
| \`"unit"\` | Unit object I |
| \`"terminal"\` | Terminal object 1 |
| \`"initial"\` | Initial object 0 |

## Doctrine Strings

Valid values: Category, CartesianCategory, MonoidalCategory, BraidedMonoidal, SymmetricMonoidal, FinitelyComplete, Abelian, Topos, LawvereTheory, ElementaryTopos, MartinLofTypeTheory, ModelCategory, and others.

## Rules

1. Output EXACTLY ONE JSON code block containing the Theory, and nothing else outside it.
2. List objects in the ORDER they appear in the target theory. The CAS uses positional matching — wrong order causes false failures.
3. Keep the candidate as simple as possible. The CAS verifies by forward-applying an operator, not by inspecting the theory directly.
4. Axiom LHS and RHS must be Exprs over the theory's own morphism atoms.
5. When fixing a diff, address EVERY missingSignature and axiomViolation listed.`;
// ── LLMClient ─────────────────────────────────────────────────────────────────
class LLMClient {
    constructor(apiKey) {
        this.client = new sdk_1.default({ apiKey: apiKey ?? process.env.ANTHROPIC_API_KEY });
    }
    /**
     * Round 1: generate an initial proposal.
     *
     * @param targetName     Name of the target theory (e.g. "Monoid")
     * @param targetJson     The target theory JSON (shown to the LLM for structure)
     * @param forwardOp      Which CAS operator will be applied to the candidate
     * @param stylePrompt    Optional style hint (e.g. "prefer cobordisms")
     */
    async generateInitial(targetName, targetJson, forwardOp, stylePrompt) {
        const style = stylePrompt ? `\n\nStyle guidance: ${stylePrompt}` : "";
        const userPrompt = `The target theory is "${targetName}".\n\n` +
            `Its structure (for reference):\n\`\`\`json\n${targetJson}\n\`\`\`\n\n` +
            `The verification method is: apply \`${forwardOp}\` to your candidate, ` +
            `then check whether the result is structurally equivalent to the target above.\n\n` +
            `Propose a categorification — a "higher-dimensional" theory whose ` +
            `${forwardOp} equals the target. ` +
            `Output your proposal as a single JSON code block.${style}`;
        return this.callAndParse(userPrompt);
    }
    /**
     * Rounds 2+: refine a previous proposal given the CAS diff.
     *
     * @param targetName    Name of the target theory
     * @param diff          The VerificationResult from the previous round
     * @param prevCandidate The theory the LLM proposed last round
     * @param forwardOp     The CAS operator being applied
     * @param round         Current round number (for logging)
     */
    async refineWithDiff(targetName, diff, prevCandidate, forwardOp, round) {
        const userPrompt = `Round ${round}: Your previous proposal "${prevCandidate.name}" ` +
            `failed verification against target "${targetName}".\n\n` +
            `Previous candidate:\n\`\`\`json\n${JSON.stringify(prevCandidate, null, 2)}\n\`\`\`\n\n` +
            formatDiff(diff) +
            `\nPlease provide a corrected Theory JSON that fixes ALL of the above errors. ` +
            `Output ONLY the corrected JSON code block.`;
        return this.callAndParse(userPrompt);
    }
    /** Core: call Claude, stream the response, extract and parse the JSON block. */
    async callAndParse(userPrompt) {
        // Use streaming with finalMessage() to prevent HTTP timeouts on long outputs
        const stream = this.client.messages.stream({
            model: "claude-opus-4-6",
            max_tokens: 8192,
            // eslint-disable-next-line @typescript-eslint/no-explicit-any
            thinking: { type: "adaptive" }, // adaptive thinking (Opus 4.6)
            system: [
                {
                    type: "text",
                    text: SYSTEM_PROMPT,
                    // Cache the system prompt — it's identical every round, ~90% cheaper after round 1
                    cache_control: { type: "ephemeral" },
                },
            ],
            messages: [{ role: "user", content: userPrompt }],
        });
        // Stream text to stderr so the user sees progress
        stream.on("text", (delta) => process.stderr.write(delta));
        const message = await stream.finalMessage();
        process.stderr.write("\n");
        // Extract the full text response
        const text = message.content
            .filter((b) => b.type === "text")
            .map((b) => b.text)
            .join("");
        return extractTheoryJson(text);
    }
}
exports.LLMClient = LLMClient;
// ── Diff formatter ────────────────────────────────────────────────────────────
/**
 * Translate a VerificationResult into a structured, actionable LLM prompt.
 * This is where the CAS's rigid structural graph becomes semantic feedback.
 * The LLM doesn't receive "missingSignatures[0]" — it receives
 * "Target requires a morphism §0 → §1 ⊗ §0 (originally named 'η')".
 */
function formatDiff(result) {
    const lines = [];
    // ── Timeout warning ──────────────────────────────────────────────────────
    if (result.verificationStatus.startsWith("⏱")) {
        lines.push("⚠️  TIMEOUT WARNING: The proof engine could not converge within its " +
            "depth limit. Your axioms may form circular rewriting patterns (e.g. " +
            "A → B and B → A). Simplify your axioms or break them into smaller " +
            "non-circular steps.\n");
    }
    // ── Missing morphism signatures ──────────────────────────────────────────
    if (result.missingSignatures.length > 0) {
        lines.push("### Missing Morphisms (structural shapes, not names)");
        lines.push("The CAS identifies morphisms by their structural type (§0 = first object, §1 = second, etc.).");
        lines.push("Your theory is missing the following required morphism types:\n");
        for (const sig of result.missingSignatures) {
            lines.push(`  • Required: ${sig.domainShape} → ${sig.codomainShape}` +
                `  (originally named '${sig.sourceName}' in the target)`);
        }
        lines.push("");
    }
    // ── Unmapped / spurious objects ──────────────────────────────────────────
    if (result.unmappedObjects.length > 0) {
        lines.push("### Spurious Objects (hallucinated generators)");
        lines.push("Your theory has MORE objects than the target requires. " +
            "The following objects have no structural counterpart in the target:\n");
        for (const obj of result.unmappedObjects) {
            lines.push(`  • '${obj}' — remove this object or merge it with an existing one`);
        }
        lines.push("");
    }
    // ── Axiom violations ─────────────────────────────────────────────────────
    if (result.axiomViolations.length > 0) {
        lines.push("### Axiom Violations");
        lines.push("The following axioms are required by the target but do not hold (or could not be verified) in your theory:\n");
        for (const v of result.axiomViolations) {
            const isTimeout = v.status.startsWith("⏱");
            const verdict = isTimeout ? "TIMEOUT (may be correct but unprovable)" : "FAILED";
            lines.push(`  • Axiom '${v.sourceAxiom}': ${verdict}`);
            if (!isTimeout) {
                lines.push(`    LHS reduced to: ${v.lhsReduced}`);
                lines.push(`    RHS reduced to: ${v.rhsReduced}`);
                lines.push(`    → These must reduce to the SAME normal form`);
            }
        }
        lines.push("");
    }
    if (lines.length === 0) {
        lines.push("No specific errors reported (unknown failure). Try restructuring the theory.");
    }
    return lines.join("\n");
}
// ── JSON extraction ───────────────────────────────────────────────────────────
/**
 * Extract the first ```json ... ``` code block from a text response
 * and parse it as a TheoryJson.
 */
function extractTheoryJson(text) {
    // Try ```json ... ``` first, then ``` ... ``` as fallback
    const jsonBlockRe = /```(?:json)?\s*([\s\S]*?)```/g;
    const matches = [...text.matchAll(jsonBlockRe)];
    for (const match of matches) {
        const raw = match[1].trim();
        try {
            const parsed = JSON.parse(raw);
            validateTheoryShape(parsed);
            return parsed;
        }
        catch {
            // Try the next block
        }
    }
    // Last resort: try parsing the entire response as JSON
    try {
        const parsed = JSON.parse(text.trim());
        validateTheoryShape(parsed);
        return parsed;
    }
    catch {
        throw new Error(`LLM did not output a valid Theory JSON.\n` +
            `Response preview: ${text.slice(0, 500)}`);
    }
}
/** Minimal structural validation — catch obvious errors before sending to Lean. */
function validateTheoryShape(obj) {
    if (typeof obj !== "object" || obj === null) {
        throw new Error("Response is not a JSON object");
    }
    const t = obj;
    if (typeof t.name !== "string")
        throw new Error("Missing 'name' field");
    if (!Array.isArray(t.objects))
        throw new Error("Missing 'objects' array");
    if (!Array.isArray(t.morphisms))
        throw new Error("Missing 'morphisms' array");
    if (!Array.isArray(t.axioms))
        throw new Error("Missing 'axioms' array");
}
//# sourceMappingURL=llm.js.map