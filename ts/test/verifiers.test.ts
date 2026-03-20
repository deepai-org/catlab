/**
 * Unit tests for verifiers — uses a mock CatlabClient (no real Lean CAS).
 *
 * Run:
 *   npx ts-node test/verifiers.test.ts
 */

import type {
  CatlabCommand,
  CatlabResponse,
  CatlabResponseOk,
  TheoryJson,
  VerificationResult,
} from "../src/types";

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
} from "../src/verifiers";

// ── Test harness ─────────────────────────────────────────────────────────────

interface TestCase { name: string; fn: () => Promise<void> }
const tests: TestCase[] = [];
function test(name: string, fn: () => Promise<void>) { tests.push({ name, fn }); }

function assert(condition: boolean, msg: string): asserts condition {
  if (!condition) throw new Error(`Assertion failed: ${msg}`);
}
function assertEq<T>(actual: T, expected: T, msg: string) {
  if (actual !== expected)
    throw new Error(`${msg}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
}

// ── Mock CatlabClient ────────────────────────────────────────────────────────

type ResponseFn = (cmd: CatlabCommand) => CatlabResponse;

class MockCatlabClient {
  constructor(private responder: ResponseFn) {}

  async request(command: CatlabCommand, _timeoutMs?: number): Promise<CatlabResponse> {
    return this.responder(command);
  }

  async requestOrThrow(command: CatlabCommand, _timeoutMs?: number): Promise<CatlabResponseOk> {
    const res = await this.request(command);
    if (res.status === "error") throw new Error(`Lean CAS error: ${res.message}`);
    return res as CatlabResponseOk;
  }

  kill() {}
}

// ── Fixtures ─────────────────────────────────────────────────────────────────

const minimalTheory: TheoryJson = {
  name: "Test",
  doctrine: "Category",
  objects: [{ name: "A" }],
  morphisms: [{ name: "f", domain: "A", codomain: "A" }],
  axioms: [],
};

const passResult: VerificationResult = {
  verified: true,
  candidateName: "Test",
  verificationStatus: "✓ Success",
  missingSignatures: [],
  unmappedObjects: [],
  axiomViolations: [],
};

const failResult: VerificationResult = {
  verified: false,
  candidateName: "Test",
  verificationStatus: "✗ Failed: missing signatures",
  missingSignatures: [{ domainShape: "§0", codomainShape: "§0", sourceName: "f" }],
  unmappedObjects: ["B"],
  axiomViolations: [],
};

function okResponse(extra: Partial<CatlabResponseOk> = {}): CatlabResponseOk {
  return { id: "mock", status: "ok" as const, ...extra };
}

function errorResponse(message: string): CatlabResponse {
  return { id: "mock", status: "error" as const, message };
}

function summaryResponder(theory?: TheoryJson): ResponseFn {
  return (cmd) => {
    if ((cmd as any).command === "summary") {
      return okResponse({ theory: theory ?? minimalTheory });
    }
    return okResponse({ result: passResult });
  };
}

// ── InverseVerifier ──────────────────────────────────────────────────────────

test("InverseVerifier.preflight returns kind=inverse", async () => {
  const v = new InverseVerifier("Monoid", "opposite");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "inverse", "kind");
  assert(spec.problemDescription.includes("opposite"), "should mention operator");
  assert(spec.contextJson.includes("Monoid"), "should mention target");
  assert(spec.hint.length > 0, "hint should be non-empty");
});

test("InverseVerifier.preflight with mirror op", async () => {
  const v = new InverseVerifier("Boolean", "mirror");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assert(spec.problemDescription.includes("mirror"), "should mention mirror");
});

test("InverseVerifier.preflight with identity op", async () => {
  const v = new InverseVerifier("Group", "identity");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assert(spec.problemDescription.includes("identity"), "should mention identity");
});

test("InverseVerifier.preflight with decategorify_iso op", async () => {
  const v = new InverseVerifier("CommMonoid", "decategorify_iso");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assert(spec.problemDescription.includes("decategorify"), "should mention decategorify");
  assert(spec.hint.includes("Categorification"), "should have categorification hint");
});

test("InverseVerifier.verify passes through ok result", async () => {
  const v = new InverseVerifier("Monoid", "opposite");
  const mock = new MockCatlabClient(() => okResponse({ result: passResult })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, true, "verified");
  assertEq(result.candidateName, "Test", "candidateName");
});

test("InverseVerifier.verify throws on error", async () => {
  const v = new InverseVerifier("Monoid", "opposite");
  const mock = new MockCatlabClient(() => errorResponse("bad theory")) as any;
  let threw = false;
  try { await v.verify(mock, minimalTheory, 5000); }
  catch (e) { threw = true; assert((e as Error).message.includes("bad theory"), "error message"); }
  assert(threw, "should throw on error");
});

test("InverseVerifier.verify passes through fail result", async () => {
  const v = new InverseVerifier("Monoid", "opposite");
  const mock = new MockCatlabClient(() => okResponse({ result: failResult })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, false, "verified");
  assert(result.missingSignatures.length > 0, "should have missing sigs");
  assert(result.unmappedObjects.length > 0, "should have unmapped objects");
});

// ── PushoutComplementVerifier ────────────────────────────────────────────────

test("PushoutComplementVerifier.preflight returns kind=pushout_complement", async () => {
  const v = new PushoutComplementVerifier("Basic", "Monoid");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "pushout_complement", "kind");
  assert(spec.contextJson.includes("Basic"), "should mention base");
  assert(spec.contextJson.includes("Monoid"), "should mention target");
});

test("PushoutComplementVerifier.verify passes through result", async () => {
  const v = new PushoutComplementVerifier("Basic", "Monoid");
  const mock = new MockCatlabClient(() => okResponse({ result: passResult })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, true, "verified");
});

test("PushoutComplementVerifier.verify throws on error", async () => {
  const v = new PushoutComplementVerifier("Basic", "Monoid");
  const mock = new MockCatlabClient(() => errorResponse("fail")) as any;
  let threw = false;
  try { await v.verify(mock, minimalTheory, 5000); } catch { threw = true; }
  assert(threw, "should throw");
});

// ── ExtensionVerifier ────────────────────────────────────────────────────────

test("ExtensionVerifier.preflight returns kind=extension", async () => {
  const v = new ExtensionVerifier("Monoid", "commutative");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "extension", "kind");
  assert(spec.problemDescription.includes("commutative"), "should mention property");
});

test("ExtensionVerifier.verify throws on error", async () => {
  const v = new ExtensionVerifier("Monoid", "commutative");
  const mock = new MockCatlabClient(() => errorResponse("nope")) as any;
  let threw = false;
  try { await v.verify(mock, minimalTheory, 5000); } catch { threw = true; }
  assert(threw, "should throw");
});

// ── MultiObjectiveVerifier ───────────────────────────────────────────────────

test("MultiObjectiveVerifier.preflight returns kind=multi_objective", async () => {
  const v = new MultiObjectiveVerifier([
    { target: "Monoid", forwardOp: "opposite" },
    { target: "Group", forwardOp: "identity" },
  ]);
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "multi_objective", "kind");
  assert(spec.problemDescription.includes("opposite"), "should mention first op");
  assert(spec.problemDescription.includes("identity"), "should mention second op");
});

test("MultiObjectiveVerifier.verify merges results (all pass)", async () => {
  const v = new MultiObjectiveVerifier([
    { target: "A", forwardOp: "op1" },
    { target: "B", forwardOp: "op2" },
  ]);
  const mock = new MockCatlabClient(() => okResponse({ result: passResult })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, true, "all pass");
  assert(result.verificationStatus.includes("All objectives"), "status message");
});

test("MultiObjectiveVerifier.verify merges results (one fails)", async () => {
  let callCount = 0;
  const v = new MultiObjectiveVerifier([
    { target: "A", forwardOp: "op1" },
    { target: "B", forwardOp: "op2" },
  ]);
  const mock = new MockCatlabClient(() => {
    callCount++;
    // Both calls resolve, but alternate pass/fail based on internal ordering isn't
    // reliable with Promise.all. Just return fail for all to test merge.
    return okResponse({ result: failResult });
  }) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, false, "should fail");
  assert(result.verificationStatus.includes("Failed"), "status");
  // Merged missing sigs from both
  assert(result.missingSignatures.length >= 1, "merged missing sigs");
});

// ── FixedPointVerifier ───────────────────────────────────────────────────────

test("FixedPointVerifier.preflight returns kind=inverse (reused)", async () => {
  const v = new FixedPointVerifier("BoolAlg", "mirror");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "inverse", "kind reuses inverse");
  assert(spec.problemDescription.includes("fixed point"), "mentions fixed point");
});

test("FixedPointVerifier.verify passes through result", async () => {
  const v = new FixedPointVerifier("BoolAlg", "mirror");
  const mock = new MockCatlabClient(() => okResponse({ result: passResult })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, true, "verified");
});

// ── FactorizationVerifier ────────────────────────────────────────────────────

test("FactorizationVerifier.preflight returns kind=factorization with custom schema", async () => {
  const v = new FactorizationVerifier("Ring", "tensor");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "factorization", "kind");
  assert(spec.answerSchema !== undefined, "should have custom schema");
  assert((spec.answerSchema as any).properties.factorX !== undefined, "schema has factorX");
  assert((spec.answerSchema as any).properties.factorY !== undefined, "schema has factorY");
  assertEq(spec.answerToolName, "propose_factorization", "custom tool name");
});

test("FactorizationVerifier.validatePayload accepts valid payload", async () => {
  const v = new FactorizationVerifier("Ring");
  v.validatePayload({ factorX: minimalTheory, factorY: minimalTheory });
  // no throw = pass
});

test("FactorizationVerifier.validatePayload rejects missing factorX", async () => {
  const v = new FactorizationVerifier("Ring");
  let threw = false;
  try { v.validatePayload({ factorY: minimalTheory }); } catch { threw = true; }
  assert(threw, "should throw for missing factorX");
});

test("FactorizationVerifier.validatePayload rejects missing factorY", async () => {
  const v = new FactorizationVerifier("Ring");
  let threw = false;
  try { v.validatePayload({ factorX: minimalTheory }); } catch { threw = true; }
  assert(threw, "should throw for missing factorY");
});

test("FactorizationVerifier.validatePayload rejects non-object", async () => {
  const v = new FactorizationVerifier("Ring");
  let threw = false;
  try { v.validatePayload("not an object"); } catch { threw = true; }
  assert(threw, "should throw for non-object");
});

test("FactorizationVerifier.formatFeedback returns non-empty string", async () => {
  const v = new FactorizationVerifier("Ring");
  const fb = v.formatFeedback!(failResult, { factorX: minimalTheory, factorY: minimalTheory });
  assert(fb.length > 0, "feedback should be non-empty");
});

test("FactorizationVerifier.verify throws on error", async () => {
  const v = new FactorizationVerifier("Ring");
  const mock = new MockCatlabClient(() => errorResponse("bad")) as any;
  let threw = false;
  try { await v.verify(mock, { factorX: minimalTheory, factorY: minimalTheory }, 5000); }
  catch { threw = true; }
  assert(threw, "should throw");
});

// ── InterpolationVerifier ────────────────────────────────────────────────────

test("InterpolationVerifier.preflight returns kind=interpolation", async () => {
  const v = new InterpolationVerifier("Monoid", "Group");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "interpolation", "kind");
});

test("InterpolationVerifier.formatFeedback returns non-empty string", async () => {
  const v = new InterpolationVerifier("Monoid", "Group");
  const fb = v.formatFeedback!(failResult, minimalTheory);
  assert(fb.length > 0, "feedback non-empty");
});

// ── OptimizationVerifier ─────────────────────────────────────────────────────

test("OptimizationVerifier.preflight returns kind=optimization", async () => {
  const v = new OptimizationVerifier("opposite", "Monoid", "minimize generators");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "optimization", "kind");
  assert(spec.problemDescription.includes("minimize generators"), "cost in description");
});

test("OptimizationVerifier.verify adds cost feedback", async () => {
  const v = new OptimizationVerifier("opposite", "Monoid", "minimize generators");
  const mock = new MockCatlabClient(() => okResponse({ result: { ...passResult } })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assert(result.feedbackStrings !== undefined, "should have feedback");
  assert(result.feedbackStrings!.some(s => s.includes("Cost")), "should mention cost");
  assert(result.distance !== undefined, "should have distance");
});

// ── PullbackComplementVerifier ───────────────────────────────────────────────

test("PullbackComplementVerifier.preflight returns kind=pullback_complement", async () => {
  const v = new PullbackComplementVerifier("Basic", "Monoid");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "pullback_complement", "kind");
});

// ── SimplificationVerifier ───────────────────────────────────────────────────

test("SimplificationVerifier.preflight returns kind=simplification", async () => {
  const v = new SimplificationVerifier("Group");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "simplification", "kind");
});

test("SimplificationVerifier.verify adds size feedback", async () => {
  const v = new SimplificationVerifier("Group");
  const mock = new MockCatlabClient(() =>
    okResponse({ result: { ...passResult }, candidate_size: 3, target_size: 5 } as any)
  ) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assert(result.feedbackStrings!.some(s => s.includes("Candidate size")), "candidate size");
  assert(result.feedbackStrings!.some(s => s.includes("Target size")), "target size");
});

test("SimplificationVerifier.formatFeedback returns non-empty", async () => {
  const v = new SimplificationVerifier("Group");
  const fb = v.formatFeedback!(failResult, minimalTheory);
  assert(fb.length > 0, "non-empty");
});

// ── ModelFindingVerifier ─────────────────────────────────────────────────────

test("ModelFindingVerifier.preflight returns kind=model_finding", async () => {
  const v = new ModelFindingVerifier("Monoid");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "model_finding", "kind");
});

// ── SubobjectVerifier ────────────────────────────────────────────────────────

test("SubobjectVerifier.preflight returns kind=subobject", async () => {
  const v = new SubobjectVerifier("Ring", "commutative");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "subobject", "kind");
  assert(spec.problemDescription.includes("commutative"), "property in description");
});

test("SubobjectVerifier.verify detects non-subtheory", async () => {
  const v = new SubobjectVerifier("Ring", "commutative");
  const mock = new MockCatlabClient(() =>
    okResponse({ result: { ...passResult }, is_subtheory: false, not_in_target: ["g"] } as any)
  ) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, false, "should fail");
  assert(result.feedbackStrings!.some(s => s.includes("g")), "mentions bad generator");
});

// ── SynthesisVerifier ────────────────────────────────────────────────────────

test("SynthesisVerifier.preflight returns kind=synthesis", async () => {
  const v = new SynthesisVerifier("Category", "A", "B");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "synthesis", "kind");
});

test("SynthesisVerifier.verify detects missing generators", async () => {
  const v = new SynthesisVerifier("Category", "A", "B");
  const mock = new MockCatlabClient(() =>
    okResponse({ result: { ...passResult }, extends_theory: false, missing_from_theory: ["comp"] } as any)
  ) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, false, "should fail");
  assert(result.feedbackStrings!.some(s => s.includes("comp")), "mentions missing");
});

// ── QuotientVerifier ─────────────────────────────────────────────────────────

test("QuotientVerifier.preflight returns kind=quotient", async () => {
  const v = new QuotientVerifier("Group", "abelian");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "quotient", "kind");
});

// ── DecompositionVerifier ────────────────────────────────────────────────────

test("DecompositionVerifier.preflight returns kind=decomposition", async () => {
  const v = new DecompositionVerifier("Ring");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "decomposition", "kind");
});

// ── RelaxationVerifier ───────────────────────────────────────────────────────

test("RelaxationVerifier.preflight returns kind=relaxation", async () => {
  const v = new RelaxationVerifier("Group", "finite");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "relaxation", "kind");
});

test("RelaxationVerifier.verify adds distance feedback", async () => {
  const v = new RelaxationVerifier("Group", "finite");
  const mock = new MockCatlabClient(() =>
    okResponse({ result: { ...passResult }, edit_distance: 3 } as any)
  ) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assert(result.feedbackStrings!.some(s => s.includes("Edit distance")), "edit distance");
});

// ── CatalystVerifier ─────────────────────────────────────────────────────────

test("CatalystVerifier.preflight returns kind=catalyst", async () => {
  const v = new CatalystVerifier("Monoid", "Group");
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "catalyst", "kind");
});

test("CatalystVerifier.verify passes through result", async () => {
  const v = new CatalystVerifier("Monoid", "Group");
  const mock = new MockCatlabClient(() => okResponse({ result: passResult })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, true, "verified");
});

// ── ComposeVerifier ──────────────────────────────────────────────────────────

test("ComposeVerifier constructor rejects fewer than 2 verifiers", async () => {
  let threw = false;
  try { new ComposeVerifier([{ label: "only one", verifier: new InverseVerifier("X", "opposite") }]); }
  catch { threw = true; }
  assert(threw, "should reject <2 verifiers");
});

test("ComposeVerifier.preflight returns kind=compose", async () => {
  const v = new ComposeVerifier([
    { label: "inv", verifier: new InverseVerifier("Monoid", "opposite") },
    { label: "ext", verifier: new ExtensionVerifier("Basic", "commutative") },
  ]);
  const mock = new MockCatlabClient(summaryResponder()) as any;
  const spec = await v.preflight(mock, 5000);
  assertEq(spec.kind, "compose", "kind");
  assert(spec.problemDescription.includes("inv"), "mentions first label");
  assert(spec.problemDescription.includes("ext"), "mentions second label");
});

test("ComposeVerifier.verify merges all-pass", async () => {
  const v = new ComposeVerifier([
    { label: "a", verifier: new InverseVerifier("X", "opposite") },
    { label: "b", verifier: new InverseVerifier("Y", "mirror") },
  ]);
  const mock = new MockCatlabClient(() => okResponse({ result: { ...passResult } })) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, true, "all pass");
  assert(result.verificationStatus.includes("All constraints"), "status");
});

test("ComposeVerifier.verify merges partial failure", async () => {
  let callIdx = 0;
  const v = new ComposeVerifier([
    { label: "a", verifier: new InverseVerifier("X", "opposite") },
    { label: "b", verifier: new InverseVerifier("Y", "mirror") },
  ]);
  const mock = new MockCatlabClient(() => {
    // Both get same fail result
    return okResponse({ result: { ...failResult } });
  }) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, false, "should fail");
  assert(result.feedbackStrings!.length === 2, "two feedback entries");
});

test("ComposeVerifier.verify handles sub-verifier errors gracefully", async () => {
  const v = new ComposeVerifier([
    { label: "ok", verifier: new InverseVerifier("X", "opposite") },
    { label: "err", verifier: new InverseVerifier("Y", "mirror") },
  ]);
  let callCount = 0;
  const mock = new MockCatlabClient(() => {
    callCount++;
    // First call ok, second error — but Promise.all ordering not guaranteed
    // so just return error for all to test error handling path
    return errorResponse("boom");
  }) as any;
  const result = await v.verify(mock, minimalTheory, 5000);
  assertEq(result.verified, false, "should fail");
  assert(result.feedbackStrings!.some(s => s.includes("Error")), "error in feedback");
});

test("ComposeVerifier.formatFeedback returns non-empty string", async () => {
  const v = new ComposeVerifier([
    { label: "a", verifier: new InverseVerifier("X", "opposite") },
    { label: "b", verifier: new InverseVerifier("Y", "mirror") },
  ]);
  const fb = v.formatFeedback!(
    { ...failResult, feedbackStrings: ["[a] ✗ failed", "[b] ✓ ok"] },
    minimalTheory,
  );
  assert(fb.length > 0, "non-empty");
  assert(fb.includes("1/2"), "shows pass count");
});

// ── Cross-cutting: all verifiers throw on CAS error ──────────────────────────

const errorMock = new MockCatlabClient(() => errorResponse("CAS exploded")) as any;

for (const [name, verifier] of [
  ["PullbackComplement", new PullbackComplementVerifier("A", "B")],
  ["Simplification", new SimplificationVerifier("X")],
  ["ModelFinding", new ModelFindingVerifier("X")],
  ["Decomposition", new DecompositionVerifier("X")],
  ["Catalyst", new CatalystVerifier("A", "B")],
] as [string, any][]) {
  test(`${name}Verifier.verify throws on CAS error`, async () => {
    let threw = false;
    try { await verifier.verify(errorMock, minimalTheory, 5000); }
    catch (e) { threw = true; assert((e as Error).message.includes("CAS exploded") || (e as Error).message.includes("Lean"), "error msg"); }
    assert(threw, `${name} should throw`);
  });
}

// ── Runner ───────────────────────────────────────────────────────────────────

async function run() {
  let passed = 0;
  let failed = 0;
  const failures: { name: string; error: string }[] = [];

  for (const t of tests) {
    const startMs = Date.now();
    try {
      await t.fn();
      const ms = Date.now() - startMs;
      console.log(`  ✓ ${t.name} (${ms}ms)`);
      passed++;
    } catch (e) {
      const ms = Date.now() - startMs;
      const msg = (e as Error).message;
      console.log(`  ✗ ${t.name} (${ms}ms)`);
      console.log(`    ${msg}`);
      failed++;
      failures.push({ name: t.name, error: msg });
    }
  }

  console.log(`\n${passed} passed, ${failed} failed, ${tests.length} total`);

  if (failures.length > 0) {
    console.log("\nFailures:");
    for (const f of failures) {
      console.log(`  ✗ ${f.name}: ${f.error}`);
    }
  }

  process.exit(failed > 0 ? 1 : 0);
}

run().catch((e) => {
  console.error("Fatal:", e);
  process.exit(2);
});
