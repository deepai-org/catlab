/**
 * Solver unit tests — exercises GenericSolver with mocked LLM, CAS, and Verifier.
 *
 * Run:
 *   npx ts-node test/solver.test.ts
 */

import Anthropic from "@anthropic-ai/sdk";
import { GenericSolver } from "../src/solver";
import type {
  ProblemSpec,
  Verifier,
  VerificationResult,
  SolverProgressEvent,
  SolverOptions,
} from "../src/types";
import type { CatlabClient } from "../src/client";

// ── Test harness ─────────────────────────────────────────────────────────────

interface TestCase {
  name: string;
  fn: () => Promise<void>;
}

const tests: TestCase[] = [];
function test(name: string, fn: () => Promise<void>) {
  tests.push({ name, fn });
}

function assert(condition: boolean, msg: string): asserts condition {
  if (!condition) throw new Error(`Assertion failed: ${msg}`);
}

function assertEq<T>(actual: T, expected: T, msg: string) {
  if (actual !== expected) {
    throw new Error(`${msg}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

// ── Shared fixtures ──────────────────────────────────────────────────────────

const STUB_SPEC: ProblemSpec = {
  kind: "inverse",
  problemDescription: "Find X such that f(X) = Monoid",
  hint: "Try a monoid",
  contextJson: "{}",
};

const GOOD_PAYLOAD = {
  name: "TestTheory",
  objects: [{ name: "X" }],
  morphisms: [{ name: "m", domain: "X", codomain: "X" }],
  axioms: [],
};

function makeVerifiedResult(): VerificationResult {
  return {
    verified: true,
    candidateName: "TestTheory",
    verificationStatus: "✓ Success",
    missingSignatures: [],
    unmappedObjects: [],
    axiomViolations: [],
  };
}

function makeFailedResult(): VerificationResult {
  return {
    verified: false,
    candidateName: "TestTheory",
    verificationStatus: "✗ Failed: 1 axiom violation",
    missingSignatures: [],
    unmappedObjects: [],
    axiomViolations: [
      { sourceAxiom: "assoc", status: "✗ Failed", lhsReduced: "a", rhsReduced: "b", depthUsed: 5 },
    ],
  };
}

// ── Mock factories ───────────────────────────────────────────────────────────

function mockCatlab(): CatlabClient {
  return {
    request: async () => ({ id: "1", status: "ok" as const }),
    requestOrThrow: async () => ({ id: "1", status: "ok" as const }),
  } as unknown as CatlabClient;
}

function mockLLM(overrides: Record<string, unknown> = {}): any {
  return {
    generateInitial: async (_spec: ProblemSpec) => ({ ...GOOD_PAYLOAD }),
    refineWithFeedback: async (_spec: ProblemSpec, _fb: string, _prev: unknown, _round: number) =>
      ({ ...GOOD_PAYLOAD }),
    reflectOnSolve: async () => "no suggestions",
    ...overrides,
  };
}

function mockVerifier(overrides: Partial<Verifier> = {}): Verifier {
  return {
    preflight: async () => ({ ...STUB_SPEC }),
    verify: async () => makeVerifiedResult(),
    ...overrides,
  };
}

// ── Tests ────────────────────────────────────────────────────────────────────

test("Immediate success — verifier returns verified=true on first attempt", async () => {
  const solver = new GenericSolver(mockCatlab(), mockLLM(), mockVerifier());
  const result = await solver.solve({ maxRounds: 3, maxLLMRetries: 0, maxLeanRetries: 0 });
  assertEq(result.success, true, "should succeed");
  assertEq(result.rounds, 1, "should take 1 round");
  assert(result.winner !== undefined, "should have winner");
  assertEq(result.history.length, 1, "history should have 1 entry");
});

test("Success after refinement — verifier fails first, succeeds second", async () => {
  let verifyCall = 0;
  const verifier = mockVerifier({
    verify: async () => {
      verifyCall++;
      return verifyCall === 1 ? makeFailedResult() : makeVerifiedResult();
    },
  });
  const solver = new GenericSolver(mockCatlab(), mockLLM(), verifier);
  const result = await solver.solve({ maxRounds: 5, maxLLMRetries: 0, maxLeanRetries: 0 });
  assertEq(result.success, true, "should succeed");
  assertEq(result.rounds, 2, "should take 2 rounds");
  assertEq(result.history.length, 2, "history should have 2 entries");
  assertEq(result.history[0].result.verified, false, "first entry should be failed");
  assertEq(result.history[1].result.verified, true, "second entry should be verified");
});

test("Exhaustion — verifier never succeeds, maxRounds=3", async () => {
  const verifier = mockVerifier({ verify: async () => makeFailedResult() });
  const solver = new GenericSolver(mockCatlab(), mockLLM(), verifier);
  const result = await solver.solve({ maxRounds: 3, maxLLMRetries: 0, maxLeanRetries: 0 });
  assertEq(result.success, false, "should not succeed");
  assertEq(result.rounds, 3, "should exhaust 3 rounds");
  assertEq(result.history.length, 3, "history should have 3 entries");
});

test("Fatal LLM error — AuthenticationError propagates", async () => {
  const authErr = new Anthropic.AuthenticationError(
    401,
    { message: "invalid api key", type: "authentication_error", param: null, code: null },
    "invalid api key",
    {},
  );
  const llm = mockLLM({
    generateInitial: async () => { throw authErr; },
  });
  const solver = new GenericSolver(mockCatlab(), llm, mockVerifier());
  let threw = false;
  try {
    await solver.solve({ maxRounds: 3, maxLLMRetries: 2, maxLeanRetries: 0 });
  } catch (e) {
    threw = true;
    assert(e === authErr, "should throw the original AuthenticationError");
  }
  assert(threw, "should have thrown");
});

test("Retryable LLM error then success — parse error retried", async () => {
  let callCount = 0;
  const llm = mockLLM({
    generateInitial: async () => {
      callCount++;
      if (callCount === 1) throw new Error("LLM did not output valid JSON");
      return { ...GOOD_PAYLOAD };
    },
  });
  const solver = new GenericSolver(mockCatlab(), llm, mockVerifier());
  const result = await solver.solve({ maxRounds: 3, maxLLMRetries: 2, maxLeanRetries: 0 });
  assertEq(result.success, true, "should succeed after retry");
  assert(callCount >= 2, "LLM should have been called at least twice");
});

test("Fatal Lean error — 'not found' propagates", async () => {
  const verifier = mockVerifier({
    verify: async () => { throw new Error("theory not found"); },
  });
  const solver = new GenericSolver(mockCatlab(), mockLLM(), verifier);
  let threw = false;
  try {
    await solver.solve({ maxRounds: 3, maxLLMRetries: 0, maxLeanRetries: 0 });
  } catch (e) {
    threw = true;
    assert((e as Error).message.includes("not found"), "should contain 'not found'");
  }
  assert(threw, "should have thrown");
});

test("Progress events — onProgress receives correct phases", async () => {
  const events: SolverProgressEvent[] = [];
  const solver = new GenericSolver(mockCatlab(), mockLLM(), mockVerifier());
  const result = await solver.solve({
    maxRounds: 3,
    maxLLMRetries: 0,
    maxLeanRetries: 0,
    onProgress: (ev) => events.push(ev),
  });
  assertEq(result.success, true, "should succeed");
  assert(events.length >= 3, "should have at least 3 events (init, generating, success)");
  assertEq(events[0].phase, "init", "first event should be init");
  assertEq(events[1].phase, "generating", "second event should be generating");
  assertEq(events[2].phase, "success", "third event should be success");
  assert(events.every(e => e.maxRounds === 3), "all events should have maxRounds=3");
});

test("Custom formatFeedback — verifier's formatFeedback is called on failure", async () => {
  let formatCalled = false;
  let verifyCall = 0;
  const verifier = mockVerifier({
    verify: async () => {
      verifyCall++;
      return verifyCall === 1 ? makeFailedResult() : makeVerifiedResult();
    },
    formatFeedback: (result, _payload) => {
      formatCalled = true;
      return `custom feedback: ${result.verificationStatus}`;
    },
  });

  let feedbackReceived = "";
  const llm = mockLLM({
    refineWithFeedback: async (_spec: any, feedback: any, _prev: any, _round: any) => {
      feedbackReceived = feedback;
      return { ...GOOD_PAYLOAD };
    },
  });

  const solver = new GenericSolver(mockCatlab(), llm, verifier);
  const result = await solver.solve({ maxRounds: 5, maxLLMRetries: 0, maxLeanRetries: 0 });
  assertEq(result.success, true, "should succeed");
  assert(formatCalled, "formatFeedback should have been called");
  assert(feedbackReceived.startsWith("custom feedback:"), "LLM should receive custom feedback");
});

test("Custom validatePayload — rejection treated as PARSE_ERROR", async () => {
  let generateCalls = 0;
  const llm = mockLLM({
    generateInitial: async () => {
      generateCalls++;
      if (generateCalls === 1) return { bad: true }; // will be rejected
      return { ...GOOD_PAYLOAD };
    },
  });
  const verifier = mockVerifier({
    validatePayload: (payload: unknown) => {
      const p = payload as Record<string, unknown>;
      if (!p.name) throw new Error("LLM did not output valid payload: missing name");
    },
  });
  const solver = new GenericSolver(mockCatlab(), llm, verifier);
  const result = await solver.solve({ maxRounds: 3, maxLLMRetries: 2, maxLeanRetries: 0 });
  assertEq(result.success, true, "should succeed after validatePayload retry");
  assert(generateCalls >= 2, "should have retried generation");
});

// ── Runner ───────────────────────────────────────────────────────────────────

async function run() {
  // Silence solver's console.error output
  const origError = console.error;
  console.error = () => {};

  let passed = 0;
  let failed = 0;
  const failures: { name: string; error: string }[] = [];

  for (const t of tests) {
    const startMs = Date.now();
    try {
      await t.fn();
      const ms = Date.now() - startMs;
      origError(`  ✓ ${t.name} (${ms}ms)`);
      passed++;
    } catch (e) {
      const ms = Date.now() - startMs;
      const msg = (e as Error).message;
      origError(`  ✗ ${t.name} (${ms}ms)`);
      origError(`    ${msg}`);
      failed++;
      failures.push({ name: t.name, error: msg });
    }
  }

  origError(`\n${passed} passed, ${failed} failed, ${tests.length} total`);

  if (failures.length > 0) {
    origError("\nFailures:");
    for (const f of failures) {
      origError(`  ✗ ${f.name}: ${f.error}`);
    }
  }

  console.error = origError;
  process.exit(failed > 0 ? 1 : 0);
}

run().catch((e) => {
  console.error("Fatal:", e);
  process.exit(2);
});
