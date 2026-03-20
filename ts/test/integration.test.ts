/**
 * Wire protocol integration tests — verifies NDJSON serialization boundary
 * between TypeScript types and Lean Protocol.lean.
 *
 * Run:
 *   npx ts-node test/integration.test.ts
 *
 * Focused on: do the JSON shapes crossing the NDJSON pipe match on both sides?
 */

import { CatlabClient } from "../src/client";
import type {
  CatlabCommand,
  CatlabResponse,
  CatlabResponseOk,
  TheoryJson,
  ExprJson,
  MorphismJson,
} from "../src/types";

// ── Test harness ─────────────────────────────────────────────────────────────

interface TestCase {
  name: string;
  fn: (client: CatlabClient) => Promise<void>;
}

const tests: TestCase[] = [];
function test(name: string, fn: (client: CatlabClient) => Promise<void>) {
  tests.push({ name, fn });
}

function assert(condition: boolean, msg: string): asserts condition {
  if (!condition) throw new Error(`Assertion failed: ${msg}`);
}

function assertEq<T>(actual: T, expected: T, msg: string) {
  if (actual !== expected) {
    throw new Error(
      `${msg}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`
    );
  }
}

function assertOk(resp: CatlabResponse): asserts resp is CatlabResponseOk {
  if (resp.status !== "ok") {
    throw new Error(
      `Expected status "ok", got "${resp.status}": ${(resp as any).message}`
    );
  }
}

// ── Helpers ──────────────────────────────────────────────────────────────────

/** Recursively check that a value matches ExprJson shape. */
function isValidExpr(e: ExprJson): boolean {
  if (typeof e === "string") return true;
  if (typeof e !== "object" || e === null) return false;
  const keys = Object.keys(e);
  if (keys.length !== 1) return false;
  const key = keys[0];
  if (key === "atom") return typeof (e as any).atom === "string";
  if (key === "id") return isValidExpr((e as any).id);
  if (["comp", "tensor", "prod", "hom", "coprod"].includes(key)) {
    const arr = (e as any)[key];
    return Array.isArray(arr) && arr.length === 2 && isValidExpr(arr[0]) && isValidExpr(arr[1]);
  }
  return false;
}

// ── 1. list_theories roundtrip ───────────────────────────────────────────────

test("wire: list_theories returns string array with 33+ entries", async (client) => {
  const resp = await client.request({ command: "list_theories" });
  assertOk(resp);
  assert(Array.isArray(resp.theories), "theories should be an array");
  assert(resp.theories!.length >= 33, `expected 33+ theories, got ${resp.theories!.length}`);
  for (const t of resp.theories!) {
    assertEq(typeof t, "string", "each theory name should be a string");
  }
});

// ── 2. summary returns valid TheoryJson ──────────────────────────────────────

test("wire: summary Monoid returns well-shaped TheoryJson", async (client) => {
  const resp = await client.request({ command: "summary", theory: "Monoid" });
  assertOk(resp);
  const t = resp.theory!;
  assert(t !== undefined, "response should have theory field");
  assertEq(t.name, "Monoid", "theory name");
  assertEq(typeof t.doctrine, "string", "doctrine should be a string");
  assert(Array.isArray(t.objects) && t.objects.length > 0, "objects non-empty");
  assert(Array.isArray(t.morphisms) && t.morphisms.length > 0, "morphisms non-empty");
  assert(Array.isArray(t.axioms) && t.axioms.length > 0, "axioms non-empty");

  for (const obj of t.objects) {
    assertEq(typeof obj.name, "string", "object.name should be string");
  }
  for (const mor of t.morphisms) {
    assertEq(typeof mor.name, "string", "morphism.name should be string");
    assert(isValidExpr(mor.domain), `morphism ${mor.name} domain is valid ExprJson`);
    assert(isValidExpr(mor.codomain), `morphism ${mor.name} codomain is valid ExprJson`);
  }
  for (const ax of t.axioms) {
    assertEq(typeof ax.name, "string", "axiom.name should be string");
    assert(isValidExpr(ax.lhs), `axiom ${ax.name} lhs is valid ExprJson`);
    assert(isValidExpr(ax.rhs), `axiom ${ax.name} rhs is valid ExprJson`);
  }
});

// ── 3. validate returns boolean + errors ─────────────────────────────────────

test("wire: validate Monoid returns valid=true, errors=[]", async (client) => {
  const resp = await client.request({ command: "validate", theory: "Monoid" });
  assertOk(resp);
  assertEq(resp.valid, true, "Monoid should be valid");
  assert(Array.isArray(resp.errors), "errors should be an array");
  assertEq(resp.errors!.length, 0, "errors should be empty");
});

// ── 4. apply_operator returns transformed theory ─────────────────────────────

test("wire: apply_operator opposite on Monoid returns valid theory", async (client) => {
  // Get original Monoid for comparison
  const origResp = await client.request({ command: "summary", theory: "Monoid" });
  assertOk(origResp);
  const orig = origResp.theory!;

  const resp = await client.request({
    command: "apply_operator",
    operator: "opposite",
    theory: "Monoid",
  });
  assertOk(resp);
  const opp = resp.theory!;
  assert(opp !== undefined, "response should have theory field");
  assertEq(typeof opp.name, "string", "opposite theory should have name");
  assertEq(opp.objects.length, orig.objects.length, "same object count");
  assertEq(opp.morphisms.length, orig.morphisms.length, "same morphism count");

  // Opposite swaps domain/codomain
  for (const mor of opp.morphisms) {
    assert(isValidExpr(mor.domain), `opp morphism ${mor.name} domain valid`);
    assert(isValidExpr(mor.codomain), `opp morphism ${mor.name} codomain valid`);
  }
});

// ── 5. Full TheoryJson field presence and types ──────────────────────────────

test("wire: TheoryJson roundtrip — every field present and typed", async (client) => {
  const theories = ["Monoid", "Group", "Ring", "Category"];
  for (const name of theories) {
    const resp = await client.request({ command: "summary", theory: name });
    assertOk(resp);
    const t = resp.theory!;
    assert(t !== undefined, `${name}: theory present`);
    assertEq(typeof t.name, "string", `${name}: name is string`);
    assertEq(typeof t.doctrine, "string", `${name}: doctrine is string`);
    assert(Array.isArray(t.objects), `${name}: objects is array`);
    assert(Array.isArray(t.morphisms), `${name}: morphisms is array`);
    assert(Array.isArray(t.axioms), `${name}: axioms is array`);
  }
});

// ── 6. Expr JSON shapes are correct ─────────────────────────────────────────

test("wire: ExprJson includes compound types (prod in Monoid)", async (client) => {
  const resp = await client.request({ command: "summary", theory: "Monoid" });
  assertOk(resp);
  const t = resp.theory!;

  // Monoid should have mul: M×M → M with a compound domain
  let foundCompound = false;
  for (const mor of t.morphisms) {
    if (typeof mor.domain === "object" && mor.domain !== null) {
      foundCompound = true;
      const keys = Object.keys(mor.domain);
      assert(keys.length === 1, `compound expr should have exactly one key, got: ${keys}`);
      assert(
        ["prod", "tensor", "comp", "hom", "coprod", "atom", "id"].includes(keys[0]),
        `compound expr key "${keys[0]}" should be a valid ExprJson tag`
      );
    }
  }
  assert(foundCompound, "Monoid should have at least one morphism with compound domain");

  // Also check atom strings
  let foundAtom = false;
  for (const mor of t.morphisms) {
    if (typeof mor.domain === "string") foundAtom = true;
    if (typeof mor.codomain === "string") foundAtom = true;
  }
  assert(foundAtom, "Monoid should have at least one morphism with string-atom domain/codomain");
});

// ── 7. Error: unknown theory ─────────────────────────────────────────────────

test("wire: summary unknown theory returns error", async (client) => {
  const resp = await client.request({
    command: "summary",
    theory: "NonexistentTheory",
  });
  assertEq(resp.status, "error", "should return error status");
});

// ── 8. Error: unknown operator ───────────────────────────────────────────────

test("wire: apply_operator unknown op returns error", async (client) => {
  const resp = await client.request({
    command: "apply_operator",
    operator: "nonexistent_op",
    theory: "Monoid",
  });
  assertEq(resp.status, "error", "should return error status");
});

// ── 9. Concurrent requests don't interfere ───────────────────────────────────

test("wire: 5 concurrent requests return correct results", async (client) => {
  const [r1, r2, r3, r4, r5] = await Promise.all([
    client.request({ command: "list_theories" }),
    client.request({ command: "summary", theory: "Monoid" }),
    client.request({ command: "summary", theory: "Group" }),
    client.request({ command: "validate", theory: "Monoid" }),
    client.request({ command: "apply_operator", operator: "opposite", theory: "Monoid" }),
  ]);

  assertOk(r1);
  assert(Array.isArray(r1.theories), "list_theories: theories array");

  assertOk(r2);
  assertEq(r2.theory!.name, "Monoid", "summary Monoid: name");

  assertOk(r3);
  assertEq(r3.theory!.name, "Group", "summary Group: name");

  assertOk(r4);
  assertEq(r4.valid, true, "validate Monoid: valid");

  assertOk(r5);
  assert(r5.theory !== undefined, "opposite Monoid: theory present");
});

// ── 10. VerificationResult wire format ───────────────────────────────────────

test("wire: evaluate_inverse with wrong candidate returns VerificationResult", async (client) => {
  const wrongCandidate: TheoryJson = {
    name: "Wrong",
    doctrine: "Category",
    objects: [{ name: "X" }],
    morphisms: [],
    axioms: [],
  };

  const resp = await client.request({
    command: "evaluate_inverse",
    target: "Monoid",
    forward_op: "opposite",
    candidate: wrongCandidate,
  });
  assertOk(resp);
  const r = resp.result!;
  assert(r !== undefined, "response should have result field");
  assertEq(r.verified, false, "wrong candidate should not verify");
  assertEq(typeof r.candidateName, "string", "candidateName should be string");
  assertEq(typeof r.verificationStatus, "string", "verificationStatus should be string");
  assert(Array.isArray(r.missingSignatures), "missingSignatures should be array");
  assert(Array.isArray(r.unmappedObjects), "unmappedObjects should be array");
  assert(Array.isArray(r.axiomViolations), "axiomViolations should be array");
  // A trivially wrong candidate should have missing signatures
  assert(
    r.missingSignatures.length > 0 || r.unmappedObjects.length > 0,
    "wrong candidate should have structural mismatches"
  );
});

// ── Runner ───────────────────────────────────────────────────────────────────

async function run() {
  console.log("Starting Lean CAS for wire protocol integration tests...");
  const client = new CatlabClient();

  // Warm up — first request compiles/loads, can be slow
  await client.request({ command: "list_theories" }, 120_000);
  console.log("CAS ready.\n");

  let passed = 0,
    failed = 0;
  const failures: { name: string; error: string }[] = [];

  for (const t of tests) {
    const start = Date.now();
    try {
      await t.fn(client);
      console.log(`  \u2713 ${t.name} (${Date.now() - start}ms)`);
      passed++;
    } catch (e) {
      console.log(
        `  \u2717 ${t.name} (${Date.now() - start}ms)\n    ${(e as Error).message}`
      );
      failed++;
      failures.push({ name: t.name, error: (e as Error).message });
    }
  }

  console.log(`\n${passed} passed, ${failed} failed, ${tests.length} total`);
  if (failures.length > 0) {
    console.log("\nFailures:");
    for (const f of failures) console.log(`  \u2717 ${f.name}: ${f.error}`);
  }

  client.kill();
  process.exit(failed > 0 ? 1 : 0);
}

run().catch((e) => {
  console.error("Fatal:", e);
  process.exit(2);
});
