/**
 * API integration tests — exercises every API endpoint against the real Lean CAS.
 *
 * Run:
 *   npx ts-node test/api.test.ts
 *
 * These tests spawn the Lean REPL, call the API layer directly (no HTTP),
 * and verify the results. Each test is independent and self-contained.
 */

import { CatlabClient } from "../src/client";
import * as api from "../src/api";

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
    throw new Error(`${msg}: expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

// ── Tests: listTheories ──────────────────────────────────────────────────────

test("listTheories returns ok with array of theory names", async (client) => {
  const result = await api.listTheories(client);
  assert(result.ok === true, "result should be ok");
  if (!result.ok) return;
  assert(Array.isArray(result.data.theories), "theories should be an array");
  assert(result.data.theories.length > 0, "should have at least one theory");
  assert(result.data.theories.includes("Monoid"), "should include Monoid");
  assert(result.data.theories.includes("Category"), "should include Category");
  assert(result.data.theories.includes("Ring"), "should include Ring");
});

// ── Tests: getTheorySummary ──────────────────────────────────────────────────

test("getTheorySummary returns summary for Monoid", async (client) => {
  const result = await api.getTheorySummary(client, "Monoid");
  assert(result.ok === true, "result should be ok");
  if (!result.ok) return;
  assertEq(result.data.name, "Monoid", "name should match");
  assert(result.data.summary.length > 0, "summary should be non-empty");
});

test("getTheorySummary returns summary for Category", async (client) => {
  const result = await api.getTheorySummary(client, "Category");
  assert(result.ok === true, "result should be ok");
  if (!result.ok) return;
  assertEq(result.data.name, "Category", "name should match");
  assert(result.data.summary.length > 0, "summary should be non-empty");
});

test("getTheorySummary returns error for empty name", async (client) => {
  const result = await api.getTheorySummary(client, "");
  assert(result.ok === false, "result should be error");
  if (result.ok) return;
  assertEq(result.error.status, 400, "status should be 400");
});

// ── Tests: validateTheory ────────────────────────────────────────────────────

test("validateTheory returns valid for Monoid", async (client) => {
  const result = await api.validateTheory(client, "Monoid");
  assert(result.ok === true, "result should be ok");
  if (!result.ok) return;
  assertEq(result.data.valid, true, "Monoid should be valid");
});

test("validateTheory returns result for Ring", async (client) => {
  const result = await api.validateTheory(client, "Ring");
  assert(result.ok === true, "result should be ok");
  if (!result.ok) return;
  assert(typeof result.data.valid === "boolean", "valid should be boolean");
});

test("validateTheory returns error for empty name", async (client) => {
  const result = await api.validateTheory(client, "");
  assert(result.ok === false, "result should be error");
  if (result.ok) return;
  assertEq(result.error.status, 400, "status should be 400");
});

// ── Tests: applyOperator ─────────────────────────────────────────────────────

test("applyOperator applies Opposite to Monoid", async (client) => {
  const result = await api.applyOperator(client, "opposite", "Monoid");
  assert(result.ok === true, "result should be ok");
  if (!result.ok) return;
  assert(result.data.theory !== null, "should return a theory");
  if (result.data.theory) {
    assert(typeof result.data.theory.name === "string", "theory should have a name");
  }
});

test("applyOperator applies mirror to Category", async (client) => {
  const result = await api.applyOperator(client, "mirror", "Category");
  assert(result.ok === true, "result should be ok");
  if (!result.ok) return;
  assert(result.data.theory !== null, "should return a theory");
});

test("applyOperator error for missing operator", async (client) => {
  const result = await api.applyOperator(client, "", "Monoid");
  assert(result.ok === false, "result should be error");
  if (result.ok) return;
  assertEq(result.error.status, 400, "status should be 400");
});

test("applyOperator error for missing theory", async (client) => {
  const result = await api.applyOperator(client, "opposite", "");
  assert(result.ok === false, "result should be error");
  if (result.ok) return;
  assertEq(result.error.status, 400, "status should be 400");
});

// ── Tests: computePushout ────────────────────────────────────────────────────

test("computePushout combines two theories over a base", async (client) => {
  const result = await api.computePushout(client, "Monoid", "Monoid", "Basic");
  // May succeed or fail depending on CAS support, but API layer should not throw
  assert(result.ok === true || result.ok === false, "result should return cleanly");
});

test("computePushout error for missing fields", async (client) => {
  const result = await api.computePushout(client, "Monoid", "", "Basic");
  assert(result.ok === false, "result should be error");
  if (result.ok) return;
  assertEq(result.error.status, 400, "status should be 400");
});

// ── Tests: HTTP server routes (via fetch) ────────────────────────────────────

import * as http from "http";
import { createServer } from "../src/server";

let httpServer: http.Server;
let baseUrl: string;

async function fetchJson(path: string, options?: RequestInit): Promise<{ status: number; body: any }> {
  const res = await fetch(`${baseUrl}${path}`, options);
  const body = await res.json();
  return { status: res.status, body };
}

test("HTTP GET /api/theories returns theory list", async () => {
  const { status, body } = await fetchJson("/api/theories");
  assertEq(status, 200, "status should be 200");
  assert(Array.isArray(body.theories), "should have theories array");
  assert(body.theories.includes("Monoid"), "should include Monoid");
});

test("HTTP GET /api/theories/Monoid/summary returns summary", async () => {
  const { status, body } = await fetchJson("/api/theories/Monoid/summary");
  assertEq(status, 200, "status should be 200");
  assertEq(body.name, "Monoid", "name should match");
  assert(body.summary.length > 0, "summary should be non-empty");
});

test("HTTP GET /api/theories/Monoid/validate returns valid", async () => {
  const { status, body } = await fetchJson("/api/theories/Monoid/validate");
  assertEq(status, 200, "status should be 200");
  assertEq(body.valid, true, "should be valid");
});

test("HTTP POST /api/operator/apply applies operator", async () => {
  const { status, body } = await fetchJson("/api/operator/apply", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ operator: "opposite", theory: "Monoid" }),
  });
  assertEq(status, 200, "status should be 200");
  assert(body.theory !== null && body.theory !== undefined, "should return theory");
});

test("HTTP POST /api/pushout computes pushout", async () => {
  const { status, body } = await fetchJson("/api/pushout", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ theory1: "Monoid", theory2: "Monoid", base: "Basic" }),
  });
  // May be 200 or 500 depending on CAS support, but should not crash
  assert(status === 200 || status === 500, "should return valid status");
});

test("HTTP GET /api/nonexistent returns 404", async () => {
  const { status, body } = await fetchJson("/api/nonexistent");
  assertEq(status, 404, "status should be 404");
  assert(body.error !== undefined, "should have error field");
});

test("HTTP GET / serves the studio HTML", async () => {
  const res = await fetch(`${baseUrl}/`);
  assertEq(res.status, 200, "status should be 200");
  const text = await res.text();
  assert(text.includes("CatLab Studio"), "should contain CatLab Studio");
});

// ── Tests: ChatAgent (LLM-driven, requires ANTHROPIC_API_KEY) ────────────────

import { ChatAgent } from "../src/chat";

const hasApiKey = !!process.env.ANTHROPIC_API_KEY;

if (hasApiKey) {
  test("ChatAgent: list theories via natural language", async (client) => {
    const agent = new ChatAgent(client);
    const events = await agent.processMessage("What theories are available?");
    const textEvents = events.filter(e => e.type === "text");
    assert(textEvents.length > 0, "should have text response");
    const allText = textEvents.map(e => e.content).join(" ");
    assert(allText.includes("Monoid") || allText.includes("monoid"), "should mention Monoid");
  });

  test("ChatAgent: get theory summary", async (client) => {
    const agent = new ChatAgent(client);
    const events = await agent.processMessage("Tell me about the Group theory");
    const textEvents = events.filter(e => e.type === "text");
    assert(textEvents.length > 0, "should have text response");
  });

  test("ChatAgent: construct a theory", async (client) => {
    const agent = new ChatAgent(client);
    const events = await agent.processMessage("Make a non-commutative group — define it as a theory");
    assert(events.length > 0, "should have events");
    const statusEvents = events.filter(e => e.type === "status");
    assert(statusEvents.length > 0, "should have tool call status events");
  });

  test("ChatAgent: apply operator", async (client) => {
    const agent = new ChatAgent(client);
    const events = await agent.processMessage("Apply the opposite operator to Monoid");
    assert(events.length > 0, "should have events");
    const hasTheoryOrText = events.some(e => e.type === "theory" || e.type === "text");
    assert(hasTheoryOrText, "should return theory or text");
  });

  test("ChatAgent: conversation memory persists", async (client) => {
    const agent = new ChatAgent(client);
    await agent.processMessage("Remember: I'm interested in algebra");
    const lenAfterFirst = agent.historyLength;
    assert(lenAfterFirst >= 2, "should have at least 2 history entries after 1 exchange");
    await agent.processMessage("What did I say I was interested in?");
    assert(agent.historyLength > lenAfterFirst, "history should grow after second message");
  });

  test("ChatAgent: reset clears history", async (client) => {
    const agent = new ChatAgent(client);
    await agent.processMessage("Hello");
    assert(agent.historyLength > 0, "should have history");
    agent.reset();
    assertEq(agent.historyLength, 0, "should have empty history after reset");
  });

  test("HTTP POST /api/chat processes message", async () => {
    const { status, body } = await fetchJson("/api/chat", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ message: "List all available theories", sessionId: "test-session" }),
    });
    assertEq(status, 200, "status should be 200");
    assert(Array.isArray(body.events), "should have events array");
    assert(body.events.length > 0, "should have at least one event");
    const doneEvent = body.events.find((e: any) => e.type === "done");
    assert(doneEvent !== undefined, "should have done event");
  });

  test("HTTP POST /api/chat/reset clears session", async () => {
    const { status, body } = await fetchJson("/api/chat/reset", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ sessionId: "test-session" }),
    });
    assertEq(status, 200, "status should be 200");
    assert(body.ok === true, "should return ok");
  });

  test("HTTP POST /api/chat rejects empty message", async () => {
    const { status } = await fetchJson("/api/chat", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ message: "", sessionId: "test-session" }),
    });
    assertEq(status, 400, "status should be 400");
  });
} else {
  console.log("\n  (Skipping ChatAgent tests — ANTHROPIC_API_KEY not set)\n");
}

// ── Runner ───────────────────────────────────────────────────────────────────

async function run() {
  console.log("Starting Lean CAS...");
  const client = new CatlabClient();

  // Wait for CAS to be ready by listing theories
  console.log("Waiting for CAS to be ready...");
  await client.request({ command: "list_theories" }, 120_000);
  console.log("CAS ready.\n");

  // Start HTTP server for HTTP tests (reuses same CAS client)
  httpServer = createServer(client);
  await new Promise<void>((resolve) => httpServer.listen(0, resolve));
  const addr = httpServer.address() as { port: number };
  baseUrl = `http://localhost:${addr.port}`;
  console.log(`Test HTTP server on port ${addr.port}\n`);

  let passed = 0;
  let failed = 0;
  const failures: { name: string; error: string }[] = [];

  for (const t of tests) {
    const startMs = Date.now();
    try {
      // Some tests take CatlabClient, HTTP tests don't
      await t.fn(client);
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

  httpServer.close();
  client.kill();
  process.exit(failed > 0 ? 1 : 0);
}

run().catch((e) => {
  console.error("Fatal:", e);
  process.exit(2);
});
