/**
 * Unit tests for CatlabClient NDJSON protocol handling.
 *
 * Uses a fake REPL binary placed at .lake/build/bin/catlab-repl in a temp
 * directory so CatlabClient picks it up instead of the real Lean binary.
 *
 * Run:
 *   npx ts-node test/client.test.ts
 */

import { CatlabClient } from "../src/client";
import * as fs from "fs";
import * as path from "path";
import * as os from "os";

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

// ── Mock REPL helpers ────────────────────────────────────────────────────────

/** Create a temp dir with a fake catlab-repl binary running the given Node script. */
function makeMockRepl(script: string): { root: string; cleanup: () => void } {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "catlab-test-"));
  const binDir = path.join(root, ".lake", "build", "bin");
  fs.mkdirSync(binDir, { recursive: true });
  const binPath = path.join(binDir, "catlab-repl");
  // Write a shell script that invokes node with the inline script
  fs.writeFileSync(binPath, `#!/usr/bin/env node\n${script}\n`, { mode: 0o755 });
  return {
    root,
    cleanup: () => fs.rmSync(root, { recursive: true, force: true }),
  };
}

/** Standard echo REPL: parses each line as JSON, echoes back with status "ok". */
const ECHO_SCRIPT = `
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });
rl.on('line', (line) => {
  try {
    const req = JSON.parse(line);
    const res = { id: req.id, status: "ok", theories: ["Monoid", "Category"] };
    process.stdout.write(JSON.stringify(res) + '\\n');
  } catch {}
});
`;

// ── Tests ────────────────────────────────────────────────────────────────────

test("normal request/response", async () => {
  const mock = makeMockRepl(ECHO_SCRIPT);
  try {
    const client = new CatlabClient(mock.root);
    const res = await client.request({ command: "list_theories" }, 5000);
    assertEq(res.status, "ok", "status");
    assert("theories" in res && Array.isArray((res as any).theories), "should have theories");
    client.kill();
  } finally {
    mock.cleanup();
  }
});

test("multiple concurrent requests all resolve correctly", async () => {
  // Delayed echo: waits a random 10-50ms before responding
  const script = `
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });
rl.on('line', (line) => {
  try {
    const req = JSON.parse(line);
    const delay = 10 + Math.floor(Math.random() * 40);
    setTimeout(() => {
      const res = { id: req.id, status: "ok", echo: req.command };
      process.stdout.write(JSON.stringify(res) + '\\n');
    }, delay);
  } catch {}
});
`;
  const mock = makeMockRepl(script);
  try {
    const client = new CatlabClient(mock.root);
    const commands = [
      { command: "list_theories" as const },
      { command: "list_operators" as const },
      { command: "summary" as const, theory: "Monoid" },
    ];
    const results = await Promise.all(commands.map((c) => client.request(c, 5000)));
    assertEq(results.length, 3, "should get 3 results");
    for (const r of results) {
      assertEq(r.status, "ok", "each result should be ok");
    }
    client.kill();
  } finally {
    mock.cleanup();
  }
});

test("request times out when REPL does not respond", async () => {
  // Silent REPL: reads stdin but never writes anything back
  const script = `
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });
rl.on('line', () => {}); // swallow input
`;
  const mock = makeMockRepl(script);
  try {
    const client = new CatlabClient(mock.root);
    let threw = false;
    try {
      await client.request({ command: "list_theories" }, 200);
    } catch (e: any) {
      threw = true;
      assert(e.message.includes("timed out"), "error should mention timeout");
    }
    assert(threw, "should have thrown on timeout");
    client.kill();
  } finally {
    mock.cleanup();
  }
});

test("malformed JSON response does not crash client", async () => {
  // Sends garbage first, then a valid response
  const script = `
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });
let count = 0;
rl.on('line', (line) => {
  try {
    const req = JSON.parse(line);
    count++;
    if (count === 1) {
      process.stdout.write('this is not json\\n');
      // Send valid response after garbage
      setTimeout(() => {
        process.stdout.write(JSON.stringify({ id: req.id, status: "ok" }) + '\\n');
      }, 50);
    } else {
      process.stdout.write(JSON.stringify({ id: req.id, status: "ok" }) + '\\n');
    }
  } catch {}
});
`;
  const mock = makeMockRepl(script);
  try {
    const client = new CatlabClient(mock.root);
    // First request: garbage line is skipped, valid response arrives
    const res = await client.request({ command: "list_theories" }, 5000);
    assertEq(res.status, "ok", "should still get ok response");
    // Second request works fine
    const res2 = await client.request({ command: "list_theories" }, 5000);
    assertEq(res2.status, "ok", "second request should work");
    client.kill();
  } finally {
    mock.cleanup();
  }
});

test("process exit rejects pending requests", async () => {
  // Exits immediately after receiving first line
  const script = `
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });
rl.on('line', () => {
  process.exit(1);
});
`;
  const mock = makeMockRepl(script);
  try {
    const client = new CatlabClient(mock.root);
    let threw = false;
    try {
      await client.request({ command: "list_theories" }, 5000);
    } catch (e: any) {
      threw = true;
      assert(e.message.includes("exited"), "error should mention process exit");
    }
    assert(threw, "should have thrown when process exits");
  } finally {
    mock.cleanup();
  }
});

test("requestOrThrow throws on error response", async () => {
  const script = `
const readline = require('readline');
const rl = readline.createInterface({ input: process.stdin });
rl.on('line', (line) => {
  try {
    const req = JSON.parse(line);
    const res = { id: req.id, status: "error", message: "unknown theory" };
    process.stdout.write(JSON.stringify(res) + '\\n');
  } catch {}
});
`;
  const mock = makeMockRepl(script);
  try {
    const client = new CatlabClient(mock.root);
    let threw = false;
    try {
      await client.requestOrThrow({ command: "summary", theory: "Nonexistent" }, 5000);
    } catch (e: any) {
      threw = true;
      assert(e.message.includes("unknown theory"), "error should contain CAS message");
    }
    assert(threw, "requestOrThrow should throw on error response");
    client.kill();
  } finally {
    mock.cleanup();
  }
});

test("requestOrThrow returns data on ok response", async () => {
  const mock = makeMockRepl(ECHO_SCRIPT);
  try {
    const client = new CatlabClient(mock.root);
    const res = await client.requestOrThrow({ command: "list_theories" }, 5000);
    assertEq(res.status, "ok", "status should be ok");
    client.kill();
  } finally {
    mock.cleanup();
  }
});

test("request after kill throws", async () => {
  const mock = makeMockRepl(ECHO_SCRIPT);
  try {
    const client = new CatlabClient(mock.root);
    // Verify it works first
    await client.request({ command: "list_theories" }, 5000);
    client.kill();
    // Wait a tick for the close event to fire
    await new Promise((r) => setTimeout(r, 100));
    let threw = false;
    try {
      await client.request({ command: "list_theories" }, 5000);
    } catch (e: any) {
      threw = true;
      assert(e.message.includes("exited"), "error should mention process has exited");
    }
    assert(threw, "should throw after kill");
  } finally {
    mock.cleanup();
  }
});

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
      console.log(`  \u2713 ${t.name} (${ms}ms)`);
      passed++;
    } catch (e) {
      const ms = Date.now() - startMs;
      const msg = (e as Error).message;
      console.log(`  \u2717 ${t.name} (${ms}ms)`);
      console.log(`    ${msg}`);
      failed++;
      failures.push({ name: t.name, error: msg });
    }
  }

  console.log(`\n${passed} passed, ${failed} failed, ${tests.length} total`);

  if (failures.length > 0) {
    console.log("\nFailures:");
    for (const f of failures) {
      console.log(`  \u2717 ${f.name}: ${f.error}`);
    }
  }

  process.exit(failed > 0 ? 1 : 0);
}

run().catch((e) => {
  console.error("Fatal:", e);
  process.exit(2);
});
