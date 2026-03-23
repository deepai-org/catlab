/**
 * CatlabClient — IPC wrapper for the Lean NDJSON REPL.
 *
 * Spawns `lake exe catlab-repl`, writes one JSON request per line to stdin,
 * reads one JSON response per line from stdout, and maps responses to the
 * original Promise by request ID. The request ID queue handles the
 * asynchronous mismatch between when we send and when Lean replies.
 *
 * Key design decisions:
 *   - Response ID must match request ID: the Lean server echoes the id field.
 *   - stdout is pure NDJSON; banner/logs go to stderr only.
 *   - Each request gets an individual timeout to prevent indefinite hangs.
 */

import { spawn, ChildProcessWithoutNullStreams } from "child_process";
import * as readline from "readline";
import * as path from "path";
import { randomUUID } from "crypto";
import type { CatlabCommand, CatlabRequest, CatlabResponse } from "./types";

interface PendingRequest {
  resolve: (res: CatlabResponse) => void;
  reject: (err: Error) => void;
}

export class CatlabClient {
  private process: ChildProcessWithoutNullStreams;
  private pending = new Map<string, PendingRequest>();
  private closed = false;

  /**
   * @param repoRoot  Absolute path to the catlab repo root (where lakefile.toml lives).
   *                  Defaults to two directories up from this file (ts/src/ → catlab/).
   */
  constructor(repoRoot?: string) {
    const root = repoRoot ?? path.resolve(__dirname, "../../");

    // Use the pre-built binary directly — avoids the 30-60s lake build-system
    // check on every run. Falls back to `lake exe catlab-repl` if not found.
    const binaryPath = path.join(root, ".lake/build/bin/catlab-repl");
    const [cmd, args] = require("fs").existsSync(binaryPath)
      ? [binaryPath, [] as string[]]
      : ["lake", ["exe", "catlab-repl"]];

    this.process = spawn(cmd, args, {
      cwd: root,
      stdio: ["pipe", "pipe", "pipe"],
    });

    // stderr → log only (banner, debug output from Lean)
    this.process.stderr.on("data", (data: Buffer) => {
      process.stderr.write(`[lean] ${data}`);
    });

    // stdout → NDJSON response stream
    const rl = readline.createInterface({ input: this.process.stdout, crlfDelay: Infinity });

    rl.on("line", (line) => {
      if (!line.trim()) return;
      let response: CatlabResponse;
      try {
        response = JSON.parse(line) as CatlabResponse;
      } catch {
        process.stderr.write(`[catlab-client] Failed to parse Lean output: ${line}\n`);
        return;
      }
      const pending = this.pending.get(response.id);
      if (pending) {
        this.pending.delete(response.id);
        pending.resolve(response);
      } else {
        process.stderr.write(`[catlab-client] Unmatched response id: ${response.id}\n`);
      }
    });

    this.process.on("close", (code) => {
      this.closed = true;
      // Reject all pending requests if the process exits unexpectedly
      for (const [id, pending] of this.pending) {
        pending.reject(new Error(`Lean process exited with code ${code} while request ${id} was pending`));
      }
      this.pending.clear();
    });

    this.process.on("error", (err) => {
      process.stderr.write(`[catlab-client] Process error: ${err.message}\n`);
      this.closed = true;
      for (const [, pending] of this.pending) {
        pending.reject(err);
      }
      this.pending.clear();
    });
  }

  /**
   * Send a command to the Lean REPL and wait for the matched response.
   *
   * @param command     The command payload (without the id field)
   * @param timeoutMs   Per-request timeout. Default 30s.
   */
  async request(command: CatlabCommand, timeoutMs = 30_000): Promise<CatlabResponse> {
    if (this.closed) throw new Error("CatlabClient: process has exited");

    return new Promise<CatlabResponse>((resolve, reject) => {
      const id = randomUUID();

      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`Request "${(command as CatlabRequest).command}" (id=${id}) timed out after ${timeoutMs}ms`));
      }, timeoutMs);

      this.pending.set(id, {
        resolve: (res) => { clearTimeout(timer); resolve(res); },
        reject:  (err) => { clearTimeout(timer); reject(err); },
      });

      const payload: CatlabRequest = { id, ...command };
      this.process.stdin.write(JSON.stringify(payload) + "\n");
    });
  }

  /** Convenience: assert the response is ok, or throw with the error message. */
  async requestOrThrow(command: CatlabCommand, timeoutMs = 30_000): Promise<Extract<CatlabResponse, { status: "ok" }>> {
    const res = await this.request(command, timeoutMs);
    if (res.status === "error") throw new Error(`Lean CAS error: ${res.message}`);
    return res as Extract<CatlabResponse, { status: "ok" }>;
  }

  /** Register a user-defined theory in the Lean runtime registry. */
  async defineTheory(theory: import("./types").TheoryJson, timeoutMs = 30_000): Promise<CatlabResponse> {
    return this.requestOrThrow({ command: "define_theory", theory }, timeoutMs);
  }

  kill() {
    this.process.kill();
  }
}
