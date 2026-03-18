"use strict";
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
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.CatlabClient = void 0;
const child_process_1 = require("child_process");
const readline = __importStar(require("readline"));
const path = __importStar(require("path"));
const crypto_1 = require("crypto");
class CatlabClient {
    /**
     * @param repoRoot  Absolute path to the catlab repo root (where lakefile.toml lives).
     *                  Defaults to two directories up from this file (ts/src/ → catlab/).
     */
    constructor(repoRoot) {
        this.pending = new Map();
        this.closed = false;
        const root = repoRoot ?? path.resolve(__dirname, "../../");
        this.process = (0, child_process_1.spawn)("lake", ["exe", "catlab-repl"], {
            cwd: root,
            stdio: ["pipe", "pipe", "pipe"],
        });
        // stderr → log only (banner, debug output from Lean)
        this.process.stderr.on("data", (data) => {
            process.stderr.write(`[lean] ${data}`);
        });
        // stdout → NDJSON response stream
        const rl = readline.createInterface({ input: this.process.stdout, crlfDelay: Infinity });
        rl.on("line", (line) => {
            if (!line.trim())
                return;
            let response;
            try {
                response = JSON.parse(line);
            }
            catch {
                process.stderr.write(`[catlab-client] Failed to parse Lean output: ${line}\n`);
                return;
            }
            const pending = this.pending.get(response.id);
            if (pending) {
                this.pending.delete(response.id);
                pending.resolve(response);
            }
            else {
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
    async request(command, timeoutMs = 30000) {
        if (this.closed)
            throw new Error("CatlabClient: process has exited");
        return new Promise((resolve, reject) => {
            const id = (0, crypto_1.randomUUID)();
            const timer = setTimeout(() => {
                this.pending.delete(id);
                reject(new Error(`Request "${command.command}" (id=${id}) timed out after ${timeoutMs}ms`));
            }, timeoutMs);
            this.pending.set(id, {
                resolve: (res) => { clearTimeout(timer); resolve(res); },
                reject: (err) => { clearTimeout(timer); reject(err); },
            });
            const payload = { id, ...command };
            this.process.stdin.write(JSON.stringify(payload) + "\n");
        });
    }
    /** Convenience: assert the response is ok, or throw with the error message. */
    async requestOrThrow(command, timeoutMs = 30000) {
        const res = await this.request(command, timeoutMs);
        if (res.status === "error")
            throw new Error(`Lean CAS error: ${res.message}`);
        return res;
    }
    kill() {
        this.process.kill();
    }
}
exports.CatlabClient = CatlabClient;
//# sourceMappingURL=client.js.map