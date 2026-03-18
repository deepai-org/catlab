#!/usr/bin/env node
/**
 * CatLab Studio server — serves the UI and proxies API calls to the Lean CAS.
 *
 * Usage:
 *   ts-node src/server.ts [--port 3000] [--lean /path/to/catlab]
 *
 * API routes:
 *   GET  /api/theories                         → list all theories
 *   GET  /api/theories/:name/summary           → theory summary text
 *   GET  /api/theories/:name/validate          → validate a theory
 *   POST /api/operator/apply                   → { operator, theory }
 *   POST /api/pushout                          → { theory1, theory2, base }
 *   POST /api/evaluate-inverse                 → { target, forwardOp, candidate }
 *   GET  /                                     → serves studio/index.html
 */

import * as http from "http";
import * as fs from "fs";
import * as path from "path";
import { CatlabClient } from "./client";
import * as api from "./api";
import { ChatAgent } from "./chat";

// ── Shared client reference (set by startServer or setClient) ────────────────

let catlab: CatlabClient;

/** Per-session chat agents keyed by session ID */
const chatSessions = new Map<string, ChatAgent>();

function getChatAgent(sessionId: string): ChatAgent {
  let agent = chatSessions.get(sessionId);
  if (!agent) {
    agent = new ChatAgent(catlab);
    chatSessions.set(sessionId, agent);
  }
  return agent;
}

/** Allow tests to inject their own client */
export function setClient(client: CatlabClient) {
  catlab = client;
}

// ── Helpers ──────────────────────────────────────────────────────────────────

function sendJson(res: http.ServerResponse, status: number, data: unknown) {
  const body = JSON.stringify(data);
  res.writeHead(status, {
    "Content-Type": "application/json",
    "Access-Control-Allow-Origin": "*",
    "Content-Length": Buffer.byteLength(body),
  });
  res.end(body);
}

function readBody(req: http.IncomingMessage): Promise<string> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on("data", (c) => chunks.push(c));
    req.on("end", () => resolve(Buffer.concat(chunks).toString()));
    req.on("error", reject);
  });
}

async function parseJsonBody(req: http.IncomingMessage): Promise<Record<string, unknown>> {
  const raw = await readBody(req);
  return JSON.parse(raw);
}

function serveStatic(res: http.ServerResponse, filePath: string, contentType: string) {
  try {
    const data = fs.readFileSync(filePath);
    res.writeHead(200, {
      "Content-Type": contentType,
      "Content-Length": data.length,
    });
    res.end(data);
  } catch {
    res.writeHead(404);
    res.end("Not found");
  }
}

// ── Route matching ───────────────────────────────────────────────────────────

function matchRoute(method: string, url: string): { handler: string; params: Record<string, string> } | null {
  if (method === "GET" && url === "/api/theories") return { handler: "listTheories", params: {} };

  const summaryMatch = url.match(/^\/api\/theories\/([^/]+)\/summary$/);
  if (method === "GET" && summaryMatch) return { handler: "getTheorySummary", params: { name: summaryMatch[1] } };

  const validateMatch = url.match(/^\/api\/theories\/([^/]+)\/validate$/);
  if (method === "GET" && validateMatch) return { handler: "validateTheory", params: { name: validateMatch[1] } };

  if (method === "POST" && url === "/api/operator/apply") return { handler: "applyOperator", params: {} };
  if (method === "POST" && url === "/api/pushout") return { handler: "computePushout", params: {} };
  if (method === "POST" && url === "/api/evaluate-inverse") return { handler: "evaluateInverse", params: {} };
  if (method === "POST" && url === "/api/chat") return { handler: "chat", params: {} };
  if (method === "POST" && url === "/api/chat/reset") return { handler: "chatReset", params: {} };

  return null;
}

// ── Request handler ──────────────────────────────────────────────────────────

export async function handleRequest(
  req: http.IncomingMessage,
  res: http.ServerResponse
): Promise<void> {
  const method = req.method ?? "GET";
  const url = (req.url ?? "/").split("?")[0];

  // CORS preflight
  if (method === "OPTIONS") {
    res.writeHead(204, {
      "Access-Control-Allow-Origin": "*",
      "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
      "Access-Control-Allow-Headers": "Content-Type",
    });
    res.end();
    return;
  }

  // Static files
  if (method === "GET" && (url === "/" || url === "/index.html")) {
    const studioPath = path.resolve(__dirname, "../../studio/index.html");
    serveStatic(res, studioPath, "text/html; charset=utf-8");
    return;
  }

  // API routes
  const route = matchRoute(method, url);
  if (!route) {
    sendJson(res, 404, { error: "Not found" });
    return;
  }

  try {
    let result;
    switch (route.handler) {
      case "listTheories":
        result = await api.listTheories(catlab);
        break;
      case "getTheorySummary":
        result = await api.getTheorySummary(catlab, decodeURIComponent(route.params.name));
        break;
      case "validateTheory":
        result = await api.validateTheory(catlab, decodeURIComponent(route.params.name));
        break;
      case "applyOperator": {
        const body = await parseJsonBody(req);
        result = await api.applyOperator(catlab, body.operator as string, body.theory as string);
        break;
      }
      case "computePushout": {
        const body = await parseJsonBody(req);
        result = await api.computePushout(
          catlab,
          body.theory1 as string,
          body.theory2 as string,
          body.base as string
        );
        break;
      }
      case "evaluateInverse": {
        const body = await parseJsonBody(req);
        result = await api.evaluateInverse(
          catlab,
          body.target as string,
          body.forwardOp as string,
          body.candidate as any
        );
        break;
      }
      case "chat": {
        const body = await parseJsonBody(req);
        const sessionId = (body.sessionId as string) || "default";
        const message = body.message as string;
        if (!message) {
          sendJson(res, 400, { error: "message required" });
          return;
        }
        const agent = getChatAgent(sessionId);
        const events = await agent.processMessage(message);
        sendJson(res, 200, { events });
        return;
      }
      case "chatReset": {
        const body = await parseJsonBody(req);
        const sessionId = (body.sessionId as string) || "default";
        chatSessions.delete(sessionId);
        sendJson(res, 200, { ok: true });
        return;
      }
      default:
        sendJson(res, 500, { error: "Unknown handler" });
        return;
    }

    if (result.ok) {
      sendJson(res, 200, result.data);
    } else {
      sendJson(res, result.error.status, { error: result.error.error });
    }
  } catch (e) {
    sendJson(res, 500, { error: (e as Error).message });
  }
}

// ── Server startup ───────────────────────────────────────────────────────────

export function createServer(client: CatlabClient): http.Server {
  catlab = client;
  return http.createServer(handleRequest);
}

if (require.main === module) {
  let port = 3000;
  let repoRoot: string | undefined;
  const cliArgs = process.argv.slice(2);
  for (let i = 0; i < cliArgs.length; i++) {
    if (cliArgs[i] === "--port") port = parseInt(cliArgs[++i], 10);
    if (cliArgs[i] === "--lean") repoRoot = cliArgs[++i];
  }

  catlab = new CatlabClient(repoRoot);
  const server = http.createServer(handleRequest);
  server.listen(port, () => {
    console.log(`CatLab Studio running at http://localhost:${port}`);
    console.log(`API available at http://localhost:${port}/api/theories`);
  });

  process.on("SIGINT", () => {
    console.log("\nShutting down...");
    catlab.kill();
    server.close();
    process.exit(0);
  });
}
