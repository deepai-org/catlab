/**
 * API layer — pure functions that map HTTP-shaped requests to CatlabClient calls.
 * No HTTP dependency: fully testable with a mock or real CatlabClient.
 */

import type { CatlabClient } from "./client";
import type { CatlabResponse, TheoryJson } from "./types";

// ── Request/Response shapes (framework-agnostic) ─────────────────────────────

export interface ApiError {
  error: string;
  status: number;
}

export type ApiResult<T> = { ok: true; data: T } | { ok: false; error: ApiError };

function ok<T>(data: T): ApiResult<T> {
  return { ok: true, data };
}

function err<T>(status: number, message: string): ApiResult<T> {
  return { ok: false, error: { error: message, status } };
}

function unwrap(res: CatlabResponse): CatlabResponse & { status: "ok" } {
  if (res.status === "error") throw new Error(res.message);
  return res as CatlabResponse & { status: "ok" };
}

// ── API handlers ─────────────────────────────────────────────────────────────

export async function listTheories(
  client: CatlabClient,
  timeoutMs = 30_000
): Promise<ApiResult<{ theories: string[] }>> {
  try {
    const res = unwrap(await client.request({ command: "list_theories" }, timeoutMs));
    return ok({ theories: res.theories ?? [] });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}

export async function listOperators(
  client: CatlabClient,
  timeoutMs = 30_000
): Promise<ApiResult<{ operators: unknown[] }>> {
  try {
    const res = unwrap(await client.request({ command: "list_operators" }, timeoutMs));
    return ok({ operators: res.operators ?? [] });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}

export async function getTheorySummary(
  client: CatlabClient,
  theoryName: string,
  timeoutMs = 30_000
): Promise<ApiResult<{ name: string; summary: string; theory?: TheoryJson }>> {
  if (!theoryName) return err(400, "theory name required");
  try {
    const res = unwrap(await client.request({ command: "summary", theory: theoryName }, timeoutMs));
    return ok({ name: theoryName, summary: res.summary ?? "", theory: res.theory });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}

export async function validateTheory(
  client: CatlabClient,
  theoryName: string,
  timeoutMs = 30_000
): Promise<ApiResult<{ valid: boolean; errors: string[] }>> {
  if (!theoryName) return err(400, "theory name required");
  try {
    const res = unwrap(await client.request({ command: "validate", theory: theoryName }, timeoutMs));
    return ok({ valid: res.valid ?? false, errors: res.errors ?? [] });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}

export async function applyOperator(
  client: CatlabClient,
  operator: string,
  theory: string,
  timeoutMs = 30_000
): Promise<ApiResult<{ theory: TheoryJson | null; message?: string }>> {
  if (!operator) return err(400, "operator required");
  if (!theory) return err(400, "theory required");
  try {
    const res = unwrap(
      await client.request({ command: "apply_operator", operator, theory }, timeoutMs)
    );
    return ok({ theory: res.theory ?? null, message: res.message });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}

export async function computePushout(
  client: CatlabClient,
  theory1: string,
  theory2: string,
  base: string,
  timeoutMs = 30_000
): Promise<ApiResult<{ theory: TheoryJson | null; message?: string }>> {
  if (!theory1 || !theory2 || !base) return err(400, "theory1, theory2, and base required");
  try {
    const res = unwrap(
      await client.request({ command: "compute_pushout", theory1, theory2, base }, timeoutMs)
    );
    return ok({ theory: res.theory ?? null, message: res.message });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}

export async function submitTheory(
  client: CatlabClient,
  theory: TheoryJson,
  timeoutMs = 30_000
): Promise<ApiResult<{ valid: boolean; errors: string[]; theory: TheoryJson }>> {
  if (!theory || !theory.name) return err(400, "theory with name required");
  try {
    const res = unwrap(
      await client.request({ command: "validate", theory: JSON.stringify(theory) }, timeoutMs)
    );
    return ok({
      valid: res.valid ?? false,
      errors: res.errors ?? [],
      theory,
    });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}

export async function evaluateInverse(
  client: CatlabClient,
  target: string,
  forwardOp: string,
  candidate: TheoryJson,
  timeoutMs = 30_000
): Promise<ApiResult<{ result: unknown }>> {
  if (!target || !forwardOp || !candidate) return err(400, "target, forward_op, and candidate required");
  try {
    const res = unwrap(
      await client.request(
        { command: "evaluate_inverse", target, forward_op: forwardOp, candidate },
        timeoutMs
      )
    );
    return ok({ result: res.result ?? null });
  } catch (e) {
    return err(500, (e as Error).message);
  }
}
