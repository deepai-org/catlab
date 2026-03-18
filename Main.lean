import Catlab.Repl.Server

def main : IO Unit := do
  -- Banner to stderr only — stdout is reserved for NDJSON responses.
  -- The TypeScript orchestrator reads stdout line-by-line as JSON;
  -- any non-JSON on stdout would break readline parsing.
  IO.eprintln "CatLab v0.1.0 — NDJSON mode (stderr=log, stdout=JSON)"
  CatLab.Repl.ndjsonLoop
