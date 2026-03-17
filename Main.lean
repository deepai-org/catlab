import Catlab.Repl.Server

def main : IO Unit := do
  IO.println "CatLab v0.1.0 — Categorical Computer Algebra System"
  IO.println "Type 'help' for commands, 'quit' to exit."
  IO.println ""
  CatLab.Repl.replLoop
