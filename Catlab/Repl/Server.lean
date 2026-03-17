/-
  CatLab -- REPL Server

  A simple line-based REPL that reads commands from stdin and
  writes JSON results to stdout. The TypeScript orchestrator
  communicates with this process over stdio.

  Usage: lake exe catlab-repl
-/

import Catlab.Core.Theory
import Catlab.Operators.Mirror
import Catlab.Operators.DayConvolution
import Catlab.Operators.Limits
import Catlab.Operators.Decategorify
import Catlab.Core.Validate
import Catlab.Core.PrettyPrint
import Catlab.Repl.Protocol
import Catlab.Library.Monoid
import Catlab.Library.Group
import Catlab.Library.Ring
import Catlab.Library.BooleanAlgebra
import Catlab.Library.Basic

namespace CatLab.Repl

open CatLab.Library

/-- Registry of built-in theories -/
def theoryRegistry : List (String × Theory) :=
  [ ("Monoid", TheoryOfMonoids),
    ("Group", TheoryOfGroups),
    ("AbelianGroup", TheoryOfAbelianGroups),
    ("Ring", TheoryOfRings),
    ("CommutativeRing", TheoryOfCommutativeRings),
    ("BooleanAlgebra", TheoryOfBooleanAlgebra),
    ("HeytingAlgebra", TheoryOfHeytingAlgebra),
    ("Poset", TheoryOfPosets),
    ("Lattice", TheoryOfLattices),
    ("Semiring", TheoryOfSemirings),
    ("Category", TheoryOfCategories) ]

/-- Look up a theory by name -/
def lookupTheory (name : String) : Option Theory :=
  (theoryRegistry.find? (fun (n, _) => n == name)).map Prod.snd

/-- Execute a simple text command -/
def executeCommand (input : String) : String :=
  let parts := input.trimAscii.toString.splitOn " "
  match parts with
  | ["summary", name] =>
    match lookupTheory name with
    | some t => resultToJson (.success t (t.summary))
    | none => resultToJson (.error s!"Theory '{name}' not found")

  | ["mirror", name] =>
    match lookupTheory name with
    | some t =>
      let result := mirror t
      resultToJson (.success result s!"Computed {result.name}")
    | none => resultToJson (.error s!"Theory '{name}' not found")

  | ["tensor", name1, name2] =>
    match lookupTheory name1, lookupTheory name2 with
    | some t1, some t2 =>
      let result := tensorTheories t1 t2
      resultToJson (.success result s!"Computed {result.name}")
    | none, _ => resultToJson (.error s!"Theory '{name1}' not found")
    | _, none => resultToJson (.error s!"Theory '{name2}' not found")

  | ["decategorify", name] =>
    match lookupTheory name with
    | some t =>
      let result := decategorify t
      resultToJson (.success result s!"Computed {result.name}")
    | none => resultToJson (.error s!"Theory '{name}' not found")

  | ["validate", name] =>
    match lookupTheory name with
    | some t => resultToJson (.error (validationReport t))
    | none => resultToJson (.error s!"Theory '{name}' not found")

  | ["pretty", name] =>
    match lookupTheory name with
    | some t => resultToJson (.error (t.pp))
    | none => resultToJson (.error s!"Theory '{name}' not found")

  | ["list"] =>
    let names := theoryRegistry.map Prod.fst |> String.intercalate ", "
    resultToJson (.error s!"Available theories: {names}")

  | ["help"] =>
    resultToJson (.error "Commands: summary <name>, mirror <name>, tensor <name1> <name2>, decategorify <name>, validate <name>, pretty <name>, list, help, quit")

  | ["quit"] => "quit"

  | _ => resultToJson (.error s!"Unknown command: {input.trimAscii.toString}")

/-- Main REPL loop -/
partial def replLoop : IO Unit := do
  IO.print "catlab> "
  let stdout ← IO.getStdout
  stdout.flush
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.trimAscii.toString == "quit" || line.isEmpty then
    IO.println "Goodbye."
    return
  let result := executeCommand line
  IO.println result
  replLoop

end CatLab.Repl
