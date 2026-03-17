/-
  CatLab -- REPL Protocol

  JSON-RPC interface for the TypeScript orchestrator to communicate
  with the Lean 4 CAS engine. The orchestrator sends theory ASTs
  and operator commands; Lean executes them and returns results.
-/

import Catlab.Core.Theory
import Catlab.Operators.Mirror
import Catlab.Operators.DayConvolution
import Catlab.Operators.Limits
import Catlab.Operators.Decategorify
import Catlab.Operators.Localize
import Catlab.Operators.Sheafify

namespace CatLab.Repl

/-- The operations the orchestrator can request -/
inductive Command where
  | mirror (theory : String)
  | tensor (theory1 theory2 : String)
  | slice (theory : String) (object : String)
  | pullback (theory : String) (f g : String)
  | pushout (theory : String) (f g : String)
  | yoneda (theory : String)
  | grothendieck (theory : String)
  | leftKan (functor : String) (diagram : String)
  | rightKan (functor : String) (diagram : String)
  | sheafify (theory : String) (topology : String)
  | localize (theory : String) (weakEquivs : List String)
  | decategorify (theory : String) (strategy : String)
  | verifyCategorification (candidate : String) (target : String)
  | summary (theory : String)
  deriving Repr, Inhabited

/-- Result of a command execution -/
inductive CommandResult where
  | success (theory : Theory) (message : String)
  | error (message : String)
  deriving Repr, Inhabited

/-- Format a theory as a simple JSON-like string for the orchestrator -/
def theoryToJson (t : Theory) : String :=
  let objs := t.objects.map (fun o => s!"\"{o.id.name}\"") |> String.intercalate ", "
  let mors := t.morphisms.map (fun m => s!"\"{m.id.name}\"") |> String.intercalate ", "
  let axs := t.axioms.map (fun a => s!"\"{a.id.name}\"") |> String.intercalate ", "
  s!"\{\"name\": \"{t.name}\", " ++
  s!"\"doctrine\": \"{repr t.doctrine.doctrine}\", " ++
  s!"\"objects\": [{objs}], " ++
  s!"\"morphisms\": [{mors}], " ++
  s!"\"axioms\": [{axs}]}"

/-- Format a command result for the orchestrator -/
def resultToJson : CommandResult → String
  | .success t msg => s!"\{\"status\": \"success\", \"message\": \"{msg}\", \"theory\": {theoryToJson t}}"
  | .error msg => s!"\{\"status\": \"error\", \"message\": \"{msg}\"}"

end CatLab.Repl
