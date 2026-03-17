/-
  CatLab -- Operator Pipeline

  Compose operators into pipelines. This is the CAS "expression evaluator":
  parse a sequence of operations and execute them left-to-right.
-/

import Catlab.Core.Theory
import Catlab.Core.Validate
import Catlab.Core.Equality
import Catlab.Operators.Mirror
import Catlab.Operators.DayConvolution
import Catlab.Operators.Limits
import Catlab.Operators.Yoneda
import Catlab.Operators.Decategorify
import Catlab.Operators.Sheafify
import Catlab.Operators.Localize

namespace CatLab

/-- An operator that transforms theories -/
inductive Op where
  | mirror
  | yoneda
  | presheaf
  | decategorify (strategy : DecatStrategy := .isoClasses)
  | tensor (other : Theory)
  | adjoinProduct (a b : Expr)
  | adjoinCoproduct (a b : Expr)
  | adjoinPullback (f g : Generator1)
  | adjoinPushout (f g : Generator1)
  | adjoinEqualizer (f g : Generator1)
  | adjoinCoequalizer (f g : Generator1)
  deriving Repr, Inhabited

/-- Apply a single operator to a theory -/
def applyOp (t : Theory) (op : Op) : Theory :=
  match op with
  | .mirror => mirror t
  | .yoneda => presheafCategory t
  | .presheaf => presheafCategory t
  | .decategorify s => decategorify t s
  | .tensor other => tensorTheories t other
  | .adjoinProduct a b => t.adjoinLimit (computeProduct a b)
  | .adjoinCoproduct a b => t.adjoinLimit (computeCoproduct a b)
  | .adjoinPullback f g => t.adjoinLimit (computePullback f g)
  | .adjoinPushout f g => t.adjoinLimit (computePushout f g)
  | .adjoinEqualizer f g => t.adjoinLimit (computeEqualizer f g)
  | .adjoinCoequalizer f g => t.adjoinLimit (computeCoequalizer f g)

/-- A pipeline: a sequence of operators applied left-to-right -/
def Pipeline := List Op

/-- Execute a pipeline, optionally validating after each step -/
def executePipeline (t : Theory) (ops : Pipeline) (validateSteps : Bool := false)
    : Theory × List String :=
  ops.foldl (fun (theory, log) op =>
    let result := applyOp theory op
    let stepLog := s!"  {repr op} → {result.name} ({result.objects.length} obj, {result.morphisms.length} mor, {result.axioms.length} ax)"
    if validateSteps then
      let errors := validate result
      if errors.isEmpty then
        (result, log ++ [stepLog ++ " ✓"])
      else
        let errMsg := errors.map toString |> String.intercalate "; "
        (result, log ++ [stepLog ++ s!" ⚠ {errMsg}"])
    else
      (result, log ++ [stepLog])
  ) (t, [s!"Starting from: {t.name}"])

/-- Pretty-print a pipeline execution -/
def pipelineReport (t : Theory) (ops : Pipeline) (validateSteps : Bool := false) : String :=
  let (result, log) := executePipeline t ops validateSteps
  let logStr := log |> String.intercalate "\n"
  s!"Pipeline execution:\n{logStr}\n\nResult: {result.summary}"

end CatLab
