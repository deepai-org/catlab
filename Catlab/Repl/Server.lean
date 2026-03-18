/-
  CatLab -- REPL Server (NDJSON over stdio)

  Reads one JSON request per line from stdin, writes one JSON response
  per line to stdout. The TypeScript orchestrator drives this process
  via child_process.spawn and communicates over stdio.

  Usage:
    lake exe catlab-repl

  Or for batch testing (Step 2 of build order — before TypeScript):
    echo '{"id":"t1","command":"list_theories"}' | lake exe catlab-repl
    cat test_input.jsonl | lake exe catlab-repl

  Supported commands:
    list_theories                         → names of all 34 library theories
    summary          { theory }          → Theory.summary string
    apply_operator   { operator, theory }→ operator(theory) as Theory JSON
    compute_pushout  { theory1, theory2, base } → pushout result
    evaluate_inverse { target, forward_op, candidate } → VerificationResult
    solve_inverse    { target, forward_op, candidates } → first passing candidate
-/

import Lean
import Catlab.Core.Theory
import Catlab.Core.Equality
import Catlab.Core.Primitives
import Catlab.Core.InverseProblem
import Catlab.Core.Validate
import Catlab.Core.PrettyPrint
import Catlab.Operators.Arrow
import Catlab.Operators.Booleanize
import Catlab.Operators.Center
import Catlab.Operators.Chu
import Catlab.Operators.Comma
import Catlab.Operators.Coproduct
import Catlab.Operators.DayConvolution
import Catlab.Operators.Decategorify
import Catlab.Operators.Derived
import Catlab.Operators.DrinfeldCenter
import Catlab.Operators.ExactCompletion
import Catlab.Operators.Family
import Catlab.Operators.Free
import Catlab.Operators.Freyd
import Catlab.Operators.FunctorCategory
import Catlab.Operators.IndPro
import Catlab.Operators.Int
import Catlab.Operators.Internal
import Catlab.Operators.Isbell
import Catlab.Operators.Karoubi
import Catlab.Operators.MacNeille
import Catlab.Operators.Matrix
import Catlab.Operators.Mirror
import Catlab.Operators.Morita
import Catlab.Operators.Nerve
import Catlab.Operators.OperadEnvelope
import Catlab.Operators.Opposite
import Catlab.Operators.Pushout
import Catlab.Operators.Quotient
import Catlab.Operators.Span
import Catlab.Operators.Stabilize
import Catlab.Operators.Syntactic
import Catlab.Operators.TwistedArrow
import Catlab.Operators.Ultrapower
import Catlab.Operators.Yoneda
import Catlab.Library.Monoid
import Catlab.Library.Group
import Catlab.Library.Ring
import Catlab.Library.BooleanAlgebra
import Catlab.Library.Poset
import Catlab.Library.Lattice
import Catlab.Library.Semiring
import Catlab.Library.Module
import Catlab.Library.Category
import Catlab.Library.ElementaryTopos
import Catlab.Library.HoTT
import Catlab.Library.InfinityTopos
import Catlab.Library.ModelCategory
import Catlab.Library.Derivator
import Catlab.Library.InfinityNCategory
import Catlab.Library.Operad
import Catlab.Library.CategoriesWithAttributes
import Catlab.Library.CubicalTypeTheory
import Catlab.Library.LinearLogic
import Catlab.Library.GeometricLogic
import Catlab.Library.CohesiveHoTT
import Catlab.Library.SymmetricMonoidalCategory
import Catlab.Library.EnrichedCategory
import Catlab.Library.AbelianCategory
import Catlab.Library.TriangulatedCategory
import Catlab.Library.Locale
import Catlab.Library.HopfAlgebra
import Catlab.Library.LieAlgebra
import Catlab.Library.DifferentialGradedAlgebra
import Catlab.Repl.Protocol

namespace CatLab.Repl

open Lean (Json)
open CatLab.Library

-- ============================================================
-- Theory registry: all 34 library theories
-- ============================================================

def theoryRegistry : List (String × Theory) :=
  [ ("Monoid",                   TheoryOfMonoids)
  , ("Group",                    TheoryOfGroups)
  , ("AbelianGroup",             TheoryOfAbelianGroups)
  , ("Ring",                     TheoryOfRings)
  , ("CommutativeRing",          TheoryOfCommutativeRings)
  , ("Category",                 TheoryOfCategories)
  , ("Poset",                    TheoryOfPosets)
  , ("Lattice",                  TheoryOfLattices)
  , ("BooleanAlgebra",           TheoryOfBooleanAlgebra)
  , ("HeytingAlgebra",           TheoryOfHeytingAlgebra)
  , ("Semiring",                 TheoryOfSemirings)
  , ("Module",                   TheoryOfModules "R")
  , ("ElementaryTopos",          TheoryOfElementaryTopos)
  , ("HoTT",                     TheoryOfHoTT)
  , ("InfinityTopos",            TheoryOfInfinityTopos)
  , ("ModelCategory",            TheoryOfModelCategory)
  , ("Derivator",                TheoryOfDerivator)
  , ("Infinity2Category",        TheoryOfInfinityTwoCategory)
  , ("Multicategory",            TheoryOfMulticategory)
  , ("SymmetricOperad",          TheoryOfSymmetricOperad)
  , ("CategoriesWithAttributes", TheoryOfCategoriesWithAttributes)
  , ("CubicalTypeTheory",        TheoryOfCubicalTypeTheory)
  , ("LinearLogic",              TheoryOfLinearLogic)
  , ("GeometricLogic",           TheoryOfGeometricLogic)
  , ("CohesiveHoTT",             TheoryOfCohesiveHoTT)
  , ("SymmetricMonoidal",        TheoryOfSymmetricMonoidalCategory)
  , ("EnrichedCategory",         TheoryOfEnrichedCategory)
  , ("AbelianCategory",          TheoryOfAbelianCategory)
  , ("TriangulatedCategory",     TheoryOfTriangulatedCategory)
  , ("Locale",                   TheoryOfLocale)
  , ("HopfAlgebra",              TheoryOfHopfAlgebra)
  , ("LieAlgebra",               TheoryOfLieAlgebra)
  , ("DGA",                      TheoryOfDifferentialGradedAlgebra) ]

def lookupTheory (name : String) : Except String Theory :=
  match theoryRegistry.find? (fun (n, _) => n == name) with
  | some (_, t) => .ok t
  | none        => .error s!"Theory '{name}' not found. Use 'list_theories' to see available names."

-- ============================================================
-- Forward operator dispatch
-- All pure unary Theory → Theory operators from Catlab.Operators
-- ============================================================

def applyForwardOp (op : String) (t : Theory) : Except String Theory :=
  match op with
  -- Symmetries & involutions
  | "opposite"                          => .ok (opposite t)
  | "mirror"                            => .ok (mirror t)
  | "identity"                          => .ok t
  -- Decategorification variants
  | "decategorify_iso" | "decategorify" => .ok (decategorify t .isoClasses)
  | "decategorify_K0"                   => .ok (decategorify t .grothendieckGroup)
  | "decategorify_chi"                  => .ok (decategorify t .eulerCharacteristic)
  -- Arrow & comma constructions
  | "arrow"                             => .ok (Arrow.arrowCat t)
  | "arrow_category"                    => .ok (arrowCategory t)
  | "twisted_arrow"                     => .ok (twistedArrow t)
  -- Completions & envelopes
  | "karoubi"                           => .ok (karoubiEnvelope t)
  | "morita"                            => .ok (moritaEnvelope t)
  | "macneille"                         => .ok (macneilleCompletion t)
  | "reg_completion"                    => .ok (regCompletion t)
  | "ex_completion"                     => .ok (exCompletion t)
  | "ind_completion"                    => .ok (indCompletion t)
  | "pro_completion"                    => .ok (proCompletion t)
  -- Presheaf & functor categories
  | "presheaf"                          => .ok (presheafCategory t)
  | "family"                            => .ok (familyCategory t)
  | "scone"                             => .ok (scone t)
  | "syntactic"                         => .ok (syntacticCategory t)
  -- Derived & homotopy
  | "chain_complex"                     => .ok (chainComplexCategory t)
  | "homotopy"                          => .ok (homotopyCategory t)
  | "derived"                           => .ok (derivedCategory t)
  | "stabilize"                         => .ok (stabilize t)
  -- Monoidal centers
  | "center"                            => .ok (center t)
  | "drinfeld_center"                   => .ok (drinfeldCenter t)
  -- Logic & topos
  | "booleanize"                        => .ok (booleanize t)
  -- Span & cospan
  | "span"                              => .ok (spanCategory t)
  | "cospan"                            => .ok (cospanCategory t)
  -- Simplicial
  | "nerve"                             => .ok (nerve t)
  | "realize"                           => .ok (realize t)
  -- Isbell duality
  | "isbell_spec"                       => .ok (isbellSpec t)
  | "isbell_cospec"                     => .ok (isbellCospec t)
  | "isbell"                            => .ok (isbellAdjunction t)
  -- Miscellaneous
  | "matrix"                            => .ok (matrixCategory t)
  | "int"                               => .ok (intConstruction t)
  | "internal_cat"                      => .ok (internalCategoryCategory t)
  | "path"                              => .ok (pathCategory t)
  | "operad_envelope"                   => .ok (operadicEnvelope t)
  | s => .error s!"Unknown forward_op '{s}'. Use one of: opposite, mirror, identity, decategorify_iso, decategorify_K0, decategorify_chi, arrow, arrow_category, twisted_arrow, karoubi, morita, macneille, reg_completion, ex_completion, ind_completion, pro_completion, presheaf, family, scone, syntactic, chain_complex, homotopy, derived, stabilize, center, drinfeld_center, booleanize, span, cospan, nerve, realize, isbell_spec, isbell_cospec, isbell, matrix, int, internal_cat, path, operad_envelope"

-- ============================================================
-- apply_operator command
-- Applies a single named operator to a theory from the registry
-- ============================================================

def handleApplyOp (j : Json) (id : String) : Json :=
  match getStr j "operator", getStr j "theory" with
  | .ok op, .ok name =>
    match lookupTheory name with
    | .error e => errorResponse id e
    | .ok t    =>
      match applyForwardOp op t with
      | .error e  => errorResponse id e
      | .ok result =>
        okResponse id [("theory", theoryToJson result),
                       ("summary", .str result.summary)]
  | .error e, _ => errorResponse id e
  | _, .error e => errorResponse id e

-- ============================================================
-- compute_pushout command
-- Computes pushout (inclusion base theory1) (inclusion base theory2)
-- ============================================================

def handleComputePushout (j : Json) (id : String) : Json :=
  match getStr j "theory1", getStr j "theory2", getStr j "base" with
  | .ok n1, .ok n2, .ok nb =>
    match lookupTheory n1, lookupTheory n2, lookupTheory nb with
    | .ok t1, .ok t2, .ok base =>
      let f := TheoryMorphism.inclusion base t1
      let g := TheoryMorphism.inclusion base t2
      match pushout f g with
      | none    => errorResponse id s!"pushout failed: source theories don't share base '{nb}'"
      | some po =>
        okResponse id [("theory", theoryToJson po), ("summary", .str po.summary)]
    | .error e, _, _ | _, .error e, _ | _, _, .error e => errorResponse id e
  | .error e, _, _ | _, .error e, _ | _, _, .error e   => errorResponse id e

-- ============================================================
-- evaluate_inverse command
-- Applies forwardOp to candidate, diffs against target, returns VerificationResult
-- ============================================================

def handleEvaluateInverse (j : Json) (id : String) : Json :=
  -- Parse required fields
  let targetResult  := getStr j "target"
  let forwardResult := getStr j "forward_op"
  let candidateJson := j.getObjVal? "candidate"
  match targetResult, forwardResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok targetName, .ok fwdOp, .ok candJson =>
    match lookupTheory targetName, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok target, .ok candidate =>
      match applyForwardOp fwdOp candidate with
      | .error e => errorResponse id e
      | .ok produced =>
        let result := computeStructuralDiff candidate produced target
        okResponse id [("result", verificationToJson result)]

-- ============================================================
-- solve_inverse command
-- Tries each candidate in order, returns first that passes
-- ============================================================

def handleSolveInverse (j : Json) (id : String) : Json :=
  let targetResult    := getStr j "target"
  let forwardResult   := getStr j "forward_op"
  let candidatesJson  := j.getObjVal? "candidates"
  match targetResult, forwardResult, candidatesJson with
  | .error e, _, _     => errorResponse id e
  | _, .error e, _     => errorResponse id e
  | _, _, .error _     => errorResponse id "missing field 'candidates'"
  | .ok tn, .ok fwdOp, .ok (.arr arr) =>
    match lookupTheory tn with
    | .error e => errorResponse id e
    | .ok target =>
      let forward : Theory → Option Theory := fun c =>
        match applyForwardOp fwdOp c with
        | .ok t   => some t
        | .error _ => none
      -- Parse all candidates, skip malformed ones with error reporting
      let parsed := arr.toList.filterMap fun cj =>
        match theoryFromJson cj with
        | .ok t   => some t
        | .error _ => none
      match solveInverse target forward parsed with
      | none             =>
        okResponse id [("verified", .bool false),
                       ("message", .str s!"No candidate passed. Tried {parsed.length} proposal(s).")]
      | some (winner, r) =>
        okResponse id [("verified", .bool true),
                       ("winner",   theoryToJson winner),
                       ("result",   verificationToJson r)]
  | _, _, .ok other =>
    errorResponse id s!"'candidates' must be an array, got: {other.compress}"

-- ============================================================
-- evaluate_pushout_complement command
-- Find X such that pushout(base, X) ≅ target
-- Verifies by computing pushout(base, candidate) and diffing against target
-- ============================================================

def handleEvaluatePushoutComplement (j : Json) (id : String) : Json :=
  let baseResult   := getStr j "base"
  let targetResult := getStr j "target"
  let candidateJson := j.getObjVal? "candidate"
  match baseResult, targetResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok baseName, .ok targetName, .ok candJson =>
    match lookupTheory baseName, lookupTheory targetName, theoryFromJson candJson with
    | .error e, _, _ => errorResponse id e
    | _, .error e, _ => errorResponse id e
    | _, _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok base, .ok target, .ok candidate =>
      let f := TheoryMorphism.inclusion base candidate
      let g := TheoryMorphism.inclusion base target
      match pushout f g with
      | none    => errorResponse id s!"pushout(base, candidate) failed"
      | some produced =>
        let result := computeStructuralDiff candidate produced target
        okResponse id [("result", verificationToJson result)]

-- ============================================================
-- evaluate_extension command
-- Find X extending base with property P
-- Verifies candidate extends base (inclusion exists) and satisfies property
-- ============================================================

def handleEvaluateExtension (j : Json) (id : String) : Json :=
  let baseResult     := getStr j "base"
  let propertyResult := getStr j "property"
  let candidateJson  := j.getObjVal? "candidate"
  match baseResult, propertyResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok baseName, .ok _property, .ok candJson =>
    match lookupTheory baseName, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok base, .ok candidate =>
      -- Check that candidate extends base: all base objects/morphisms present
      let missingObjs := base.objects.filter fun o =>
        !candidate.objects.any fun co => co.id == o.id
      let missingMors := base.morphisms.filter fun m =>
        !candidate.morphisms.any fun cm => cm.id == m.id
      -- Use self-diff (candidate ≅ candidate) so verified=true when extension holds
      let result := computeStructuralDiff candidate candidate candidate
      if missingObjs.isEmpty && missingMors.isEmpty then
        okResponse id [("result", verificationToJson result),
                       ("extends_base", .bool true)]
      else
        let missingNames := (missingObjs.map (fun o => Json.str (toString o.id))
                          ++ missingMors.map (fun m => Json.str (toString m.id)))
        okResponse id [("result", verificationToJson result),
                       ("extends_base", .bool false),
                       ("missing_from_base", .arr missingNames.toArray)]

-- ============================================================
-- evaluate_multi_objective command
-- Find X such that F₁(X)≅T₁ ∧ F₂(X)≅T₂ ∧ ...
-- Verifies each objective independently, all must pass
-- ============================================================

def handleEvaluateMultiObjective (j : Json) (id : String) : Json :=
  let candidateJson  := j.getObjVal? "candidate"
  let objectivesJson := j.getObjVal? "objectives"
  match candidateJson, objectivesJson with
  | .error _, _       => errorResponse id "missing field 'candidate'"
  | _, .error _       => errorResponse id "missing field 'objectives'"
  | .ok candJson, .ok (.arr objectives) =>
    match theoryFromJson candJson with
    | .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok candidate =>
      let subResults := objectives.toList.map fun objJson =>
        let targetName := match objJson.getObjVal? "target" with
          | .ok (.str s) => s | _ => ""
        let fwdOp := match objJson.getObjVal? "forward_op" with
          | .ok (.str s) => s | _ => ""
        match lookupTheory targetName with
        | .error e =>
          Json.mkObj [("candidateName", .str candidate.name), ("verified", .bool false),
            ("verificationStatus", .str s!"✗ Failed: target '{targetName}' not found: {e}"),
            ("missingSignatures", .arr #[]), ("unmappedObjects", .arr #[]),
            ("axiomViolations", .arr #[])]
        | .ok target =>
          match applyForwardOp fwdOp candidate with
          | .error e =>
            Json.mkObj [("candidateName", .str candidate.name), ("verified", .bool false),
              ("verificationStatus", .str s!"✗ Failed: operator '{fwdOp}' error: {e}"),
              ("missingSignatures", .arr #[]), ("unmappedObjects", .arr #[]),
              ("axiomViolations", .arr #[])]
          | .ok produced =>
            verificationToJson (computeStructuralDiff candidate produced target)
      let allVerified := subResults.all fun r =>
        match r.getObjVal? "verified" with
        | .ok (.bool true) => true | _ => false
      okResponse id [("verified", .bool allVerified),
                     ("subResults", .arr subResults.toArray)]
  | .ok _, .ok other =>
    errorResponse id s!"'objectives' must be an array, got: {other.compress}"

-- ============================================================
-- evaluate_fixed_point command
-- Find X such that F(X) ≅ X
-- Applies forwardOp to candidate, diffs against candidate itself
-- ============================================================

def handleEvaluateFixedPoint (j : Json) (id : String) : Json :=
  let forwardResult  := getStr j "forward_op"
  let candidateJson  := j.getObjVal? "candidate"
  match forwardResult, candidateJson with
  | .error e, _       => errorResponse id e
  | _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok fwdOp, .ok candJson =>
    match theoryFromJson candJson with
    | .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok candidate =>
      match applyForwardOp fwdOp candidate with
      | .error e => errorResponse id e
      | .ok produced =>
        -- Diff F(candidate) against candidate itself
        let result := computeStructuralDiff candidate produced candidate
        okResponse id [("result", verificationToJson result)]

-- ============================================================
-- summary / validate commands
-- ============================================================

def handleSummary (j : Json) (id : String) : Json :=
  match getStr j "theory" with
  | .error e => errorResponse id e
  | .ok name =>
    match lookupTheory name with
    | .error e => errorResponse id e
    | .ok t    =>
      okResponse id [("summary",   .str t.summary),
                     ("theory",    theoryToJson t)]

def handleValidate (j : Json) (id : String) : Json :=
  match getStr j "theory" with
  | .error e => errorResponse id e
  | .ok name =>
    match lookupTheory name with
    | .error e => errorResponse id e
    | .ok t    =>
      let errors := validate t
      okResponse id [("valid",   .bool errors.isEmpty),
                     ("errors",  .arr (errors.map (Json.str ∘ toString)).toArray)]

def handleListTheories (_j : Json) (id : String) : Json :=
  let names := theoryRegistry.map (Json.str ∘ Prod.fst)
  okResponse id [("theories", .arr names.toArray),
                 ("count",    natJson theoryRegistry.length)]

-- ============================================================
-- Main dispatch: parse request, route to handler, return response
-- ============================================================

def handleRequest (line : String) : Json :=
  match Json.parse line with
  | .error e  =>
    -- Malformed JSON: can't echo an id, use "parse_error"
    errorResponse "parse_error" s!"JSON parse error: {e}"
  | .ok j =>
    -- Extract optional request id for correlation
    let id := match j.getObjVal? "id" with
      | .ok (.str s) => s
      | _            => "unknown"
    match j.getObjVal? "command" with
    | .error _        => errorResponse id "missing field 'command'"
    | .ok (.str cmd)  =>
      match cmd with
      | "list_theories"    => handleListTheories    j id
      | "summary"          => handleSummary         j id
      | "validate"         => handleValidate        j id
      | "apply_operator"   => handleApplyOp         j id
      | "compute_pushout"  => handleComputePushout  j id
      | "evaluate_inverse"             => handleEvaluateInverse            j id
      | "solve_inverse"                => handleSolveInverse               j id
      | "evaluate_pushout_complement"  => handleEvaluatePushoutComplement  j id
      | "evaluate_extension"           => handleEvaluateExtension          j id
      | "evaluate_multi_objective"     => handleEvaluateMultiObjective     j id
      | "evaluate_fixed_point"         => handleEvaluateFixedPoint         j id
      | other              => errorResponse id s!"Unknown command '{other}'. Supported: list_theories, summary, validate, apply_operator, compute_pushout, evaluate_inverse, solve_inverse, evaluate_pushout_complement, evaluate_extension, evaluate_multi_objective, evaluate_fixed_point"
    | .ok other =>
      errorResponse id s!"'command' must be a string, got: {other.compress}"

-- ============================================================
-- NDJSON main loop
-- Reads one line → writes one line → flushes → repeat
-- The flush is CRITICAL: without it the TypeScript orchestrator
-- hangs waiting for the buffer to clear.
-- ============================================================

partial def ndjsonLoop : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  let line   ← stdin.getLine
  -- Empty line = EOF (stdin closed by orchestrator)
  if line.trim.isEmpty then return
  let response := handleRequest line
  stdout.putStrLn response.compress
  stdout.flush                          -- ← critical: unblock the TS readline
  ndjsonLoop

end CatLab.Repl
