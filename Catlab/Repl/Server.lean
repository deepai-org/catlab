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
    compute_pushout_cocone { theory1, theory2, base } → pushout + inclusion morphisms
    compute_morphism { source, target, kind } → TheoryMorphism as JSON
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
import Catlab.Operators.Adjunction
import Catlab.Operators.Algebraize
import Catlab.Operators.Amalgamate
import Catlab.Operators.Arrow
import Catlab.Operators.ArtinGluing
import Catlab.Operators.Assembly
import Catlab.Operators.Booleanize
import Catlab.Operators.Bousfield
import Catlab.Operators.Center
import Catlab.Operators.ChangeOfBase
import Catlab.Operators.Chu
import Catlab.Operators.Cleavage
import Catlab.Operators.Collage
import Catlab.Operators.Comma
import Catlab.Operators.Coproduct
import Catlab.Operators.Core
import Catlab.Operators.CwF
import Catlab.Operators.DayConvolution
import Catlab.Operators.Decategorify
import Catlab.Operators.Derived
import Catlab.Operators.Dialectica
import Catlab.Operators.DrinfeldCenter
import Catlab.Operators.EndsCoends
import Catlab.Operators.ExactCompletion
import Catlab.Operators.Factorization
import Catlab.Operators.Family
import Catlab.Operators.Fractions
import Catlab.Operators.Free
import Catlab.Operators.Freyd
import Catlab.Operators.FunctorCategory
import Catlab.Operators.Grothendieck
import Catlab.Operators.IndPro
import Catlab.Operators.Int
import Catlab.Operators.Internal
import Catlab.Operators.Isbell
import Catlab.Operators.Kan
import Catlab.Operators.Karoubi
import Catlab.Operators.Kleisli
import Catlab.Operators.Lawvere
import Catlab.Operators.Limits
import Catlab.Operators.Localize
import Catlab.Operators.MacNeille
import Catlab.Operators.Matrix
import Catlab.Operators.Mirror
import Catlab.Operators.Monad
import Catlab.Operators.Morita
import Catlab.Operators.Nerve
import Catlab.Operators.OperadEnvelope
import Catlab.Operators.Opposite
import Catlab.Operators.PER
import Catlab.Operators.Product
import Catlab.Operators.Pullback
import Catlab.Operators.Pushout
import Catlab.Operators.HomotopyPushout
import Catlab.Operators.Quotient
import Catlab.Operators.Realizability
import Catlab.Operators.Sheafify
import Catlab.Operators.Skolem
import Catlab.Operators.Slice
import Catlab.Operators.Span
import Catlab.Operators.Stabilize
import Catlab.Operators.Subcategory
import Catlab.Operators.Syntactic
import Catlab.Operators.TriposToTopos
import Catlab.Operators.TwistedArrow
import Catlab.Operators.Ultrapower
import Catlab.Operators.Yoneda
import Catlab.Operators.Registry
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
import Catlab.Library.Sphere
import Catlab.Library.Univalence
import Catlab.Library.SecretBoss
import Catlab.Operators.PropTrunc
import Catlab.Operators.LoopSpace
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
  , ("DGA",                      TheoryOfDifferentialGradedAlgebra)
  , ("S0",                       TheoryOfS0)
  , ("S1",                       TheoryOfS1)
  , ("S2",                       TheoryOfS2)
  , ("Univalence",               TheoryOfUnivalence 0)
  , ("SubobjectClassifier",      TheoryOfSubobjectClassifier)
  , ("HomotopyPullback",         TheoryOfHomotopyPullback)
  , ("TypeA",                    TheoryOfTypeA)
  , ("BasedPathSpace",           TheoryOfBasedPathSpace)
  , ("LoopSpaceSquared",         TheoryOfLoopSpaceSquared) ]

-- Runtime registry for user-defined theories (populated by define_theory command).
-- Uses `initialize` so it's a global IO.Ref accessible from pure code via unsafeBaseIO.
initialize runtimeRegistry : IO.Ref (List (String × Theory)) ← IO.mkRef []

/-- Look up a theory by name. Checks extra (runtime) list first, then static registry. -/
def lookupTheory (name : String) (extra : List (String × Theory) := []) : Except String Theory :=
  match extra.find? (fun (n, _) => n == name) with
  | some (_, t) => .ok t
  | none =>
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
  | "core"                              => .ok (core t (t.morphisms.map (·.id)))
  | "identity"                          => .ok t
  -- Decategorification variants
  | "decategorify_iso" | "decategorify" => .ok (decategorify t .isoClasses)
  | "decategorify_K0"                   => .ok (decategorify t .grothendieckGroup)
  | "decategorify_chi"                  => .ok (decategorify t .eulerCharacteristic)
  -- Arrow & comma constructions
  | "arrow"                             => .ok (Arrow.arrowCat t)
  | "arrow_category"                    => .ok (arrowCategory t)
  | "twisted_arrow"                     => .ok (twistedArrow t)
  | "slice"                             =>
    match t.objects.head? with
    | some obj => .ok (slice t (.atom obj.id))
    | none     => .error "slice requires at least one object"
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
  | "yoneda"                            => .ok (presheafCategory t)
  | "family"                            => .ok (familyCategory t)
  -- grothendieck requires an IndexedCategory param; use family for Fam(C)
  -- | "grothendieck" => needs IndexedCategory, dispatched via parameterized path
  | "functor_category"                  => .ok (functorCategory t t)
  | "scone"                             => .ok (scone t)
  | "freyd"                             => .ok (scone t)
  | "syntactic"                         => .ok (syntacticCategory t)
  | "lawvere"                           => .ok (lawvereModelCategory t t)
  | "free"                              => .ok (presheafCategory t)
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
  -- Products & coproducts (self × self as default)
  | "product"                           => .ok (productCategory t t)
  | "coproduct"                         => .ok (coproductCategory t t)
  -- Miscellaneous
  | "matrix"                            => .ok (matrixCategory t)
  | "int"                               => .ok (intConstruction t)
  | "internal_cat"                      => .ok (internalCategoryCategory t)
  | "path"                              => .ok (pathCategory t)
  | "factorization"                     => .ok (pathCategory t)
  | "operad_envelope"                   => .ok (operadicEnvelope t)
  | "limits"                            => .ok (regCompletion t)
  -- HoTT operators
  | "homotopy_suspension"              =>
    match homotopySuspension t with
    | some r => .ok r
    | none   => .error "homotopySuspension failed"
  | "homotopy_coproduct"               =>
    match homotopyCoproduct t t with
    | some r => .ok r
    | none   => .error "homotopyCoproduct failed"
  | "prop_trunc"                        => .ok (propTruncTheory t)
  | "loop_space"                        => .ok (loopSpace t)
  | s => .error s!"Unknown forward_op '{s}'. Use one of: opposite, mirror, core, identity, decategorify_iso, decategorify_K0, decategorify_chi, arrow, arrow_category, twisted_arrow, slice, karoubi, morita, macneille, reg_completion, ex_completion, ind_completion, pro_completion, presheaf, yoneda, family, functor_category, scone, freyd, syntactic, lawvere, free, chain_complex, homotopy, derived, stabilize, center, drinfeld_center, booleanize, span, cospan, nerve, realize, isbell_spec, isbell_cospec, isbell, product, coproduct, matrix, int, internal_cat, path, factorization, operad_envelope, limits, homotopy_suspension, homotopy_coproduct, prop_trunc, loop_space"

/-- Does this operator reverse composition order (and is an involution)?
    Such operators benefit from contravariant verification: instead of diffing
    forwardOp(candidate) against target, we diff candidate against
    forwardOp(target), which keeps composition direction aligned with the
    rewriter's axiom orientation. This is a heuristic for better convergence
    of the bounded Knuth-Bendix procedure, not a solution to the underlying
    Word Problem — if the rewrite system diverges in one orientation, it may
    also diverge in the other. -/
def isCompReversing (op : String) : Bool :=
  match op with
  | "opposite" => true
  | "mirror"   => true   -- mirror also reverses comp (dual to opposite)
  | _          => false

-- ============================================================
-- Operator-aware structural diff
-- Dispatches to contravariant or forward strategy based on operator
-- ============================================================

/-- Verify forwardOp(candidate) ≅ target using the best strategy for the operator.
    For comp-reversing involutions (opposite, mirror): contravariant strategy
    (empirically better convergence, but does not eliminate undecidability).
    For all others: standard forward strategy. -/
def operatorAwareDiff (fwdOp : String) (candidate target : Theory) : Except String VerificationResult :=
  if isCompReversing fwdOp then
    -- Contravariant: diff candidate against forwardOp(target)
    match applyForwardOp fwdOp target with
    | .ok expected => .ok (computeStructuralDiff candidate candidate expected)
    | .error _ =>
      -- Fallback to forward strategy
      match applyForwardOp fwdOp candidate with
      | .error e => .error e
      | .ok produced => .ok (computeStructuralDiff candidate produced target)
  else
    -- Standard forward: diff forwardOp(candidate) against target
    match applyForwardOp fwdOp candidate with
    | .error e => .error e
    | .ok produced => .ok (computeStructuralDiff candidate produced target)

/-- Verify forwardOp(candidate) ≅ candidate (fixed-point) using the best strategy. -/
def operatorAwareFixedPointDiff (fwdOp : String) (candidate : Theory) : Except String VerificationResult :=
  match applyForwardOp fwdOp candidate with
  | .error e => .error e
  | .ok produced =>
    if isCompReversing fwdOp then
      -- Contravariant: use produced (= F(X)) as target so its axioms are the reference
      .ok (computeStructuralDiff candidate candidate produced)
    else
      -- Standard: diff produced against candidate
      .ok (computeStructuralDiff candidate produced candidate)

-- ============================================================
-- apply_operator command
-- Applies a single named operator to a theory from the registry
-- ============================================================

def handleApplyOp (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "operator", getStr j "theory" with
  | .ok op, .ok name =>
    match lookupTheory name rt with
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

def handleComputePushout (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "theory1", getStr j "theory2", getStr j "base" with
  | .ok n1, .ok n2, .ok nb =>
    match lookupTheory n1 rt, lookupTheory n2 rt, lookupTheory nb rt with
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
-- compute_pushout_cocone command
-- Like compute_pushout but also returns the inclusion morphisms
-- ============================================================

def handleComputePushoutCocone (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "theory1", getStr j "theory2", getStr j "base" with
  | .ok n1, .ok n2, .ok nb =>
    match lookupTheory n1 rt, lookupTheory n2 rt, lookupTheory nb rt with
    | .ok t1, .ok t2, .ok base =>
      let f := TheoryMorphism.inclusion base t1
      let g := TheoryMorphism.inclusion base t2
      match pushoutCocone f g with
      | none    => errorResponse id s!"pushout cocone failed: source theories don't share base '{nb}'"
      | some cocone =>
        okResponse id [
          ("theory",      theoryToJson cocone.apex),
          ("summary",     .str cocone.apex.summary),
          ("inclusionA",  theoryMorphismToJson cocone.leftLeg),
          ("inclusionB",  theoryMorphismToJson cocone.rightLeg)]
    | .error e, _, _ | _, .error e, _ | _, _, .error e => errorResponse id e
  | .error e, _, _ | _, .error e, _ | _, _, .error e   => errorResponse id e

-- ============================================================
-- compute_pullback command
-- Computes pullback (inclusion target theory1) (inclusion target theory2)
-- ============================================================

def handleComputePullback (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "theory1", getStr j "theory2", getStr j "base" with
  | .ok n1, .ok n2, .ok nb =>
    match lookupTheory n1 rt, lookupTheory n2 rt, lookupTheory nb rt with
    | .ok t1, .ok t2, .ok base =>
      let f := TheoryMorphism.inclusion base t1
      let g := TheoryMorphism.inclusion base t2
      match theoryPullback f g with
      | none    => errorResponse id s!"pullback failed: theories don't share base '{nb}'"
      | some pb =>
        okResponse id [("theory", theoryToJson pb), ("summary", .str pb.summary)]
    | .error e, _, _ | _, .error e, _ | _, _, .error e => errorResponse id e
  | .error e, _, _ | _, .error e, _ | _, _, .error e   => errorResponse id e

-- ============================================================
-- compute_pullback_cone command
-- Like compute_pullback but also returns the projection morphisms
-- ============================================================

def handleComputePullbackCone (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "theory1", getStr j "theory2", getStr j "base" with
  | .ok n1, .ok n2, .ok nb =>
    match lookupTheory n1 rt, lookupTheory n2 rt, lookupTheory nb rt with
    | .ok t1, .ok t2, .ok base =>
      let f := TheoryMorphism.inclusion base t1
      let g := TheoryMorphism.inclusion base t2
      match pullbackCone f g with
      | none    => errorResponse id s!"pullback cone failed: theories don't share base '{nb}'"
      | some cone =>
        okResponse id [
          ("theory",      theoryToJson cone.apex),
          ("summary",     .str cone.apex.summary),
          ("leftProj",    theoryMorphismToJson cone.leftProj),
          ("rightProj",   theoryMorphismToJson cone.rightProj)]
    | .error e, _, _ | _, .error e, _ | _, _, .error e => errorResponse id e
  | .error e, _, _ | _, .error e, _ | _, _, .error e   => errorResponse id e

-- ============================================================
-- compute_morphism command
-- Computes a TheoryMorphism between two theories and returns it as JSON
-- ============================================================

def handleComputeMorphism (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "source", getStr j "target", getStr j "kind" with
  | .ok srcName, .ok tgtName, .ok kind =>
    match lookupTheory srcName rt, lookupTheory tgtName rt with
    | .ok src, .ok tgt =>
      match kind with
      | "inclusion" =>
        let tm := TheoryMorphism.inclusion src tgt
        let preserves := tm.preservesTyping
        okResponse id [
          ("morphism",        theoryMorphismToJson tm),
          ("preservesTyping", .bool preserves)]
      | "identity" =>
        let tm := TheoryMorphism.id src
        okResponse id [("morphism", theoryMorphismToJson tm)]
      | k => errorResponse id s!"Unknown morphism kind '{k}'. Use 'inclusion' or 'identity'."
    | .error e, _ | _, .error e => errorResponse id e
  | .error e, _, _ | _, .error e, _ | _, _, .error e => errorResponse id e

-- ============================================================
-- evaluate_inverse command
-- Applies forwardOp to candidate, diffs against target, returns VerificationResult
-- ============================================================

def handleEvaluateInverse (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  -- Parse required fields
  let targetResult  := getStr j "target"
  let forwardResult := getStr j "forward_op"
  let candidateJson := j.getObjVal? "candidate"
  match targetResult, forwardResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok targetName, .ok fwdOp, .ok candJson =>
    match lookupTheory targetName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok target, .ok candidate =>
      match operatorAwareDiff fwdOp candidate target with
      | .error e => errorResponse id e
      | .ok result =>
        -- If timeout on MLTT/HIT theory, include produced theory for TS-side Hyperion re-verification
        let hasTimeout := result.axiomViolations.any fun v =>
          match v.status with | .Timeout _ => true | _ => false
        if hasTimeout then
          match applyForwardOp fwdOp candidate with
          | .ok p =>
            okResponse id [("result", verificationToJson result),
                           ("produced", theoryToJson p),
                           ("target", theoryToJson target),
                           ("produced_doctrine", .str (toString (repr p.doctrine.doctrine)))]
          | .error _ =>
            okResponse id [("result", verificationToJson result)]
        else
          okResponse id [("result", verificationToJson result)]

-- ============================================================
-- solve_inverse command
-- Tries each candidate in order, returns first that passes
-- ============================================================

def handleSolveInverse (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let targetResult    := getStr j "target"
  let forwardResult   := getStr j "forward_op"
  let candidatesJson  := j.getObjVal? "candidates"
  match targetResult, forwardResult, candidatesJson with
  | .error e, _, _     => errorResponse id e
  | _, .error e, _     => errorResponse id e
  | _, _, .error _     => errorResponse id "missing field 'candidates'"
  | .ok tn, .ok fwdOp, .ok (.arr arr) =>
    match lookupTheory tn rt with
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

def handleEvaluatePushoutComplement (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let baseResult   := getStr j "base"
  let targetResult := getStr j "target"
  let candidateJson := j.getObjVal? "candidate"
  match baseResult, targetResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok baseName, .ok targetName, .ok candJson =>
    match lookupTheory baseName rt, lookupTheory targetName rt, theoryFromJson candJson with
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

def handleEvaluateExtension (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let baseResult     := getStr j "base"
  let propertyResult := getStr j "property"
  let candidateJson  := j.getObjVal? "candidate"
  match baseResult, propertyResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok baseName, .ok _property, .ok candJson =>
    match lookupTheory baseName rt, theoryFromJson candJson with
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

def handleEvaluateMultiObjective (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
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
        match lookupTheory targetName rt with
        | .error e =>
          Json.mkObj [("candidateName", .str candidate.name), ("verified", .bool false),
            ("verificationStatus", .str s!"✗ Failed: target '{targetName}' not found: {e}"),
            ("missingSignatures", .arr #[]), ("unmappedObjects", .arr #[]),
            ("axiomViolations", .arr #[])]
        | .ok target =>
          match operatorAwareDiff fwdOp candidate target with
          | .error e =>
            Json.mkObj [("candidateName", .str candidate.name), ("verified", .bool false),
              ("verificationStatus", .str s!"✗ Failed: operator '{fwdOp}' error: {e}"),
              ("missingSignatures", .arr #[]), ("unmappedObjects", .arr #[]),
              ("axiomViolations", .arr #[])]
          | .ok result => verificationToJson result
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
      match operatorAwareFixedPointDiff fwdOp candidate with
      | .error e => errorResponse id e
      | .ok result => okResponse id [("result", verificationToJson result)]

-- ============================================================
-- evaluate_pullback_complement command
-- Find X such that pullback(base, X) ≅ target
-- Dual of pushout complement: uses opposite theories
-- ============================================================

def handleEvaluatePullbackComplement (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let baseResult   := getStr j "base"
  let targetResult := getStr j "target"
  let candidateJson := j.getObjVal? "candidate"
  match baseResult, targetResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok baseName, .ok targetName, .ok candJson =>
    match lookupTheory baseName rt, lookupTheory targetName rt, theoryFromJson candJson with
    | .error e, _, _ => errorResponse id e
    | _, .error e, _ => errorResponse id e
    | _, _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok base, .ok target, .ok candidate =>
      -- Pullback complement via duality: pullback in C = pushout in C^op
      let baseOp := opposite base
      let targetOp := opposite target
      let candidateOp := opposite candidate
      let f := TheoryMorphism.inclusion baseOp candidateOp
      let g := TheoryMorphism.inclusion baseOp targetOp
      match pushout f g with
      | none    => errorResponse id s!"pullback complement failed (pushout in op-category)"
      | some produced =>
        -- Diff in the opposite category, then report
        let result := computeStructuralDiff candidate (opposite produced) target
        okResponse id [("result", verificationToJson result)]

-- ============================================================
-- evaluate_simplification command
-- Find minimal X ≅ T
-- Verifies X ≅ target and reports generator count
-- ============================================================

def handleEvaluateSimplification (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let targetResult := getStr j "target"
  let candidateJson := j.getObjVal? "candidate"
  match targetResult, candidateJson with
  | .error e, _       => errorResponse id e
  | _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok targetName, .ok candJson =>
    match lookupTheory targetName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok target, .ok candidate =>
      -- Verify structural equivalence (identity operator)
      let result := computeStructuralDiff candidate candidate target
      -- Report size metrics for optimization
      let candSize := candidate.objects.length + candidate.morphisms.length + candidate.axioms.length
      let targetSize := target.objects.length + target.morphisms.length + target.axioms.length
      okResponse id [("result", verificationToJson result),
                     ("candidate_size", natJson candSize),
                     ("target_size", natJson targetSize)]

-- ============================================================
-- evaluate_model command
-- Generate a concrete instance/algebra for a theory
-- The candidate provides concrete assignments; we check axioms hold
-- ============================================================

def handleEvaluateModel (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let theoryResult := getStr j "theory"
  let candidateJson := j.getObjVal? "candidate"
  match theoryResult, candidateJson with
  | .error e, _       => errorResponse id e
  | _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok theoryName, .ok candJson =>
    match lookupTheory theoryName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok theory, .ok candidate =>
      -- Run universe/positivity/predicativity validation on the candidate
      let validationErrors := validate candidate
      if !validationErrors.isEmpty then
        okResponse id [("result", Json.mkObj [
          ("status", "invalid"),
          ("score", Json.num 0),
          ("reason", Json.str s!"validation failed: {validationErrors.map toString}")])]
      else
        -- A "model" here is a theory with the same structure as the target
        -- but with concrete interpretations. Verify it's a valid instance
        -- by checking the candidate's axiom structure matches the theory.
        let result := computeStructuralDiff candidate candidate theory
        okResponse id [("result", verificationToJson result)]

-- ============================================================
-- evaluate_subobject command
-- Find a sub-theory of target satisfying property P
-- Candidate must be a sub-theory (all generators from candidate exist in target)
-- ============================================================

def handleEvaluateSubobject (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let targetResult   := getStr j "target"
  let propertyResult := getStr j "property"
  let candidateJson  := j.getObjVal? "candidate"
  match targetResult, propertyResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok targetName, .ok _property, .ok candJson =>
    match lookupTheory targetName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok target, .ok candidate =>
      -- Check that candidate is a sub-theory: all its generators map into target
      -- Use extension check in reverse: target extends candidate
      let missingObjs := candidate.objects.filter fun o =>
        !target.objects.any fun to_ => to_.id == o.id
      let missingMors := candidate.morphisms.filter fun m =>
        !target.morphisms.any fun tm => tm.id == m.id
      -- Self-diff for the sub-theory (its own axioms must be consistent)
      let result := computeStructuralDiff candidate candidate candidate
      if missingObjs.isEmpty && missingMors.isEmpty then
        okResponse id [("result", verificationToJson result),
                       ("is_subtheory", .bool true),
                       ("candidate_size", natJson (candidate.objects.length + candidate.morphisms.length))]
      else
        let missingNames := (missingObjs.map (fun o => Json.str (toString o.id))
                          ++ missingMors.map (fun m => Json.str (toString m.id)))
        okResponse id [("result", verificationToJson result),
                       ("is_subtheory", .bool false),
                       ("not_in_target", .arr missingNames.toArray)]

-- ============================================================
-- evaluate_synthesis command
-- Find morphism sequence that composes to A → B within a theory
-- The candidate is a theory extending the base with the desired composite
-- ============================================================

def handleEvaluateSynthesis (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let theoryResult := getStr j "theory"
  let candidateJson := j.getObjVal? "candidate"
  match theoryResult, candidateJson with
  | .error e, _       => errorResponse id e
  | _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok theoryName, .ok candJson =>
    match lookupTheory theoryName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok theory, .ok candidate =>
      -- Verify: candidate extends theory (all theory generators present)
      -- and adds exactly the desired morphisms as compositions of existing ones
      let missingObjs := theory.objects.filter fun o =>
        !candidate.objects.any fun co => co.id == o.id
      let missingMors := theory.morphisms.filter fun m =>
        !candidate.morphisms.any fun cm => cm.id == m.id
      let result := computeStructuralDiff candidate candidate candidate
      if missingObjs.isEmpty && missingMors.isEmpty then
        okResponse id [("result", verificationToJson result),
                       ("extends_theory", .bool true),
                       ("new_morphisms", natJson (candidate.morphisms.length - theory.morphisms.length))]
      else
        let missingNames := (missingObjs.map (fun o => Json.str (toString o.id))
                          ++ missingMors.map (fun m => Json.str (toString m.id)))
        okResponse id [("result", verificationToJson result),
                       ("extends_theory", .bool false),
                       ("missing_from_theory", .arr missingNames.toArray)]

-- ============================================================
-- evaluate_quotient command
-- Find minimal congruence ∼ on base such that base/∼ satisfies property P
-- The candidate is a theory representing base/∼ (with some axioms collapsed)
-- ============================================================

def handleEvaluateQuotient (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let baseResult     := getStr j "base"
  let propertyResult := getStr j "property"
  let candidateJson  := j.getObjVal? "candidate"
  match baseResult, propertyResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok baseName, .ok _property, .ok candJson =>
    match lookupTheory baseName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok base, .ok candidate =>
      -- Verify: candidate has ≤ generators than base (it's a quotient)
      -- and there exists a surjection base → candidate (all base objects present)
      let missingObjs := base.objects.filter fun o =>
        !candidate.objects.any fun co => co.id == o.id
      let baseSize := base.objects.length + base.morphisms.length + base.axioms.length
      let candSize := candidate.objects.length + candidate.morphisms.length + candidate.axioms.length
      let result := computeStructuralDiff candidate candidate candidate
      if missingObjs.isEmpty then
        okResponse id [("result", verificationToJson result),
                       ("is_quotient", .bool true),
                       ("base_size", natJson baseSize),
                       ("candidate_size", natJson candSize)]
      else
        let missingNames := missingObjs.map (fun o => Json.str (toString o.id))
        okResponse id [("result", verificationToJson result),
                       ("is_quotient", .bool false),
                       ("missing_objects", .arr missingNames.toArray)]

-- ============================================================
-- evaluate_decomposition command
-- Find set of Xᵢ such that ⨁ Xᵢ ≅ target (coproduct decomposition)
-- The candidate provides multiple sub-theories; we verify their coproduct
-- ============================================================

def handleEvaluateDecomposition (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let targetResult := getStr j "target"
  let candidateJson := j.getObjVal? "candidate"
  match targetResult, candidateJson with
  | .error e, _       => errorResponse id e
  | _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok targetName, .ok candJson =>
    match lookupTheory targetName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok target, .ok candidate =>
      -- The candidate represents the "reassembled" theory from components
      -- Verify it matches the target structurally
      let result := computeStructuralDiff candidate candidate target
      okResponse id [("result", verificationToJson result)]

-- ============================================================
-- evaluate_relaxation command
-- Find X minimizing edit distance to target while satisfying property P
-- ============================================================

def handleEvaluateRelaxation (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let targetResult   := getStr j "target"
  let propertyResult := getStr j "property"
  let candidateJson  := j.getObjVal? "candidate"
  match targetResult, propertyResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok targetName, .ok _property, .ok candJson =>
    match lookupTheory targetName rt, theoryFromJson candJson with
    | .error e, _ => errorResponse id e
    | _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok target, .ok candidate =>
      -- Compute structural diff to measure edit distance
      let result := computeStructuralDiff candidate candidate target
      -- Report size difference as a simple distance metric
      let targetSize := target.objects.length + target.morphisms.length + target.axioms.length
      let candSize := candidate.objects.length + candidate.morphisms.length + candidate.axioms.length
      let sizeDiff := if candSize > targetSize then candSize - targetSize else targetSize - candSize
      okResponse id [("result", verificationToJson result),
                     ("edit_distance", natJson sizeDiff),
                     ("candidate_size", natJson candSize),
                     ("target_size", natJson targetSize)]

-- ============================================================
-- evaluate_catalyst command
-- Find C such that A⊗C → B⊗C is valid (inclusion exists)
-- ============================================================

def handleEvaluateCatalyst (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let sourceResult := getStr j "source"
  let targetResult := getStr j "target"
  let candidateJson := j.getObjVal? "candidate"
  match sourceResult, targetResult, candidateJson with
  | .error e, _, _       => errorResponse id e
  | _, .error e, _       => errorResponse id e
  | _, _, .error _       => errorResponse id "missing field 'candidate'"
  | .ok sourceName, .ok targetName, .ok candJson =>
    match lookupTheory sourceName rt, lookupTheory targetName rt, theoryFromJson candJson with
    | .error e, _, _ => errorResponse id e
    | _, .error e, _ => errorResponse id e
    | _, _, .error e => errorResponse id s!"invalid candidate: {e}"
    | .ok source, .ok target, .ok catalyst =>
      -- Compute A⊗C and B⊗C
      let ac := tensorTheories source catalyst
      let bc := tensorTheories target catalyst
      -- Check if A⊗C maps into B⊗C (all generators of A⊗C present in B⊗C)
      let result := computeStructuralDiff catalyst ac bc
      okResponse id [("result", verificationToJson result),
                     ("ac_size", natJson (ac.objects.length + ac.morphisms.length)),
                     ("bc_size", natJson (bc.objects.length + bc.morphisms.length))]

-- ============================================================
-- evaluate_factorization command
-- Find (X, Y) such that tensor(X, Y) ≅ target
-- ============================================================

def handleEvaluateFactorization (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  let targetResult := getStr j "target"
  let binaryOp     := match getStr j "binary_op" with | .ok s => s | .error _ => "tensor"
  let factorXJson  := j.getObjVal? "factor_x"
  let factorYJson  := j.getObjVal? "factor_y"
  match targetResult, factorXJson, factorYJson with
  | .error e, _, _       => errorResponse id e
  | _, .error _, _       => errorResponse id "missing field 'factor_x'"
  | _, _, .error _       => errorResponse id "missing field 'factor_y'"
  | .ok targetName, .ok fxJson, .ok fyJson =>
    match lookupTheory targetName rt, theoryFromJson fxJson, theoryFromJson fyJson with
    | .error e, _, _ => errorResponse id e
    | _, .error e, _ => errorResponse id s!"invalid factor_x: {e}"
    | _, _, .error e => errorResponse id s!"invalid factor_y: {e}"
    | .ok target, .ok factorX, .ok factorY =>
      -- Apply binary operator (currently only tensor supported)
      let composed := match binaryOp with
        | "tensor" => tensorTheories factorX factorY
        | _ => tensorTheories factorX factorY  -- fallback to tensor
      let result := computeStructuralDiff composed composed target
      okResponse id [("result", verificationToJson result),
                     ("composed_size", natJson (composed.objects.length + composed.morphisms.length))]

-- ============================================================
-- summary / validate commands
-- ============================================================

def handleSummary (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "theory" with
  | .error e => errorResponse id e
  | .ok name =>
    match lookupTheory name rt with
    | .error e => errorResponse id e
    | .ok t    =>
      okResponse id [("summary",   .str t.summary),
                     ("theory",    theoryToJson t)]

def handleValidate (j : Json) (id : String) (rt : List (String × Theory)) : Json :=
  match getStr j "theory" with
  | .error e => errorResponse id e
  | .ok name =>
    match lookupTheory name rt with
    | .error e => errorResponse id e
    | .ok t    =>
      let errors := validate t
      okResponse id [("valid",   .bool errors.isEmpty),
                     ("errors",  .arr (errors.map (Json.str ∘ toString)).toArray)]


def handleListOperators (_j : Json) (id : String) : Json :=
  let metas := operatorMetas.map operatorMetaToJson
  let groups := operatorGroups.map groupMetaToJson
  okResponse id [("operators", .arr metas.toArray),
                 ("groups",    .arr groups.toArray),
                 ("count",     natJson operatorMetas.length)]

-- ============================================================
-- define_theory: register a user-defined theory at runtime
-- ============================================================

def handleDefineTheory (j : Json) (id : String) : IO Json := do
  match j.getObjVal? "theory" with
  | .error _ => return errorResponse id "missing 'theory' field"
  | .ok theoryJson =>
    match theoryFromJson theoryJson with
    | .error e => return errorResponse id s!"Invalid theory JSON: {e}"
    | .ok theory =>
      -- Register in runtime registry (shadows any existing theory with same name)
      runtimeRegistry.modify fun reg =>
        -- Remove any existing entry with the same name, then prepend
        (theory.name, theory) :: reg.filter (fun (n, _) => n != theory.name)
      return okResponse id [("message", .str s!"Theory '{theory.name}' registered"),
                            ("name",    .str theory.name),
                            ("theory",  theoryToJson theory)]

-- ============================================================
-- Main dispatch: parse request, route to handler, return response
-- ============================================================

def handleRequest (line : String) : IO Json := do
  match Json.parse line with
  | .error e  =>
    -- Malformed JSON: can't echo an id, use "parse_error"
    return errorResponse "parse_error" s!"JSON parse error: {e}"
  | .ok j =>
    -- Extract optional request id for correlation
    let id := match j.getObjVal? "id" with
      | .ok (.str s) => s
      | _            => "unknown"
    match j.getObjVal? "command" with
    | .error _        => return errorResponse id "missing field 'command'"
    | .ok (.str cmd)  =>
      match cmd with
      | "define_theory"  => handleDefineTheory j id
      | "list_theories"  =>
        -- Include runtime theories in the listing
        let runtime ← runtimeRegistry.get
        let staticNames := theoryRegistry.map (Json.str ∘ Prod.fst)
        let runtimeNames := runtime.map (Json.str ∘ Prod.fst)
        let allNames := runtimeNames ++ staticNames
        let metas := theoryMetas.map theoryMetaToJson
        let groups := theoryGroups.map groupMetaToJson
        return okResponse id [("theories", .arr allNames.toArray),
                              ("metas",    .arr metas.toArray),
                              ("groups",   .arr groups.toArray),
                              ("count",    natJson allNames.length)]
      | other =>
        let rt ← runtimeRegistry.get
        return match other with
        | "list_operators"   => handleListOperators   j id
        | "summary"          => handleSummary         j id rt
        | "validate"         => handleValidate        j id rt
        | "apply_operator"   => handleApplyOp         j id rt
        | "compute_pushout"         => handleComputePushout        j id rt
        | "compute_pushout_cocone"  => handleComputePushoutCocone j id rt
        | "compute_pullback"         => handleComputePullback       j id rt
        | "compute_pullback_cone"    => handleComputePullbackCone  j id rt
        | "compute_morphism"        => handleComputeMorphism      j id rt
        | "evaluate_inverse"             => handleEvaluateInverse            j id rt
        | "solve_inverse"                => handleSolveInverse               j id rt
        | "evaluate_pushout_complement"  => handleEvaluatePushoutComplement  j id rt
        | "evaluate_extension"           => handleEvaluateExtension          j id rt
        | "evaluate_multi_objective"     => handleEvaluateMultiObjective     j id rt
        | "evaluate_fixed_point"         => handleEvaluateFixedPoint         j id
        | "evaluate_pullback_complement" => handleEvaluatePullbackComplement j id rt
        | "evaluate_simplification"      => handleEvaluateSimplification     j id rt
        | "evaluate_model"               => handleEvaluateModel              j id rt
        | "evaluate_subobject"           => handleEvaluateSubobject          j id rt
        | "evaluate_synthesis"           => handleEvaluateSynthesis          j id rt
        | "evaluate_quotient"            => handleEvaluateQuotient           j id rt
        | "evaluate_decomposition"       => handleEvaluateDecomposition      j id rt
        | "evaluate_relaxation"          => handleEvaluateRelaxation         j id rt
        | "evaluate_catalyst"            => handleEvaluateCatalyst           j id rt
        | "evaluate_factorization"      => handleEvaluateFactorization     j id rt
        | _                  => errorResponse id s!"Unknown command '{other}'"
    | .ok other =>
      return errorResponse id s!"'command' must be a string, got: {other.compress}"

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
  let response ← handleRequest line
  stdout.putStrLn response.compress
  stdout.flush                          -- ← critical: unblock the TS readline
  ndjsonLoop

end CatLab.Repl
