/-
  CatLab -- REPL Protocol (NDJSON)

  JSON wire format for the TypeScript ↔ Lean CAS channel.
  Each message is a single minified JSON object on one line (NDJSON).

  REQUEST  (TypeScript → Lean):
    { "id": "r1", "command": "evaluate_inverse",
      "target": "Monoid", "forward_op": "decategorify_iso",
      "candidate": { <Theory JSON> } }

  RESPONSE (Lean → TypeScript):
    { "id": "r1", "status": "ok",    <result fields> }
    { "id": "r1", "status": "error", "message": "..." }

  Theory JSON:
    { "name": "...", "doctrine": "MonoidalCategory",
      "objects":   [{ "name": "A" }, ...],
      "morphisms": [{ "name": "μ", "domain": <Expr>, "codomain": <Expr> }, ...],
      "axioms":    [{ "name": "assoc", "lhs": <Expr>, "rhs": <Expr> }, ...] }

  Expr JSON (tagged single-key objects):
    "unit" | "terminal" | "initial"   →  Expr constants
    "X"                               →  Expr.atom (gid "X")  [bare string shorthand]
    { "atom": "X" }                   →  Expr.atom (gid "X")
    { "comp":   [e1, e2] }            →  Expr.comp e1 e2
    { "tensor": [e1, e2] }            →  Expr.tensor e1 e2
    { "prod":   [e1, e2] }            →  Expr.prod e1 e2
    { "hom":    [e1, e2] }            →  Expr.hom e1 e2
    { "coprod": [e1, e2] }            →  Expr.coprod e1 e2
    { "id": e }                       →  Expr.id e
-/

import Lean
import Catlab.Core.Theory
import Catlab.Core.Doctrine
import Catlab.Core.Validate
import Catlab.Core.InverseProblem

namespace CatLab.Repl

open CatLab
open Lean (Json JsonNumber)

-- ============================================================
-- JSON field helpers
-- NOTE: Lean.Json.getObjVal? returns Except String Json (not Option)
-- ============================================================

def getStr (j : Json) (key : String) : Except String String :=
  match j.getObjVal? key with
  | .ok (.str s) => .ok s
  | .ok _        => .error s!"field '{key}' must be a string"
  | .error _     => .error s!"missing required field '{key}'"

def getStrOpt (j : Json) (key : String) : String :=
  match j.getObjVal? key with
  | .ok (.str s) => s
  | _            => ""

def getObjArr (j : Json) (key : String) : Except String (Array Json) :=
  match j.getObjVal? key with
  | .ok (.arr a) => .ok a
  | .ok _        => .error s!"field '{key}' must be an array"
  | .error _     => .ok #[]   -- missing array = empty (optional field)

def natJson (n : Nat) : Json :=
  .num { mantissa := Int.ofNat n, exponent := 0 }

-- ============================================================
-- Doctrine deserialization
-- ============================================================

/-- Short names for each doctrine, used when serializing theories to JSON.
    Produces "CartesianClosed" not "CatLab.Doctrine.CartesianClosed", so the
    LLM sees clean strings it can copy back verbatim. -/
def doctrineToStr : Doctrine → String
  | .Category                    => "Category"
  | .CartesianCategory           => "CartesianCategory"
  | .CartesianClosed             => "CartesianClosed"
  | .MonoidalCategory            => "MonoidalCategory"
  | .BraidedMonoidal             => "BraidedMonoidal"
  | .SymmetricMonoidal           => "SymmetricMonoidal"
  | .SymmetricMonoidalClosed     => "SymmetricMonoidalClosed"
  | .FinitelyComplete            => "FinitelyComplete"
  | .FinitelyCocomplete          => "FinitelyCocomplete"
  | .Abelian                     => "Abelian"
  | .Topos                       => "Topos"
  | .GrothendieckTopos           => "GrothendieckTopos"
  | .LawvereTheory               => "LawvereTheory"
  | .StableCategory              => "StableCategory"
  | .ElementaryTopos             => "ElementaryTopos"
  | .MartinLofTypeTheory         => "MartinLofTypeTheory"
  | .PresentableInfinityCategory => "PresentableInfinityCategory"
  | .ModelCategory               => "ModelCategory"
  | .Derivator                   => "Derivator"
  | .InfinityNCategory           => "InfinityNCategory"
  | .Operad                      => "Operad"
  | .CubicalTypeTheory           => "CubicalTypeTheory"
  | .LinearLogic                 => "LinearLogic"
  | .GeometricLogic              => "GeometricLogic"
  | .CohesiveHomotopyTypeTheory  => "CohesiveHomotopyTypeTheory"
  | .EnrichedCategory            => "EnrichedCategory"
  | .TriangulatedCategory        => "TriangulatedCategory"
  | .Locale                      => "Locale"
  | .DifferentialGraded          => "DifferentialGraded"

def doctrineFromStr (raw : String) : Except String Doctrine :=
  -- Strip Lean repr prefix so both "CartesianClosed" and
  -- "CatLab.Doctrine.CartesianClosed" are accepted
  let s := raw.stripPrefix "CatLab.Doctrine."
  match s with
  | "Category"                    => .ok .Category
  | "CartesianCategory"           => .ok .CartesianCategory
  | "CartesianClosed"             => .ok .CartesianClosed
  | "MonoidalCategory"            => .ok .MonoidalCategory
  | "BraidedMonoidal"             => .ok .BraidedMonoidal
  | "SymmetricMonoidal"           => .ok .SymmetricMonoidal
  | "SymmetricMonoidalClosed"     => .ok .SymmetricMonoidalClosed
  | "FinitelyComplete"            => .ok .FinitelyComplete
  | "FinitelyCocomplete"          => .ok .FinitelyCocomplete
  | "Abelian"                     => .ok .Abelian
  | "Topos"                       => .ok .Topos
  | "GrothendieckTopos"           => .ok .GrothendieckTopos
  | "LawvereTheory"               => .ok .LawvereTheory
  | "StableCategory"              => .ok .StableCategory
  | "ElementaryTopos"             => .ok .ElementaryTopos
  | "MartinLofTypeTheory"         => .ok .MartinLofTypeTheory
  | "PresentableInfinityCategory" => .ok .PresentableInfinityCategory
  | "ModelCategory"               => .ok .ModelCategory
  | "Derivator"                   => .ok .Derivator
  | "InfinityNCategory"           => .ok .InfinityNCategory
  | "Operad"                      => .ok .Operad
  | "CubicalTypeTheory"           => .ok .CubicalTypeTheory
  | "LinearLogic"                 => .ok .LinearLogic
  | "GeometricLogic"              => .ok .GeometricLogic
  | "CohesiveHomotopyTypeTheory"  => .ok .CohesiveHomotopyTypeTheory
  | "EnrichedCategory"            => .ok .EnrichedCategory
  | "TriangulatedCategory"        => .ok .TriangulatedCategory
  | "Locale"                      => .ok .Locale
  | "DifferentialGraded"          => .ok .DifferentialGraded
  | s                             => .error s!"Unknown doctrine '{s}' (raw: '{raw}')"

-- ============================================================
-- Expr deserialization
-- ============================================================

-- Parse a 2-element array into a binary Expr constructor
private def parseBinary2 (args : Array Json) (tag : String)
    (ctor : Expr → Expr → Expr) (recurse : Json → Except String Expr)
    : Except String Expr :=
  if args.size == 2 then
    match recurse args[0]!, recurse args[1]! with
    | .ok a, .ok b => .ok (ctor a b)
    | .error e, _  => .error e
    | _, .error e  => .error e
  else .error s!"'{tag}' requires exactly 2 elements, got {args.size}"

/-- Parse a JSON value into a CatLab Expr. -/
partial def exprFromJson (j : Json) : Except String Expr :=
  match j with
  | .str "unit"     => .ok .unit
  | .str "terminal" => .ok .terminal
  | .str "initial"  => .ok .initial
  | .str s          => .ok (.atom (gid s 0 .sort))   -- bare string shorthand
  | .obj _          =>
    -- Try "atom" first
    match j.getObjVal? "atom" with
    | .ok (.str s) => .ok (.atom (gid s 0 .sort))
    | .ok _        => .error "'atom' value must be a string"
    | .error _     =>
      -- Try binary constructors as a list — return first that matches
      let binaryTags : List (String × (Expr → Expr → Expr)) :=
        [("comp", .comp), ("tensor", .tensor), ("prod", .prod),
         ("hom", .hom), ("coprod", .coprod)]
      let binaryResult : Option (Except String Expr) :=
        binaryTags.findSome? fun (tag, ctor) =>
          match j.getObjVal? tag with
          | .ok (.arr args) => some (parseBinary2 args tag ctor exprFromJson)
          | .ok _           => some (.error s!"'{tag}' must be an array")
          | .error _        => none
      match binaryResult with
      | some r => r
      | none   =>
        -- Try "id"
        match j.getObjVal? "id" with
        | .ok inner => (exprFromJson inner).map .id
        | .error _  => .error s!"unrecognized Expr tag in: {j.compress}"
  | other => .error s!"expected string or object Expr, got: {other.compress}"

-- ============================================================
-- Theory deserialization
-- ============================================================

def objectFromJson (j : Json) : Except String Generator0 :=
  match j.getObjVal? "name" with
  | .ok (.str n) =>
    let desc := getStrOpt j "description"
    .ok { id := { name := Name.root n, kind := .sort }, description := desc }
  | .ok _ => .error "object 'name' must be a string"
  | .error _ => .error "object missing required field 'name'"

def morphismFromJson (j : Json) : Except String Generator1 := do
  let name ← getStr j "name"
  let domJson ← match j.getObjVal? "domain" with
    | .ok dj  => .ok dj
    | .error _ => .error s!"morphism '{name}' missing 'domain'"
  let codJson ← match j.getObjVal? "codomain" with
    | .ok cj  => .ok cj
    | .error _ => .error s!"morphism '{name}' missing 'codomain'"
  let dom ← exprFromJson domJson
  let cod ← exprFromJson codJson
  let desc := getStrOpt j "description"
  .ok { id := { name := Name.root name, kind := .morphism },
        domain := dom, codomain := cod, description := desc }

def axiomFromJson (j : Json) : Except String Generator2 := do
  let name ← getStr j "name"
  -- Accept "lhs"/"rhs" or "leftPath"/"rightPath"
  let lhsKey := match j.getObjVal? "lhs" with | .ok _ => "lhs" | _ => "leftPath"
  let rhsKey := match j.getObjVal? "rhs" with | .ok _ => "rhs" | _ => "rightPath"
  let lhsJson ← match j.getObjVal? lhsKey with
    | .ok lj  => .ok lj
    | .error _ => .error s!"axiom '{name}' missing 'lhs'/'leftPath'"
  let rhsJson ← match j.getObjVal? rhsKey with
    | .ok rj  => .ok rj
    | .error _ => .error s!"axiom '{name}' missing 'rhs'/'rightPath'"
  let lhs ← exprFromJson lhsJson
  let rhs ← exprFromJson rhsJson
  let desc := getStrOpt j "description"
  .ok { id := { name := Name.root name, kind := .twoCell },
        leftPath := lhs, rightPath := rhs, description := desc }

/-- Deserialize a Theory from JSON.
    Unknown fields (e.g. LLM-generated "notes", "reasoning", "confidence") are
    silently ignored — only the known keys are extracted via getObjVal?.
    This is intentional: the LLM occasionally adds helpful but schema-breaking
    commentary fields, and crashing on them would abort an otherwise valid theory. -/
def theoryFromJson (j : Json) : Except String Theory := do
  let name     ← getStr j "name"
  let docStr   := match j.getObjVal? "doctrine" with
    | .ok (.str s) => s | _ => "Category"
  let doctrine ← doctrineFromStr docStr
  let objsArr  ← getObjArr j "objects"
  let morsArr  ← getObjArr j "morphisms"
  let axsArr   ← getObjArr j "axioms"
  let objects   ← objsArr.toList.mapM objectFromJson
  let morphisms ← morsArr.toList.mapM morphismFromJson
  let axioms    ← axsArr.toList.mapM axiomFromJson
  let theory : Theory := { name, doctrine := { doctrine }, objects, morphisms, axioms }
  -- Auto-upgrade doctrine: if the LLM wrote `prod` but labeled it "Category",
  -- infer the actual minimum doctrine and upgrade silently.
  .ok theory.autoUpgradeDoctrine

-- ============================================================
-- Serialization: Theory → Json
-- ============================================================

partial def exprToJson : Expr → Json
  | .atom gid   => Json.mkObj [("atom",   .str gid.name.toString)]
  | .id obj     => Json.mkObj [("id",     exprToJson obj)]
  | .comp f g   => Json.mkObj [("comp",   .arr #[exprToJson f, exprToJson g])]
  | .tensor a b => Json.mkObj [("tensor", .arr #[exprToJson a, exprToJson b])]
  | .prod a b   => Json.mkObj [("prod",   .arr #[exprToJson a, exprToJson b])]
  | .hom a b    => Json.mkObj [("hom",    .arr #[exprToJson a, exprToJson b])]
  | .coprod a b => Json.mkObj [("coprod", .arr #[exprToJson a, exprToJson b])]
  | .unit       => .str "unit"
  | .terminal   => .str "terminal"
  | .initial    => .str "initial"
  | e           => .str e.toName.toString   -- fallback

def objectToJson (o : Generator0) : Json :=
  Json.mkObj [("name", .str o.id.name.toString), ("description", .str o.description)]

def morphismToJson (m : Generator1) : Json :=
  Json.mkObj [
    ("name",        .str m.id.name.toString),
    ("domain",      exprToJson m.domain),
    ("codomain",    exprToJson m.codomain),
    ("description", .str m.description)]

def axiomToJson (a : Generator2) : Json :=
  Json.mkObj [
    ("name",        .str a.id.name.toString),
    ("lhs",         exprToJson a.leftPath),
    ("rhs",         exprToJson a.rightPath),
    ("description", .str a.description)]

def theoryToJson (t : Theory) : Json :=
  Json.mkObj [
    ("name",      .str t.name),
    ("doctrine",  .str (doctrineToStr t.doctrine.doctrine)),
    ("objects",   .arr (t.objects.map objectToJson).toArray),
    ("morphisms", .arr (t.morphisms.map morphismToJson).toArray),
    ("axioms",    .arr (t.axioms.map axiomToJson).toArray)]

-- ============================================================
-- Serialization: VerificationResult → Json
-- ============================================================

def missingSignatureToJson (s : MorphismSignature) : Json :=
  Json.mkObj [
    ("domainShape",   .str s.domainShape.toName.toString),
    ("codomainShape", .str s.codomainShape.toName.toString),
    ("sourceName",    .str s.sourceName.toString)]

def axiomViolationToJson (v : AxiomViolation) : Json :=
  let base := [
    ("sourceAxiom", .str v.sourceAxiom.id.name.toString),
    ("status",      .str (toString v.status)),
    ("lhsReduced",  .str v.lhsReduced.toName.toString),
    ("rhsReduced",  .str v.rhsReduced.toName.toString),
    ("depthUsed",   natJson v.depthUsed)]
  -- Include rewrite traces when non-empty (timeout diagnostics)
  let withTrace := base ++
    (if v.lhsTrace.isEmpty then [] else
      [("lhsTrace", .arr (v.lhsTrace.map (.str ∘ toString)).toArray)]) ++
    (if v.rhsTrace.isEmpty then [] else
      [("rhsTrace", .arr (v.rhsTrace.map (.str ∘ toString)).toArray)])
  Json.mkObj withTrace

def verificationToJson (r : VerificationResult) : Json :=
  Json.mkObj [
    ("verified",           .bool r.verified),
    ("candidateName",      .str r.candidate.name),
    ("verificationStatus", .str (toString r.status)),
    ("missingSignatures",  .arr (r.missingSignatures.map missingSignatureToJson).toArray),
    ("unmappedObjects",    .arr (r.unmappedObjects.map (.str ∘ toString)).toArray),
    ("axiomViolations",    .arr (r.axiomViolations.map axiomViolationToJson).toArray),
    ("doctrine",           .str (toString (repr r.candidate.doctrine.doctrine)))]

-- ============================================================
-- Serialization: TheoryMorphism → Json
-- ============================================================

/-- Serialize a GeneratorMap entry as a JSON object { "source": "name", "target": <expr> } -/
def generatorMapEntryToJson (entry : GeneratorId × Expr) : Json :=
  Json.mkObj [
    ("source", .str entry.1.name.toString),
    ("target", exprToJson entry.2)]

/-- Serialize a TheoryMorphism to JSON.
    Exposes the explicit generator mappings so the TS orchestrator can
    inspect functor action on objects and morphisms. -/
def theoryMorphismToJson (tm : TheoryMorphism) : Json :=
  Json.mkObj [
    ("name",         .str tm.name),
    ("source",       .str tm.source.name),
    ("target",       .str tm.target.name),
    ("onObjects",    .arr (tm.onObjects.toList.map generatorMapEntryToJson).toArray),
    ("onMorphisms",  .arr (tm.onMorphisms.toList.map generatorMapEntryToJson).toArray)]

-- ============================================================
-- Response helpers
-- ============================================================

def okResponse (id : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("id", .str id) :: ("status", .str "ok") :: fields)

def errorResponse (id : String) (msg : String) : Json :=
  Json.mkObj [("id", .str id), ("status", .str "error"), ("message", .str msg)]

end CatLab.Repl
