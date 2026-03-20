/-
  CatLab -- Naturality and Coherence Checking

  Verifies that:
  1. Natural transformation families satisfy naturality squares
  2. Monoidal categories have required coherence axioms (pentagon, triangle, hexagon)
  3. Axiom schemas in functor categories are well-formed

  Uses the bounded Knuth-Bendix rewriter for equation checking where possible,
  and structural checks for axiom presence.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Catlab.Core.KnuthBendix

namespace CatLab

-- ============================================================
-- Coherence checking results
-- ============================================================

/-- A coherence check result -/
inductive CoherenceResult where
  | ok (message : String)
  | missing (message : String)
  | failed (message : String)
  deriving Repr, Inhabited

instance : ToString CoherenceResult where
  toString
    | .ok msg => s!"[OK] {msg}"
    | .missing msg => s!"[MISSING] {msg}"
    | .failed msg => s!"[FAILED] {msg}"

def CoherenceResult.isOk : CoherenceResult → Bool
  | .ok _ => true
  | _ => false

-- ============================================================
-- Naturality checking
-- ============================================================

/-- Check that a NatTransFamily satisfies the naturality condition.
    For each morphism f : A → B in the source theory, verify:
      α_B ∘ F(f) = G(f) ∘ α_A
    using KB normalization on the theory's axioms.

    Parameters:
    - `t`: the ambient theory containing the axioms
    - `family`: the natural transformation family
    - `fOnMor`: how the source functor F acts on morphisms
    - `gOnMor`: how the target functor G acts on morphisms
    - `sourceMorphisms`: the morphisms to check naturality over -/
def checkNaturality
    (t : Theory)
    (family : NatTransFamily)
    (fOnMor gOnMor : GeneratorMap)
    (sourceMorphisms : List Generator1) : List CoherenceResult :=
  sourceMorphisms.map fun f =>
    -- Find α components at domain and codomain of f
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let αDom := family.components.find? fun (objId, _) => objId.name == domName
    let αCod := family.components.find? fun (objId, _) => objId.name == codName
    match αDom, αCod with
    | some (_, compDom), some (_, compCod) =>
      -- Build the two sides of the naturality square:
      -- LHS: α_B ∘ F(f)
      let lhs := Expr.comp (fOnMor.apply f.id) (.atom compCod.id)
      -- RHS: G(f) ∘ α_A
      let rhs := Expr.comp (.atom compDom.id) (gOnMor.apply f.id)
      -- Check via KB
      if KnuthBendix.kbEqual t.axioms lhs rhs then
        .ok s!"Naturality at {f.id.name}: α_cod ∘ F(f) = G(f) ∘ α_dom"
      else
        .failed s!"Naturality fails at {f.id.name}: α_cod ∘ F(f) ≠ G(f) ∘ α_dom"
    | none, _ => .missing s!"No component at domain of {f.id.name}"
    | _, none => .missing s!"No component at codomain of {f.id.name}"

/-- Check naturality of a natural transformation by examining axioms.
    Looks for axioms matching the pattern `comp(α_dom, G(f)) = comp(F(f), α_cod)`
    where α is indexed by a common prefix and f ranges over source morphisms.

    This is a structural check: it verifies that the AXIOMS encoding naturality
    are present and well-typed, not that they hold (that's KB's job). -/
def checkNaturalityAxiomsPresent
    (t : Theory)
    (componentPrefix : Name)
    (sourceMorphisms : List Generator1) : List CoherenceResult :=
  sourceMorphisms.map fun f =>
    -- Look for an axiom whose name contains the morphism's name
    -- and whose LHS or RHS references components at domain and codomain
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let hasNatAxiom := t.axioms.any fun ax =>
      let atoms := ax.leftPath.atoms ++ ax.rightPath.atoms
      -- Check: axiom references both a component at dom and a component at cod
      let hasDomRef := atoms.any fun a => match a with
        | .app pfx n => pfx == componentPrefix && n == domName
        | _ => false
      let hasCodRef := atoms.any fun a => match a with
        | .app pfx n => pfx == componentPrefix && n == codName
        | _ => false
      hasDomRef && hasCodRef
    if hasNatAxiom then
      .ok s!"Naturality axiom present for {f.id.name}"
    else
      .missing s!"No naturality axiom found for {f.id.name}"

-- ============================================================
-- Monoidal coherence checking
-- ============================================================

/-- Required coherence axiom names for a monoidal category -/
private def monoidalCoherenceNames : List String :=
  ["pentagon", "triangle"]

/-- Additional coherence for symmetric monoidal -/
private def symmetricCoherenceNames : List String :=
  ["hexagon", "symm_invol"]

/-- Check that a theory with monoidal doctrine has the required coherence axioms.
    Verifies:
    - Pentagon identity (associator coherence)
    - Triangle identity (unitor coherence)
    - Hexagon identity (symmetry coherence, if symmetric)
    - Symmetry involutivity (if symmetric) -/
def checkMonoidalCoherence (t : Theory) : List CoherenceResult :=
  let isMonoidal := match t.doctrine.doctrine with
    | .MonoidalCategory | .BraidedMonoidal | .SymmetricMonoidal
    | .SymmetricMonoidalClosed => true
    | _ => false
  let isSymmetric := match t.doctrine.doctrine with
    | .SymmetricMonoidal | .SymmetricMonoidalClosed | .BraidedMonoidal => true
    | _ => false
  if !isMonoidal then []
  else
    let requiredNames := monoidalCoherenceNames ++
      (if isSymmetric then symmetricCoherenceNames else [])
    requiredNames.map fun name =>
      let found := t.axioms.any fun ax =>
        match ax.id.name with
        | .root n => n == name
        | _ => false
      if found then
        .ok s!"Coherence axiom '{name}' present"
      else
        .missing s!"Coherence axiom '{name}' missing"

/-- Check that isomorphism axioms are present for structural morphisms.
    For each morphism name in `isoNames`, verify that there exists an axiom
    asserting `f ∘ f⁻¹ = id` (or equivalent). -/
def checkIsomorphismAxioms (t : Theory) (isoNames : List (String × String)) : List CoherenceResult :=
  isoNames.map fun (fwd, inv) =>
    let found := t.axioms.any fun ax =>
      let atoms := ax.leftPath.atoms ++ ax.rightPath.atoms
      let hasFwd := atoms.any fun a => match a with
        | .root n => n == fwd
        | _ => false
      let hasInv := atoms.any fun a => match a with
        | .root n => n == inv
        | _ => false
      hasFwd && hasInv
    if found then
      .ok s!"Isomorphism axiom for {fwd}/{inv} present"
    else
      .missing s!"Isomorphism axiom for {fwd}/{inv} missing"

-- ============================================================
-- Axiom well-formedness beyond basic validation
-- ============================================================

/-- Check that quantified axiom schemas have well-formed quantifiers:
    each quantifier variable should appear in the axiom's LHS or RHS. -/
def checkQuantifierUsage (t : Theory) : List CoherenceResult :=
  t.axioms.flatMap fun ax =>
    if ax.quantifiers.isEmpty then []
    else
      ax.quantifiers.filterMap fun qv =>
        let varExpr := Expr.var qv.name
        let usedInLHS := ax.leftPath.atoms.any (· == .root qv.name) ||
          ax.leftPath == varExpr
        let usedInRHS := ax.rightPath.atoms.any (· == .root qv.name) ||
          ax.rightPath == varExpr
        if usedInLHS || usedInRHS then none
        else some (.missing s!"Quantifier '{qv.name}' in axiom '{ax.id.name}' not referenced in LHS or RHS")

/-- Run all coherence checks on a theory. Returns a summary. -/
def checkCoherence (t : Theory) : List CoherenceResult :=
  checkMonoidalCoherence t ++
  checkQuantifierUsage t ++
  checkIsomorphismAxioms t
    [("assoc", "assoc_inv"), ("l_unitor", "l_unitor_inv"), ("r_unitor", "r_unitor_inv")]

end CatLab
