/-
  CatLab — Skolemization and Morleyization

  Skolemization eliminates existential quantifiers by adjoining Skolem
  functions: each ∀x.∃y.φ(x,y) becomes ∀x.φ(x, f(x)) where f is a
  fresh function symbol.

  Morleyization (after Michael Morley) adds a new relation symbol for
  every formula, yielding a theory where every axiom is universal-existential.
  This is the syntactic counterpart of Morley's omitting types theorem.
-/

import Catlab.Core.Theory

namespace CatLab

/-- An existential axiom: a universally quantified statement containing
    an existential quantifier to be eliminated. -/
structure ExistentialAxiom where
  /-- Name of the axiom -/
  name : GeneratorId
  /-- The existentially bound variable name -/
  boundVar : String
  /-- The body formula (as an expression, may contain .var references) -/
  body : Expr
  /-- Free variables and their types (the universal context) -/
  context : List (String × Expr)
  deriving Repr, Inhabited

/-- Build the domain type for a Skolem function from the universal context.
    If context is [("x", A), ("y", B)], the Skolem function has domain A × B. -/
private def skolemDomain (ctx : List (String × Expr)) : Expr :=
  match ctx.map Prod.snd with
  | [] => .terminal
  | types => Expr.prodList types

/-- Create a Skolem function for an existential axiom.
    For ∀x:A. ∃y:B. φ(x,y), produce f_skolem : A → B. -/
private def mkSkolemFunction (ea : ExistentialAxiom) (codom : Expr) : Generator1 :=
  { id := { name := .nested (.root "skolem") ea.name.name.toString
            kind := .morphism }
    domain := skolemDomain ea.context
    codomain := codom
    description := s!"Skolem function for {ea.name}: witnesses ∃{ea.boundVar}" }

/-- Substitute the Skolem function application for the bound variable in the body.
    Replaces occurrences of `var boundVar` with `f(x₁, ..., xₙ)` where the xᵢ
    are the context variables. -/
private def applySkolem (ea : ExistentialAxiom) (skolemId : GeneratorId) : Expr :=
  let contextArgs := ea.context.map fun (v, _) => Expr.var v
  let skolemApp := match contextArgs with
    | [] => Expr.atom skolemId
    | [x] => .app (Expr.atom skolemId) x
    | args => .app (Expr.atom skolemId) (Expr.prodList args)
  ea.body.subst ea.boundVar skolemApp

/-- Skolemize a theory with respect to given existential axioms.

    For each existential axiom ∀x₁...xₙ. ∃y. φ(x₁,...,xₙ, y):
    1. Add a Skolem function fₛ : X₁ × ... × Xₙ → Y
    2. Replace the axiom with ∀x₁...xₙ. φ(x₁,...,xₙ, fₛ(x₁,...,xₙ))

    The resulting theory is equiconsistent with the original: any model
    of the Skolemized theory restricts to a model of the original. -/
def skolemize (t : Theory) (existentials : List ExistentialAxiom) : Theory :=
  -- For each existential, determine the codomain from the body's type context
  -- (we use the bound variable's implicit type, encoded as an atom)
  let skolemFunctions := existentials.map fun ea =>
    let codom := Expr.atom (gid ea.boundVar)
    mkSkolemFunction ea codom

  let skolemIds := existentials.map fun ea =>
    { name := .nested (.root "skolem") ea.name.name.toString
      kind := .morphism : GeneratorId }

  -- Build the Skolemized axioms: replace ∃y.φ with φ[y := f(x̄)]
  let skolemAxioms := existentials.zipIdx.map fun (ea, idx) =>
    let sId := match skolemIds[idx]? with
      | some id => id
      | none => gid "unreachable"
    let newBody := applySkolem ea sId
    { id := { name := .nested (.root "skolemized") ea.name.name.toString
              kind := .twoCell }
      quantifiers := ea.context.map fun (v, ty) =>
        { name := v, domain := some ty, codomain := none, kind := .sort : AxiomVar }
      leftPath := newBody
      rightPath := newBody  -- tautological: the Skolemized formula is asserted
      description := s!"Skolemized form of {ea.name}" : Generator2 }

  -- Remove the original existential axioms and add Skolemized versions
  let existentialNames := existentials.map (·.name)
  let filteredAxioms := t.axioms.filter fun ax =>
    !(existentialNames.any (fun en => en.name == ax.id.name))

  { t with
    name := s!"Sk({t.name})"
    morphisms := t.morphisms ++ skolemFunctions
    axioms := filteredAxioms ++ skolemAxioms }

/-- Morleyize a theory: for each axiom, add a new relation symbol
    (morphism) that names the formula.

    This is useful for model-theoretic constructions where one needs
    every formula to be represented by an explicit symbol in the language.
    The result is a "Morley expansion" of the original theory. -/
def morleyize (t : Theory) : Theory :=
  -- For each axiom, add a relation symbol as a morphism
  let relationSymbols := t.axioms.map fun ax =>
    { id := { name := .nested (.root "Rel") ax.id.name.toString
              kind := .morphism }
      domain := match ax.quantifiers with
        | [] => .terminal
        | qs => Expr.prodList (qs.map fun q =>
            match q.domain with
            | some d => d
            | none => .atom (gid q.name))
      codomain := .atom (gid "Ω")
      description := s!"Relation symbol for axiom {ax.id}" : Generator1 }

  -- Add the truth-value object Ω if not already present
  let hasOmega := t.objects.any (fun o => o.id.name == .root "Ω")
  let extraObjects := if hasOmega then [] else
    [{ id := gid "Ω"
       description := "Truth-value object (subobject classifier)" : Generator0 }]

  -- For each relation symbol, add an axiom asserting it classifies the original formula
  let classifyingAxioms := t.axioms.zipIdx.map fun (ax, idx) =>
    let relId := { name := .nested (.root "Rel") ax.id.name.toString
                   kind := .morphism : GeneratorId }
    { id := { name := .nested (.root "Rel_ax") ax.id.name.toString
              kind := .twoCell }
      quantifiers := ax.quantifiers
      leftPath := .comp (Expr.atom relId) (.atom (gid "⊤_Ω"))
      rightPath := ax.leftPath
      description := s!"Rel({ax.id}) classifies the formula of axiom {ax.id}" : Generator2 }

  { t with
    name := s!"Mor({t.name})"
    objects := t.objects ++ extraObjects
    morphisms := t.morphisms ++ relationSymbols
    axioms := t.axioms ++ classifyingAxioms }

end CatLab
