/-
  CatLab — Syntactic / Classifying Category Construction

  Takes a theory (signature: sorts, function symbols, relation symbols, axioms)
  and constructs its classifying category:
  - Objects are contexts (lists of typed variables), represented as products of sorts
  - Morphisms are provably-equal classes of terms in context
  - Projection, weakening, substitution morphisms
  - Universal property: any model in a category C corresponds to a product-preserving
    functor from the classifying category to C
-/

import Catlab.Core.Theory

namespace CatLab

/-- A typed variable in a context -/
structure TypedVar where
  name : String
  sort : GeneratorId
  deriving Repr, Inhabited

/-- A context: a list of typed variables, represented categorically as a product of sorts -/
structure Context where
  vars : List TypedVar
  deriving Repr, Inhabited

namespace Context

def toExpr (ctx : Context) : Expr :=
  Expr.prodList (ctx.vars.map fun v => .atom v.sort)

def empty : Context := { vars := [] }

def extend (ctx : Context) (v : TypedVar) : Context :=
  { vars := ctx.vars ++ [v] }

def name (ctx : Context) : String :=
  if ctx.vars.isEmpty then "·"
  else String.intercalate "," (ctx.vars.map fun v => s!"{v.name}:{v.sort.name}")

end Context

/-- Build all singleton contexts from a theory's sorts -/
def singletonContexts (t : Theory) : List Context :=
  t.objects.map fun ob => { vars := [{ name := toString ob.id.name, sort := ob.id }] }

/-- Build pairwise product contexts from a theory's sorts -/
def pairContexts (t : Theory) : List Context :=
  t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { vars := [{ name := toString a.id.name, sort := a.id },
                  { name := toString b.id.name, sort := b.id }] }

/-- Construct the classifying (syntactic) category of a theory.

    Objects: contexts (finite products of sorts).
    Morphisms: equivalence classes of terms-in-context, plus structural morphisms.
    Axioms: the theory's axioms lifted to the syntactic category. -/
def syntacticCategory (t : Theory) : Theory :=
  -- Objects: the empty context, each singleton context, and pair contexts
  let emptyCtx : Context := Context.empty
  let singletons := singletonContexts t
  let pairs := pairContexts t

  let allContexts := [emptyCtx] ++ singletons ++ pairs

  let contextObjects := allContexts.map fun ctx =>
    { id := gid s!"[{ctx.name}]"
      description := s!"Context {ctx.name}" : Generator0 }

  -- Projection morphisms: for each pair context (A,B), projections π₁ and π₂
  let projections := pairs.flatMap fun ctx =>
    match ctx.vars with
    | [v1, v2] =>
      [{ id := gid s!"π₁_{v1.sort.name}_{v2.sort.name}"
         domain := ctx.toExpr
         codomain := .atom v1.sort
         description := s!"First projection from ({v1.sort.name},{v2.sort.name})" : Generator1 },
       { id := gid s!"π₂_{v1.sort.name}_{v2.sort.name}"
         domain := ctx.toExpr
         codomain := .atom v2.sort
         description := s!"Second projection from ({v1.sort.name},{v2.sort.name})" }]
    | _ => []

  -- Weakening morphisms: for each sort A and B, weakening w : [A] → [A,B]
  -- categorically the diagonal / pairing with identity
  let weakenings := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := gid s!"weaken_{a.id.name}_{b.id.name}"
        domain := .atom a.id
        codomain := .prod (.atom a.id) (.atom b.id)
        description := s!"Weakening: extend context {a.id.name} with {b.id.name}" : Generator1 }

  -- Substitution morphisms: for each morphism f : A → B in the theory,
  -- lifting to the syntactic category
  let substitutions := t.morphisms.map fun f =>
    { id := gid s!"subst_{f.id.name}"
      domain := f.domain
      codomain := f.codomain
      description := s!"Substitution by {f.id.name}" : Generator1 }

  -- Terminal morphisms: from each context to the empty context
  let terminalMaps := singletons.map fun ctx =>
    { id := gid s!"!_{ctx.name}"
      domain := ctx.toExpr
      codomain := .terminal
      description := s!"Terminal morphism from [{ctx.name}]" : Generator1 }

  -- Axioms from the theory become equations in the syntactic category
  let liftedAxioms := t.axioms.map fun ax =>
    { ax with
      id := gid s!"syn_{ax.id.name}"
      proofName := none
      description := s!"Syntactic lifting of {ax.id.name}" }

  -- Product-projection axioms: π₁ ∘ ⟨f,g⟩ = f
  let projAxioms := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := gid s!"proj_beta_{a.id.name}_{b.id.name}"
        leftPath := .comp (.atom (gid s!"weaken_{a.id.name}_{b.id.name}"))
                          (.atom (gid s!"π₁_{a.id.name}_{b.id.name}"))
        rightPath := Expr.id (.atom a.id)
        description := s!"β-rule: π₁ ∘ weaken = id at {a.id.name}" : Generator2 }

  { name := s!"Syn({t.name})"
    doctrine := { doctrine := .CartesianCategory }
    objects := contextObjects
    morphisms := projections ++ weakenings ++ substitutions ++ terminalMaps
    axioms := liftedAxioms ++ projAxioms }

/-- A model of a theory T in a category C is a product-preserving functor
    from the classifying category Syn(T) to C.

    Given a theory T and a "target" category C, this constructs the
    theory of models: functors Syn(T) → C preserving finite products. -/
def modelCategory (t : Theory) (c : Theory) : Theory :=
  let synT := syntacticCategory t

  -- For each object (context) in Syn(T), a model assigns an object of C
  let modelObjects := synT.objects.map fun ctx =>
    { id := gid s!"M({ctx.id.name})"
      description := s!"Image of {ctx.id.name} under model" : Generator0 }

  -- For each morphism in Syn(T), a model assigns a morphism of C
  let modelMorphisms := synT.morphisms.map fun f =>
    { id := gid s!"M({f.id.name})"
      domain := .atom (gid s!"M({repr f.domain})")
      codomain := .atom (gid s!"M({repr f.codomain})")
      description := s!"Image of {f.id.name} under model" : Generator1 }

  -- Product-preservation: M(A × B) ≅ M(A) × M(B)
  let preservationAxioms := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := gid s!"preserve_prod_{a.id.name}_{b.id.name}"
        leftPath := .atom (gid s!"M({repr (Expr.prod (.atom a.id) (.atom b.id))})")
        rightPath := .prod (.atom (gid s!"M([{a.id.name}])"))
                           (.atom (gid s!"M([{b.id.name}])"))
        description := s!"Product preservation: M({a.id.name}×{b.id.name}) ≅ M({a.id.name})×M({b.id.name})" : Generator2 }

  { name := s!"Mod({t.name},{c.name})"
    doctrine := c.doctrine
    objects := modelObjects
    morphisms := modelMorphisms
    axioms := preservationAxioms }

end CatLab
