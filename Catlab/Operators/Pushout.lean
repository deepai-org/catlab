/-
  CatLab -- Pushout of Theories (Amalgamated Sum)

  The pushout of two morphisms f : T₀ → T₁ and g : T₀ → T₂ is the
  amalgamated sum T₁ ⊔_{T₀} T₂: the theory that freely identifies
  f(x) with g(x) for every generator x in T₀.

  This is the fundamental Tier 2 combinator. All other combinators derive:

    theoryCoproduct T₁ T₂      = pushout (initialMorphism T₁) (initialMorphism T₂)
    theoryExtend T T'           = pushout (inclusion T T') (id T)
    theoryQuotient T eqs        = pushout (inclusion T T_eqs) (id T)

  Algorithm:
    1. Tag T₁'s generators with Name.inl, T₂'s with Name.inr  →  disjoint union.
    2. For each T₀-generator x: emit Union-Find equation inl(f(x)) ~ inr(g(x)).
    3. Collapse: keep one rep per equivalence class, rewrite all Exprs through rep.

  The inl/inr tagging is consistent with Coproduct.lean, so
  `pushout (initialMorphism T₁) (initialMorphism T₂)` produces exactly
  the same theory as `coproductCategory T₁ T₂`.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Catlab.Core.Primitives
import Catlab.Operators.Quotient   -- for UnionFind

namespace CatLab

/-- The pushout T₁ ⊔_{T₀} T₂ of f : T₀ → T₁ and g : T₀ → T₂.
    Returns `none` when f and g have different source theories (no shared base). -/
def pushout (f g : TheoryMorphism) : Option Theory :=
  if f.source.name != g.source.name then none
  else
    let t0 := f.source
    let t1 := f.target
    let t2 := g.target

    -- Step 1: disjoint union via Name.inl / Name.inr tagging
    let tag1 : Name → Name := .inl
    let tag2 : Name → Name := .inr

    let disjObjects :=
      (t1.objects.map fun o => { o with id := { o.id with name := tag1 o.id.name } }) ++
      (t2.objects.map fun o => { o with id := { o.id with name := tag2 o.id.name } })

    let disjMorphisms :=
      (t1.morphisms.map fun m =>
        { m with
          id       := { m.id with name := tag1 m.id.name }
          domain   := m.domain.mapNames tag1
          codomain := m.codomain.mapNames tag1 }) ++
      (t2.morphisms.map fun m =>
        { m with
          id       := { m.id with name := tag2 m.id.name }
          domain   := m.domain.mapNames tag2
          codomain := m.codomain.mapNames tag2 })

    let disjAxioms :=
      (t1.axioms.map fun a =>
        { a with
          id        := { a.id with name := tag1 a.id.name }
          leftPath  := a.leftPath.mapNames  tag1
          rightPath := a.rightPath.mapNames tag1 }) ++
      (t2.axioms.map fun a =>
        { a with
          id        := { a.id with name := tag2 a.id.name }
          leftPath  := a.leftPath.mapNames  tag2
          rightPath := a.rightPath.mapNames tag2 })

    -- Step 2: Union-Find equations from T₀ generators
    -- For object x in T₀: unify inl(f(x)) with inr(g(x))
    -- For morphism m in T₀: unify inl(f(m)) with inr(g(m))
    -- We extract Name from atomic Exprs; non-atomic maps are not supported here
    -- (non-atomic maps arise only with exotic morphisms, not from `inclusion`).
    let equations : List (Name × Name) :=
      (t0.objects.filterMap fun o =>
        match (f.onObjects.apply o.id).mapNames tag1,
              (g.onObjects.apply o.id).mapNames tag2 with
        | .atom l, .atom r => some (l.name, r.name)
        | _, _ => none) ++
      (t0.morphisms.filterMap fun m =>
        match (f.onMorphisms.apply m.id).mapNames tag1,
              (g.onMorphisms.apply m.id).mapNames tag2 with
        | .atom l, .atom r => some (l.name, r.name)
        | _, _ => none)

    -- Step 3: collapse via Union-Find
    let uf  := equations.foldl (fun uf (a, b) => uf.union a b) UnionFind.empty
    let rep : Name → Name := uf.find

    let rewrite (e : Expr) : Expr := e.mapNames rep

    -- Keep only the canonical representative from each equivalence class
    let keptObjects   := disjObjects.filter   fun o => rep o.id.name == o.id.name
    let keptMorphisms := (disjMorphisms.filter fun m => rep m.id.name == m.id.name).map
      fun m => { m with domain := rewrite m.domain, codomain := rewrite m.codomain }

    -- Rewrite axioms and deduplicate (collapse may merge axioms from the two sides)
    let rawAxioms := disjAxioms.map fun a =>
      { a with
        id        := { a.id with name := rep a.id.name }
        leftPath  := rewrite a.leftPath
        rightPath := rewrite a.rightPath }
    let keptAxioms := rawAxioms.foldl
      (fun acc a => if acc.any (fun b => b.id == a.id) then acc else a :: acc) []
      |>.reverse

    some {
      name      := s!"{t1.name} ⊔_({t0.name}) {t2.name}"
      doctrine  := t1.doctrine   -- TODO: join doctrines (use the richer of t1/t2)
      objects   := keptObjects
      morphisms := keptMorphisms
      axioms    := keptAxioms }

/-- A pushout cocone: the apex theory P plus the two inclusion morphisms
    (cocone legs) with correct name mappings.
    Unlike computing inclusions post-hoc via `TheoryMorphism.inclusion`,
    these legs are constructed at pushout time and correctly account for
    the inl/inr tagging and Union-Find collapse. -/
structure PushoutCocone where
  apex : Theory
  /-- Left leg: T₁ → P, mapping each T₁-generator to rep(inl(x)) in P -/
  leftLeg : TheoryMorphism
  /-- Right leg: T₂ → P, mapping each T₂-generator to rep(inr(x)) in P -/
  rightLeg : TheoryMorphism

/-- Compute the pushout cocone with correct cocone leg mappings.
    The key insight: at pushout construction time, we know that generator x
    in T₁ maps to `rep(inl(x))` in P, and generator y in T₂ maps to
    `rep(inr(y))` in P. This avoids the name-matching failure of
    `TheoryMorphism.inclusion` on pushout outputs. -/
def pushoutCocone (f g : TheoryMorphism) : Option PushoutCocone :=
  if f.source.name != g.source.name then none
  else
    let t0 := f.source
    let t1 := f.target
    let t2 := g.target

    -- Recompute the same Union-Find as `pushout` to get `rep`
    let tag1 : Name → Name := .inl
    let tag2 : Name → Name := .inr

    let equations : List (Name × Name) :=
      (t0.objects.filterMap fun o =>
        match (f.onObjects.apply o.id).mapNames tag1,
              (g.onObjects.apply o.id).mapNames tag2 with
        | .atom l, .atom r => some (l.name, r.name)
        | _, _ => none) ++
      (t0.morphisms.filterMap fun m =>
        match (f.onMorphisms.apply m.id).mapNames tag1,
              (g.onMorphisms.apply m.id).mapNames tag2 with
        | .atom l, .atom r => some (l.name, r.name)
        | _, _ => none)

    let uf := equations.foldl (fun uf (a, b) => uf.union a b) UnionFind.empty
    let rep : Name → Name := uf.find

    -- Get the actual pushout theory
    match pushout f g with
    | none => none
    | some apex =>
      -- Left leg: T₁ → P. Each T₁-generator x maps to rep(inl(x)) in P.
      let leftOnObjects := GeneratorMap.ofList
        (t1.objects.map fun o =>
          let pushoutName := rep (tag1 o.id.name)
          (o.id, .atom { o.id with name := pushoutName }))
      let leftOnMorphisms := GeneratorMap.ofList
        (t1.morphisms.map fun m =>
          let pushoutName := rep (tag1 m.id.name)
          (m.id, .atom { m.id with name := pushoutName }))
      let leftLeg : TheoryMorphism :=
        { name := s!"ι₁ : {t1.name} → {apex.name}"
          source := t1
          target := apex
          onObjects := leftOnObjects
          onMorphisms := leftOnMorphisms }

      -- Right leg: T₂ → P. Each T₂-generator y maps to rep(inr(y)) in P.
      let rightOnObjects := GeneratorMap.ofList
        (t2.objects.map fun o =>
          let pushoutName := rep (tag2 o.id.name)
          (o.id, .atom { o.id with name := pushoutName }))
      let rightOnMorphisms := GeneratorMap.ofList
        (t2.morphisms.map fun m =>
          let pushoutName := rep (tag2 m.id.name)
          (m.id, .atom { m.id with name := pushoutName }))
      let rightLeg : TheoryMorphism :=
        { name := s!"ι₂ : {t2.name} → {apex.name}"
          source := t2
          target := apex
          onObjects := rightOnObjects
          onMorphisms := rightOnMorphisms }

      some { apex, leftLeg, rightLeg }

/-- Coproduct as pushout over ⊥.  Equivalent to `coproductCategory` but derived
    from first principles, making the algebraic relationship explicit. -/
def theoryCoproduct (t1 t2 : Theory) : Theory :=
  pushout (initialMorphism t1) (initialMorphism t2) |>.getD
    { name := s!"{t1.name} ⊔ {t2.name}", doctrine := t1.doctrine,
      objects := [], morphisms := [], axioms := [] }

end CatLab
