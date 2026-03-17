/-
  CatLab — Categories with Families (CwF) / Comprehension Categories

  Given a base category of contexts and a presheaf of types (with terms),
  build the comprehension category where:

  - Objects: contexts from the base, plus extended contexts Γ.A for each
    context Γ and type A in context Γ
  - Morphisms: substitutions from the base, plus projections p : Γ.A → Γ
    and generic terms q : Γ.A → A[p]
  - Satisfies the universal property of context extension
-/

import Catlab.Core.Theory

namespace CatLab

/-- Data for a category with families: a base category of contexts,
    together with types and terms indexed over it. -/
structure CwFData where
  /-- The base theory (category of contexts and substitutions) -/
  base : Theory
  /-- Types in context: for each context Γ, a list of type names -/
  types : List (GeneratorId × List GeneratorId)
  /-- Terms in context: for each (context, type) pair, a list of term names -/
  terms : List (GeneratorId × GeneratorId × List GeneratorId)
  deriving Repr, Inhabited

/-- Build the comprehension category from CwF data.

    Extends the base category with context extension objects Γ.A,
    projection morphisms p : Γ.A → Γ, and generic term morphisms
    q, satisfying the universal property of comprehension. -/
def comprehensionCategory (cwf : CwFData) : Theory :=
  let base := cwf.base

  -- Extended context objects: for each context Γ and type A in Γ,
  -- add an object Γ.A
  let extObjects := cwf.types.flatMap fun (ctx, tys) =>
    tys.map fun ty =>
      let name : Name := .nested ctx.name ty.name.toString
      ({ id := { name, kind := .sort }
         description := s!"Context extension {ctx}.{ty}" } : Generator0)

  -- Projection morphisms: p_A : Γ.A → Γ for each extension
  let projections := cwf.types.flatMap fun (ctx, tys) =>
    tys.map fun ty =>
      let extName : Name := .nested ctx.name ty.name.toString
      let projName : Name := .nested extName "p"
      ({ id := { name := projName, kind := .morphism }
         domain := .atom { name := extName, kind := .sort }
         codomain := .atom ctx
         description := s!"Projection p : {ctx}.{ty} → {ctx}" } : Generator1)

  -- Generic term morphisms: q_A : Γ.A → Ty(A)[p] for each extension
  -- q represents the "last variable" in the extended context
  let genericTerms := cwf.types.flatMap fun (ctx, tys) =>
    tys.map fun ty =>
      let extName : Name := .nested ctx.name ty.name.toString
      let qName : Name := .nested extName "q"
      ({ id := { name := qName, kind := .morphism }
         domain := .atom { name := extName, kind := .sort }
         codomain := .app (.atom ty) (.atom { name := .nested extName "p", kind := .morphism })
         description := s!"Generic term q : {ctx}.{ty} → {ty}[p]" } : Generator1)

  -- Universal property: for any σ : Δ → Γ and term a : Tm(A[σ]),
  -- there exists a unique ⟨σ, a⟩ : Δ → Γ.A such that p ∘ ⟨σ,a⟩ = σ and q ∘ ⟨σ,a⟩ = a
  -- We express the two equations as axiom schemas.
  let projAxioms := cwf.types.flatMap fun (ctx, tys) =>
    tys.map fun ty =>
      let extName : Name := .nested ctx.name ty.name.toString
      let projName : Name := .nested extName "p"
      let pairName : Name := .nested extName "extend"
      ({ id := { name := .nested extName "p_beta", kind := .twoCell }
         quantifiers :=
           [ { name := "Δ", kind := .sort }
           , { name := "σ", kind := .morphism
               domain := some (.var "Δ")
               codomain := some (.atom ctx) }
           , { name := "a", kind := .morphism
               domain := some (.var "Δ")
               codomain := none } ]
         leftPath := .comp
           (.atom { name := pairName, kind := .morphism })
           (.atom { name := projName, kind := .morphism })
         rightPath := .var "σ"
         description := s!"β-law: p ∘ ⟨σ,a⟩ = σ" } : Generator2)

  let termAxioms := cwf.types.flatMap fun (ctx, tys) =>
    tys.map fun ty =>
      let extName : Name := .nested ctx.name ty.name.toString
      let qName : Name := .nested extName "q"
      let pairName : Name := .nested extName "extend"
      ({ id := { name := .nested extName "q_beta", kind := .twoCell }
         quantifiers :=
           [ { name := "Δ", kind := .sort }
           , { name := "σ", kind := .morphism
               domain := some (.var "Δ")
               codomain := some (.atom ctx) }
           , { name := "a", kind := .morphism
               domain := some (.var "Δ")
               codomain := none } ]
         leftPath := .comp
           (.atom { name := pairName, kind := .morphism })
           (.atom { name := qName, kind := .morphism })
         rightPath := .var "a"
         description := s!"β-law: q ∘ ⟨σ,a⟩ = a" } : Generator2)

  -- η-law: ⟨p, q⟩ = id on Γ.A
  let etaAxioms := cwf.types.flatMap fun (ctx, tys) =>
    tys.map fun ty =>
      let extName : Name := .nested ctx.name ty.name.toString
      let pairName : Name := .nested extName "extend"
      ({ id := { name := .nested extName "eta", kind := .twoCell }
         leftPath := .atom { name := pairName, kind := .morphism }
         rightPath := .id (.atom { name := extName, kind := .sort })
         description := s!"η-law: ⟨p,q⟩ = id on {ctx}.{ty}" } : Generator2)

  { name := s!"CwF({base.name})"
    doctrine := base.doctrine
    objects := base.objects ++ extObjects
    morphisms := base.morphisms ++ projections ++ genericTerms
    axioms := base.axioms ++ projAxioms ++ termAxioms ++ etaAxioms }

end CatLab
