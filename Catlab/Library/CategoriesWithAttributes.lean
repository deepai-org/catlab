/-
  CatLab -- Categories with Attributes (CwA)

  A CwA (Cartmell 1978, Pitts) is an alternative to Categories with Families
  for modelling dependent type theory.  It packages the type-theoretic
  structure as an attribute bundle rather than a presheaf of terms.

  Data:
    - A category  C  (contexts and context-morphisms / substitutions)
    - For each Γ ∈ C, a set  Attr(Γ)  of "attributes" / types
    - For each Γ ∈ C and  A ∈ Attr(Γ):
        * A comprehension object  Γ.A ∈ C
        * A projection  π_{Γ,A} : Γ.A → Γ
        * A generic attribute  q_{Γ,A} ∈ Attr(Γ.A)   (the "last variable")
    - For each substitution σ : Δ → Γ and A ∈ Attr(Γ):
        * A reindexed attribute  σ*(A) ∈ Attr(Δ)
        * A morphism  σ̄ : Δ.σ*(A) → Γ.A  over σ  (comprehension is natural)
  Axioms encode the pullback / universality property of comprehension.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfCategoriesWithAttributes : Theory :=
  let Ctx  := Expr.atom (gid "Ctx")   -- contexts
  let Sub  := Expr.atom (gid "Sub")   -- substitutions (context morphisms)
  let Attr := Expr.atom (gid "Attr")  -- attributes / types
  let Tm   := Expr.atom (gid "Tm")    -- terms (elements of attributes)
  { name     := "CategoriesWithAttributes"
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects  := [
      { id := gid "Ctx",  description := "Contexts" },
      { id := gid "Sub",  description := "Substitutions (context morphisms)" },
      { id := gid "Attr", description := "Attributes / types in a context" },
      { id := gid "Tm",   description := "Terms (elements of attributes)" }
    ]
    morphisms := [
      -- ── Category structure on contexts ────────────────────────────────
      { id := gid "dom",   domain := Sub, codomain := Ctx,
        description := "Domain of a substitution: Sub → Ctx" },
      { id := gid "cod",   domain := Sub, codomain := Ctx,
        description := "Codomain of a substitution: Sub → Ctx" },
      { id := gid "id_sub", domain := Ctx, codomain := Sub,
        description := "Identity substitution: Ctx → Sub" },
      { id := gid "comp_sub", domain := .prod Sub Sub, codomain := Sub,
        description := "Composition of substitutions" },

      -- ── Attribute projection: attributes live over a context ──────────
      { id := gid "attr_ctx", domain := Attr, codomain := Ctx,
        description := "The context of an attribute: Attr → Ctx" },

      -- ── Comprehension: Γ.A for each Γ and A ∈ Attr(Γ) ───────────────
      { id := gid "comp_ctx", domain := Attr, codomain := Ctx,
        description := "Comprehension context Γ.A : Attr → Ctx" },
      { id := gid "proj",     domain := Attr, codomain := Sub,
        description := "Projection π_{Γ,A} : Γ.A → Γ" },

      -- ── Generic term / last variable ─────────────────────────────────
      { id := gid "gen_tm", domain := Attr, codomain := Tm,
        description := "Generic attribute q_{Γ,A} ∈ Attr(Γ.A)" },

      -- ── Reindexing: σ*(A) for σ : Δ → Γ and A ∈ Attr(Γ) ────────────
      { id := gid "reindex", domain := .prod Attr Sub, codomain := Attr,
        description := "Reindexed attribute σ*(A) : Attr × Sub → Attr" },

      -- ── Lifted substitution: σ̄ : Δ.σ*(A) → Γ.A ─────────────────────
      { id := gid "lift_sub", domain := .prod Sub Attr, codomain := Sub,
        description := "Lifted substitution σ̄ over comprehension" },

      -- ── Pairing substitution: ⟨σ, t⟩ : Δ → Γ.A ─────────────────────
      { id := gid "pair_sub", domain := .prod Sub Tm, codomain := Sub,
        description := "Pairing substitution ⟨σ, t⟩ : Δ → Γ.A" },

      -- ── Term substitution ────────────────────────────────────────────
      { id := gid "tm_attr",  domain := Tm, codomain := Attr,
        description := "Type of a term: Tm → Attr" },
      { id := gid "tm_subst", domain := .prod Tm Sub, codomain := Tm,
        description := "Term substitution t[σ] : Tm × Sub → Tm" },

      -- ── Empty context ────────────────────────────────────────────────
      { id := gid "empty_ctx", domain := .terminal, codomain := Ctx,
        description := "Empty context ◇ : 1 → Ctx" }
    ]
    axioms := [
      -- ── Projection is the domain of the comprehension sub ─────────────
      { id := gid "proj_dom"
        leftPath  := .comp (.atom (gid "proj")) (.atom (gid "dom"))
        rightPath := .atom (gid "comp_ctx")
        description := "dom(π_{Γ,A}) = Γ.A" },

      { id := gid "proj_cod"
        leftPath  := .comp (.atom (gid "proj")) (.atom (gid "cod"))
        rightPath := .atom (gid "attr_ctx")
        description := "cod(π_{Γ,A}) = Γ" },

      -- ── Reindexing preserves context ──────────────────────────────────
      { id := gid "reindex_ctx"
        leftPath  := .comp (.atom (gid "reindex")) (.atom (gid "attr_ctx"))
        rightPath := .comp (.prod (.id Attr) (.atom (gid "dom"))) (.atom (gid "attr_ctx"))
        description := "attr_ctx(σ*(A)) = dom(σ)" },

      -- ── Pairing universality: π ∘ ⟨σ,t⟩ = σ ─────────────────────────
      { id := gid "pair_proj"
        leftPath  := .comp (.atom (gid "pair_sub")) (.atom (gid "proj"))
        rightPath := .comp (.prod (.id Sub) (.atom (gid "tm_attr"))) (.atom (gid "proj"))
        description := "π ∘ ⟨σ, t⟩ = σ" },

      -- ── Identity substitution is neutral ──────────────────────────────
      { id := gid "comp_sub_left_id"
        leftPath  := .comp (.prod (.atom (gid "id_sub")) (.id Sub)) (.atom (gid "comp_sub"))
        rightPath := .id Sub
        description := "id ∘ σ = σ" },

      { id := gid "comp_sub_right_id"
        leftPath  := .comp (.prod (.id Sub) (.atom (gid "id_sub"))) (.atom (gid "comp_sub"))
        rightPath := .id Sub
        description := "σ ∘ id = σ" }
    ] }

end CatLab.Library
