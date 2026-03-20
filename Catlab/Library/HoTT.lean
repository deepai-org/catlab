/-
  CatLab -- Homotopy Type Theory (HoTT)

  NOTE: This is a strictified 1-categorical presentation of HoTT's syntactic
  signature. It captures the generators and equations of the type theory but
  does NOT model the semantic ∞-topos or its homotopy-coherent structure.
  Operators like `pushout` compute strict colimits, not homotopy pushouts.

  Represented as a Category with Families (CwF), following Hofmann–Streicher.
  The three sorts are:
    Ctx  — contexts (the "base" category)
    Ty   — types dependent on a context (a presheaf over Ctx)
    Tm   — terms of a type in a context (sections of the type presheaf)

  Additional structure:
    - Context extension (Γ, x:A)
    - Identity types Id_A(x, y) with reflexivity
    - Dependent products Π(A, B) with λ-abstraction and application
    - A univalent universe U with El : Tm → Ty (decoding)

  The Univalence Axiom is stated as the axiom that the canonical map
  (A = B) → Equiv(A, B) is itself an equivalence; here we encode its
  signature: ua : Equiv → Id_U, which sections the transport map.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfHoTT : Theory :=
  let Ctx := Expr.atom (gid "Ctx")
  let Ty  := Expr.atom (gid "Ty")
  let Tm  := Expr.atom (gid "Tm")
  { name     := "HomotopyTypeTheory"
    doctrine := { doctrine := .MartinLofTypeTheory, strictified := true }
    objects  := [
      { id := gid "Ctx", description := "Contexts" },
      { id := gid "Ty",  description := "Types (dependent on a context)" },
      { id := gid "Tm",  description := "Terms (dependent on a type)" }
    ]
    morphisms := [

      -- ── Context Structure ───────────────────────────────────────────
      -- Empty context: ◇ : 1 → Ctx
      { id := gid "empty_ctx", domain := .terminal, codomain := Ctx,
        description := "Empty context ◇ : 1 → Ctx" },

      -- Context extension: Γ.A = (Γ, x:A): Ctx × Ty → Ctx
      { id := gid "ctx_ext", domain := .prod Ctx Ty, codomain := Ctx,
        description := "Context extension (Γ, x:A) : Ctx × Ty → Ctx" },

      -- Weakening projection: p : Γ.A → Γ  (forget the last variable)
      { id := gid "wk", domain := .prod Ctx Ty, codomain := Ctx,
        description := "Weakening projection p : (Γ.A) → Γ" },

      -- ── Typing Projections ──────────────────────────────────────────
      -- ty_ctx: each type lives over a context: Ty → Ctx
      { id := gid "ty_ctx", domain := Ty, codomain := Ctx,
        description := "Context of a type: Ty → Ctx" },

      -- tm_ty: each term has a type: Tm → Ty
      { id := gid "tm_ty", domain := Tm, codomain := Ty,
        description := "Type of a term: Tm → Ty" },

      -- Variable: the last variable in the extended context: q : Γ.A → A
      { id := gid "var", domain := .prod Ctx Ty, codomain := Tm,
        description := "Generic variable q : Γ.A → A[p]" },

      -- ── Substitution ────────────────────────────────────────────────
      -- Type substitution: Ty × Ctx → Ty  (A[σ] given A:Ty over Δ, σ:Γ→Δ)
      { id := gid "ty_subst", domain := .prod Ty Ctx, codomain := Ty,
        description := "Type substitution A[σ] : Ty × Ctx → Ty" },

      -- Term substitution: Tm × Ctx → Tm
      { id := gid "tm_subst", domain := .prod Tm Ctx, codomain := Tm,
        description := "Term substitution t[σ] : Tm × Ctx → Tm" },

      -- ── Identity Types ──────────────────────────────────────────────
      -- Id_A(x, y): Ty × Tm × Tm → Ty
      { id := gid "Id_ty", domain := .prod Ty (.prod Tm Tm), codomain := Ty,
        description := "Identity type Id_A(x,y) : Ty × Tm × Tm → Ty" },

      -- refl : Tm → Tm  (reflexivity proof: refl(x) : Id_A(x,x))
      { id := gid "refl", domain := Tm, codomain := Tm,
        description := "Reflexivity: refl(x) : Id_A(x, x)" },

      -- J eliminator (path induction): given a motive and base case,
      -- produces a term over all identity proofs
      { id := gid "J_elim", domain := .prod Tm Tm, codomain := Tm,
        description := "J eliminator (path induction)" },

      -- ── Π Types ─────────────────────────────────────────────────────
      -- Π(A, B): Ty × Ty → Ty  (dependent product)
      { id := gid "Pi_ty", domain := .prod Ty Ty, codomain := Ty,
        description := "Dependent product Π(A, B) : Ty × Ty → Ty" },

      -- λ-abstraction: Tm → Tm  (given t : B[x], produce λx.t : Π(A,B))
      { id := gid "lam", domain := Tm, codomain := Tm,
        description := "Lambda abstraction λx.t : Tm → Tm" },

      -- Application: Tm × Tm → Tm  (apply function to argument)
      { id := gid "app", domain := .prod Tm Tm, codomain := Tm,
        description := "Application: Tm × Tm → Tm" },

      -- ── Universe (Univalence) ────────────────────────────────────────
      -- U : Ctx → Ty  (the univalent universe in each context)
      { id := gid "U", domain := Ctx, codomain := Ty,
        description := "Univalent universe U(Γ) : Ctx → Ty" },

      -- El : Tm → Ty  (decode a universe element to a type)
      { id := gid "El", domain := Tm, codomain := Ty,
        description := "El(a) : Tm → Ty  (decode universe element)" },

      -- ua : Tm → Tm  (univalence: equivalences give identity proofs)
      { id := gid "ua", domain := Tm, codomain := Tm,
        description := "Univalence map: ua(e) : Equiv(A,B) → Id_U(A,B)" }
    ]
    axioms := [

      -- ── CwF coherence ───────────────────────────────────────────────
      -- ty_ctx(A[σ]) = ctx of σ  (substitution respects contexts)
      { id := gid "subst_ctx"
        leftPath  := .comp (.atom (gid "ty_subst")) (.atom (gid "ty_ctx"))
        rightPath := .id Ctx
        description := "ty_ctx(A[σ]) = dom(σ)" },

      -- tm_ty(t[σ]) = (tm_ty t)[σ]  (substitution respects typing)
      { id := gid "subst_ty"
        leftPath  := .comp (.atom (gid "tm_subst")) (.atom (gid "tm_ty"))
        rightPath := .comp (.prod (.atom (gid "tm_ty")) (.id Ctx)) (.atom (gid "ty_subst"))
        description := "ty(t[σ]) = (ty t)[σ]" },

      -- ── Identity type axioms ────────────────────────────────────────
      -- refl is well-typed: tm_ty(refl(x)) lies over Id_A(x,x)
      { id := gid "refl_ty"
        leftPath  := .comp (.atom (gid "refl")) (.atom (gid "tm_ty"))
        rightPath := .comp (.atom (gid "Id_ty")) (.atom (gid "ty_ctx"))
        description := "ty(refl x) lies over Id_A(x,x)" },

      -- J computation: J(C, d, refl(x)) = d
      { id := gid "J_beta"
        leftPath  := .comp (.prod (.atom (gid "refl")) (.id Tm)) (.atom (gid "J_elim"))
        rightPath := .id Tm
        description := "J(C, d, refl x) = d  (J-β rule)" },

      -- ── Π type axioms ───────────────────────────────────────────────
      -- β rule: app(lam(t), a) = t[a]
      { id := gid "pi_beta"
        leftPath  := .comp (.prod (.atom (gid "lam")) (.id Tm)) (.atom (gid "app"))
        rightPath := .id Tm
        description := "β-rule: app(λx.t, a) = t[a/x]" },

      -- η rule: lam(app(f, var)) = f
      { id := gid "pi_eta"
        leftPath  := .comp (.atom (gid "app")) (.atom (gid "lam"))
        rightPath := .id Tm
        description := "η-rule: λx. f x = f" },

      -- ── Univalence ──────────────────────────────────────────────────
      -- ua is a section of transport: transport(ua(e)) = e
      { id := gid "ua_section"
        leftPath  := .comp (.prod (.atom (gid "ua")) (.id Tm)) (.atom (gid "J_elim"))
        rightPath := .id Tm
        description := "Univalence: ua is a section of the transport map" }
    ] }

end CatLab.Library
