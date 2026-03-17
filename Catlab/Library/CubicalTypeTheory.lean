/-
  CatLab -- Cubical Type Theory (CTT / CCTT)

  Cubical type theory (Cohen–Coquand–Huber–Mörtberg, 2016) reformulates
  HoTT using the interval  I = [0,1]  as a primitive.  This avoids the
  axiom-of-choice flavour of the univalence axiom and gives a computational
  interpretation.

  Key additions over ordinary type theory:
    I    — the abstract interval type (with 0, 1 : I)
    Path A  — the path type  (x = y : A)  is  I → A  (or (i : I) → A i)
    Partial types  — A [φ]  (A restricted to a face φ ⊆ ∂I^n)
    Kan composition  — filling a partial n-cube to a full cube
    Connections  — meet (∧) and join (∨) on I
    Coercion  — transport across a type path

  We represent the typing / context structure in CwF style as for HoTT,
  extended with the interval and path operations.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfCubicalTypeTheory : Theory :=
  let Ctx := Expr.atom (gid "Ctx")
  let Ty  := Expr.atom (gid "Ty")
  let Tm  := Expr.atom (gid "Tm")
  let I   := Expr.atom (gid "I")    -- the interval
  { name     := "CubicalTypeTheory"
    doctrine := { doctrine := .CubicalTypeTheory }
    objects  := [
      { id := gid "Ctx", description := "Contexts (may include interval variables)" },
      { id := gid "Ty",  description := "Types in a context" },
      { id := gid "Tm",  description := "Terms of a type" },
      { id := gid "I",   description := "The abstract interval [0,1]" }
    ]
    morphisms := [
      -- ── CwF context structure (inherited) ────────────────────────────
      { id := gid "ty_ctx",   domain := Ty, codomain := Ctx,
        description := "Context of a type" },
      { id := gid "tm_ty",    domain := Tm, codomain := Ty,
        description := "Type of a term" },
      { id := gid "empty_ctx", domain := .terminal, codomain := Ctx,
        description := "Empty context" },
      { id := gid "ctx_ext",  domain := .prod Ctx Ty, codomain := Ctx,
        description := "Context extension Γ, x:A" },
      { id := gid "wk",       domain := .prod Ctx Ty, codomain := Ctx,
        description := "Weakening projection" },
      { id := gid "var",      domain := .prod Ctx Ty, codomain := Tm,
        description := "Generic variable" },

      -- ── Interval endpoints ────────────────────────────────────────────
      { id := gid "i0", domain := Ctx, codomain := I,
        description := "Left endpoint  0 : I  in context Γ" },
      { id := gid "i1", domain := Ctx, codomain := I,
        description := "Right endpoint 1 : I  in context Γ" },

      -- ── Interval context extension: Γ, i:I ───────────────────────────
      { id := gid "ctx_ext_I", domain := Ctx, codomain := Ctx,
        description := "Interval extension: Γ ↦ Γ, i:I" },

      -- ── Connections: binary meet ∧ and join ∨ on I ───────────────────
      { id := gid "meet_I", domain := .prod I I, codomain := I,
        description := "Connection meet: i ∧ j : I" },
      { id := gid "join_I", domain := .prod I I, codomain := I,
        description := "Connection join: i ∨ j : I" },
      { id := gid "sym_I",  domain := I, codomain := I,
        description := "Symmetry (flip): 1 - i : I" },

      -- ── Path type: Path A x y  =  (i : I) → A  with  r(0)=x, r(1)=y ─
      { id := gid "Path_ty", domain := .prod Ty (.prod Tm Tm), codomain := Ty,
        description := "Path type Path_A(x,y) : Ty × Tm × Tm → Ty" },

      -- ── Path introduction: λi.t (abstraction over i : I) ─────────────
      { id := gid "path_lam", domain := Tm, codomain := Tm,
        description := "Path abstraction λi. t" },

      -- ── Path application: p @ i ──────────────────────────────────────
      { id := gid "path_app", domain := .prod Tm I, codomain := Tm,
        description := "Path application p @ i : Tm × I → Tm" },

      -- ── Reflexivity: refl_x = λi. x ──────────────────────────────────
      { id := gid "refl", domain := Tm, codomain := Tm,
        description := "Reflexivity refl(x) = λi. x" },

      -- ── Coercion (transport along a path of types) ────────────────────
      { id := gid "coe", domain := .prod Ty Tm, codomain := Tm,
        description := "Coercion: coe_{i.A}(r, t) transports t from A(0) to A(1)" },

      -- ── Kan composition (filling a partial open box) ──────────────────
      { id := gid "hcomp", domain := .prod Ty Tm, codomain := Tm,
        description := "Homogeneous composition: fill a partial square" },

      -- ── Substitution ─────────────────────────────────────────────────
      { id := gid "ty_subst", domain := .prod Ty Ctx, codomain := Ty,
        description := "Type substitution A[σ]" },
      { id := gid "tm_subst", domain := .prod Tm Ctx, codomain := Tm,
        description := "Term substitution t[σ]" },
      { id := gid "I_subst",  domain := .prod I Ctx, codomain := I,
        description := "Interval substitution i[σ]" }
    ]
    axioms := [
      -- ── Endpoint reduction ────────────────────────────────────────────
      { id := gid "path_app_0"
        leftPath  := .comp (.atom (gid "refl")) (.atom (gid "path_app"))
        rightPath := .comp (.atom (gid "i0")) (.atom (gid "tm_ty"))
        description := "(λi. x) @ 0 = x  (left endpoint)" },

      { id := gid "path_app_1"
        leftPath  := .comp (.atom (gid "refl")) (.atom (gid "path_app"))
        rightPath := .comp (.atom (gid "i1")) (.atom (gid "tm_ty"))
        description := "(λi. x) @ 1 = x  (right endpoint)" },

      -- ── β-rule for path abstraction ───────────────────────────────────
      { id := gid "path_beta"
        leftPath  := .comp (.atom (gid "path_lam")) (.atom (gid "path_app"))
        rightPath := .id Tm
        description := "(λi. t) @ i = t  (path β-rule)" },

      -- ── η-rule: p = λi. p @ i ─────────────────────────────────────────
      { id := gid "path_eta"
        leftPath  := .comp (.atom (gid "path_app")) (.atom (gid "path_lam"))
        rightPath := .id Tm
        description := "λi. (p @ i) = p  (path η-rule)" },

      -- ── Coercion at 0 is identity ─────────────────────────────────────
      { id := gid "coe_refl"
        leftPath  := .comp (.atom (gid "coe")) (.atom (gid "tm_ty"))
        rightPath := .id Tm
        description := "coe along constant path = identity" },

      -- ── Connection meet: i ∧ 0 = 0 ───────────────────────────────────
      { id := gid "meet_zero"
        leftPath  := .comp (.prod (.id I) (.atom (gid "i0"))) (.atom (gid "meet_I"))
        rightPath := .atom (gid "i0")
        description := "i ∧ 0 = 0" },

      -- ── Connection join: i ∨ 1 = 1 ───────────────────────────────────
      { id := gid "join_one"
        leftPath  := .comp (.prod (.id I) (.atom (gid "i1"))) (.atom (gid "join_I"))
        rightPath := .atom (gid "i1")
        description := "i ∨ 1 = 1" },

      -- ── Symmetry is involutive: sym(sym(i)) = i ───────────────────────
      { id := gid "sym_invol"
        leftPath  := .comp (.atom (gid "sym_I")) (.atom (gid "sym_I"))
        rightPath := .id I
        description := "1 - (1 - i) = i" }
    ] }

end CatLab.Library
