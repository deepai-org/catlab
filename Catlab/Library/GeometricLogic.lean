/-
  CatLab -- Geometric Logic

  Geometric logic is the fragment of first-order logic that is preserved by
  geometric morphisms between toposes (left exact left adjoints).  It is the
  logic of sheaves and classifying toposes.

  Geometric formulas are built from:
    ⊤   (truth)
    ∧   (finite conjunction)
    ∃   (existential quantification)
    ⊥   (falsehood — present in coherent logic)
    ∨   (finite disjunction — coherent level)
    ⋁ᵢ  (INFINITE disjunction — the strictly geometric extension)

  A geometric theory is a set of geometric sequents  φ ⊢_Γ ψ  where
  φ is coherent and ψ is geometric (may use the infinite disjunction).

  Categorically:  a geometric theory classifies a Grothendieck topos,
  and models are geometric morphisms from Set (or any base topos) into
  the classifying topos.

  Sorts: Ctx (contexts / variable lists), Form (formulas), Seq (sequents).
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfGeometricLogic : Theory :=
  let Ctx  := Expr.atom (gid "Ctx")
  let Form := Expr.atom (gid "Form")
  let Seq  := Expr.atom (gid "Seq")
  { name     := "GeometricLogic"
    doctrine := { doctrine := .GeometricLogic }
    objects  := [
      { id := gid "Ctx",  description := "Contexts (sorted variable lists)" },
      { id := gid "Form", description := "Geometric formulas" },
      { id := gid "Seq",  description := "Geometric sequents φ ⊢_Γ ψ" }
    ]
    morphisms := [
      -- ── Formula context ───────────────────────────────────────────────
      { id := gid "form_ctx", domain := Form, codomain := Ctx,
        description := "Free variables of a formula: Form → Ctx" },

      -- ── Logical connectives ───────────────────────────────────────────
      { id := gid "top",     domain := Ctx, codomain := Form,
        description := "Truth ⊤ in context Γ" },
      { id := gid "bot",     domain := Ctx, codomain := Form,
        description := "Falsehood ⊥ in context Γ" },
      { id := gid "meet",    domain := .prod Form Form, codomain := Form,
        description := "Conjunction φ ∧ ψ" },
      { id := gid "join",    domain := .prod Form Form, codomain := Form,
        description := "Disjunction φ ∨ ψ  (finite, coherent level)" },
      { id := gid "inf_join", domain := Form, codomain := Form,
        description := "Infinite disjunction ⋁ᵢ φᵢ  (geometric extension)" },
      { id := gid "exists",  domain := .prod Form Ctx, codomain := Form,
        description := "Existential quantification ∃x:A. φ" },

      -- ── Substitution (reindexing) ─────────────────────────────────────
      { id := gid "form_subst", domain := .prod Form Ctx, codomain := Form,
        description := "Formula substitution φ[σ] : Form × Ctx → Form" },

      -- ── Sequents ─────────────────────────────────────────────────────
      { id := gid "seq_ctx",  domain := Seq, codomain := Ctx,
        description := "Context of a sequent: Seq → Ctx" },
      { id := gid "seq_hyp",  domain := Seq, codomain := Form,
        description := "Hypothesis φ of sequent φ ⊢ ψ" },
      { id := gid "seq_conc", domain := Seq, codomain := Form,
        description := "Conclusion ψ of sequent φ ⊢ ψ" },

      -- ── Derivation rules as morphisms ─────────────────────────────────
      { id := gid "axiom_rule",  domain := Form, codomain := Seq,
        description := "Axiom: φ ⊢ φ" },
      { id := gid "cut_rule",    domain := .prod Seq Seq, codomain := Seq,
        description := "Cut: from φ⊢ψ and ψ⊢χ derive φ⊢χ" },
      { id := gid "meet_intro",  domain := .prod Seq Seq, codomain := Seq,
        description := "∧-introduction: φ⊢ψ and φ⊢χ give φ⊢ψ∧χ" },
      { id := gid "meet_elim_l", domain := Seq, codomain := Seq,
        description := "∧-elim left: φ∧ψ ⊢ φ" },
      { id := gid "meet_elim_r", domain := Seq, codomain := Seq,
        description := "∧-elim right: φ∧ψ ⊢ ψ" },
      { id := gid "join_intro_l", domain := Seq, codomain := Seq,
        description := "∨-intro left: φ ⊢ φ∨ψ" },
      { id := gid "join_intro_r", domain := Seq, codomain := Seq,
        description := "∨-intro right: ψ ⊢ φ∨ψ" },
      { id := gid "join_elim",   domain := .prod Seq (.prod Seq Seq), codomain := Seq,
        description := "∨-elim (case split)" },
      { id := gid "exists_intro", domain := .prod Seq Form, codomain := Seq,
        description := "∃-intro: φ[t/x] ⊢ ∃x.φ" },
      { id := gid "exists_elim",  domain := .prod Seq Seq, codomain := Seq,
        description := "∃-elim: ∃x.φ ⊢ ψ  (x not free in ψ)" },

      -- ── Geometric-specific: infinitary disjunction ───────────────────
      { id := gid "inf_intro",   domain := .prod Seq Form, codomain := Seq,
        description := "Infinitary ∨-intro: φᵢ ⊢ ⋁ᵢ φᵢ" },
      { id := gid "inf_elim",    domain := Seq, codomain := Seq,
        description := "Infinitary ∨-elim (universal property of colimit)" }
    ]
    axioms := [
      -- ── Reflexivity: φ ⊢ φ ───────────────────────────────────────────
      { id := gid "seq_refl"
        leftPath  := .comp (.atom (gid "axiom_rule")) (.atom (gid "seq_hyp"))
        rightPath := .comp (.atom (gid "axiom_rule")) (.atom (gid "seq_conc"))
        description := "Hypothesis = conclusion for the axiom rule" },

      -- ── Cut is transitive composition ─────────────────────────────────
      { id := gid "cut_trans"
        leftPath  := .comp (.prod (.atom (gid "cut_rule")) (.id Seq)) (.atom (gid "cut_rule"))
        rightPath := .comp (.prod (.id Seq) (.atom (gid "cut_rule"))) (.atom (gid "cut_rule"))
        description := "Cut is associative (transitivity)" },

      -- ── ∧ is commutative (up to derivable sequent) ───────────────────
      { id := gid "meet_comm"
        leftPath  := .comp (.atom (gid "meet")) (.atom (gid "form_ctx"))
        rightPath := .comp (.prod (.id Form) (.atom (gid "form_ctx")))
                           (.atom (gid "form_ctx"))
        description := "φ ∧ ψ and ψ ∧ φ have the same context" },

      -- ── ⊤ is the unit for ∧ ──────────────────────────────────────────
      { id := gid "meet_top"
        leftPath  := .comp (.prod (.atom (gid "top")) (.id Form)) (.atom (gid "meet"))
        rightPath := .id Form
        description := "⊤ ∧ φ = φ" },

      -- ── Frame distributivity: φ ∧ (⋁ᵢ ψᵢ) = ⋁ᵢ (φ ∧ ψᵢ) ─────────────
      { id := gid "frame_distrib"
        leftPath  := .comp (.atom (gid "inf_join")) (.atom (gid "meet"))
        rightPath := .comp (.atom (gid "meet")) (.atom (gid "inf_join"))
        description := "Geometric distributivity: φ ∧ ⋁ᵢψᵢ = ⋁ᵢ(φ∧ψᵢ)" },

      -- ── Frobenius (∃ distributes over ∧) ──────────────────────────────
      { id := gid "frobenius"
        leftPath  := .comp (.atom (gid "exists")) (.atom (gid "meet"))
        rightPath := .comp (.atom (gid "meet")) (.atom (gid "exists"))
        description := "Frobenius: ∃x.(φ∧ψ) = φ ∧ ∃x.ψ  (x not free in φ)" }
    ] }

end CatLab.Library
