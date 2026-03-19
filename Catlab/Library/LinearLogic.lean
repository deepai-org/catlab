/-
  CatLab -- Linear Logic / Linear Type Theory (Girard 1987)

  Linear logic tracks resource usage: each hypothesis must be used
  exactly once.  The connectives split into two dual groups:

  Multiplicative (⊗ / ⅋, units 1 / ⊥):
    A ⊗ B  — "both A and B, used separately"
    A ⅋ B  — "A par B" (co-product of the dual / classical disjunction)
    1      — unit for ⊗
    ⊥      — unit for ⅋

  Additive (& / ⊕, units ⊤ / 0):
    A & B  — "with" (internal choice: client picks one)
    A ⊕ B  — "plus" (external choice: server picks one)
    ⊤      — unit for &  (always succeeds)
    0      — unit for ⊕  (always fails)

  Exponentials (! / ?):
    !A     — "of course A" (reusable / classical assumption)
    ?A     — "why not A"   (dually)

  Linear negation (−)^⊥:
    A^⊥    — the linear dual of A (involution: (A^⊥)^⊥ = A)

  Categorically this is modelled as a *-autonomous category with
  monoidal products ⊗ and ⅋.  We represent the single-sorted
  "propositions as objects" view.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfLinearLogic : Theory :=
  let LProp := Expr.atom (gid "LProp")  -- propositions / types
  let Proof := Expr.atom (gid "Proof") -- proofs / terms (morphisms in the *-aut. cat)
  { name     := "LinearLogic"
    doctrine := { doctrine := .LinearLogic }
    objects  := [
      { id := gid "LProp",  description := "Propositions (objects of the *-autonomous category)" },
      { id := gid "Proof", description := "Proof terms (morphisms)" }
    ]
    morphisms := [
      -- ── Proof structure ───────────────────────────────────────────────
      { id := gid "hyp",  domain := Proof, codomain := LProp,
        description := "Hypothesis (source proposition) of a proof" },
      { id := gid "conc", domain := Proof, codomain := LProp,
        description := "Conclusion (target proposition) of a proof" },
      { id := gid "id_proof", domain := LProp, codomain := Proof,
        description := "Identity proof (axiom): A ⊢ A" },
      { id := gid "cut", domain := .prod Proof Proof, codomain := Proof,
        description := "Cut rule: compose proofs" },

      -- ── Multiplicatives ───────────────────────────────────────────────
      { id := gid "tensor",    domain := .prod LProp LProp, codomain := LProp,
        description := "Tensor product A ⊗ B" },
      { id := gid "par",       domain := .prod LProp LProp, codomain := LProp,
        description := "Par A ⅋ B" },
      { id := gid "one",       domain := .terminal, codomain := LProp,
        description := "Multiplicative unit 1" },
      { id := gid "bot",       domain := .terminal, codomain := LProp,
        description := "Multiplicative counit ⊥" },

      -- Tensor introduction and elimination
      { id := gid "tensor_intro", domain := .prod Proof Proof, codomain := Proof,
        description := "Tensor intro: f ⊗ g : A⊗B ⊢ C⊗D" },
      { id := gid "tensor_elim",  domain := Proof, codomain := Proof,
        description := "Tensor elim: A⊗B ⊢ C  (use both)" },

      -- ── Additives ────────────────────────────────────────────────────
      { id := gid "with_ty",   domain := .prod LProp LProp, codomain := LProp,
        description := "With A & B  (additive conjunction)" },
      { id := gid "plus_ty",   domain := .prod LProp LProp, codomain := LProp,
        description := "Plus A ⊕ B  (additive disjunction)" },
      { id := gid "top_prop",  domain := .terminal, codomain := LProp,
        description := "Additive unit ⊤" },
      { id := gid "zero_prop", domain := .terminal, codomain := LProp,
        description := "Additive zero 0" },

      -- With projections
      { id := gid "with_fst", domain := Proof, codomain := Proof,
        description := "Left projection: A & B ⊢ A" },
      { id := gid "with_snd", domain := Proof, codomain := Proof,
        description := "Right projection: A & B ⊢ B" },

      -- Plus injections
      { id := gid "plus_inl", domain := Proof, codomain := Proof,
        description := "Left injection: A ⊢ A ⊕ B" },
      { id := gid "plus_inr", domain := Proof, codomain := Proof,
        description := "Right injection: B ⊢ A ⊕ B" },

      -- ── Exponentials ─────────────────────────────────────────────────
      { id := gid "bang",  domain := LProp, codomain := LProp,
        description := "!A  (of course A — reusable resource)" },
      { id := gid "quest", domain := LProp, codomain := LProp,
        description := "?A  (why not A — classical dual)" },

      -- Dereliction: !A ⊢ A  (use once)
      { id := gid "derelict",   domain := Proof, codomain := Proof,
        description := "Dereliction: !A ⊢ A" },
      -- Contraction: !A ⊢ !A ⊗ !A  (duplicate)
      { id := gid "contract",   domain := Proof, codomain := Proof,
        description := "Contraction: !A ⊢ !A ⊗ !A" },
      -- Weakening: !A ⊢ 1  (discard)
      { id := gid "weaken",     domain := Proof, codomain := Proof,
        description := "Weakening: !A ⊢ 1" },
      -- Promotion: !Γ ⊢ A  implies  !Γ ⊢ !A
      { id := gid "promote",    domain := Proof, codomain := Proof,
        description := "Promotion: under !-context, A becomes !A" },

      -- ── Linear negation ───────────────────────────────────────────────
      { id := gid "lneg",  domain := LProp, codomain := LProp,
        description := "Linear negation A^⊥" },

      -- ── Exchange / structural maps ────────────────────────────────────
      { id := gid "exchange", domain := Proof, codomain := Proof,
        description := "Exchange: A ⊗ B ⊢ B ⊗ A  (symmetry of ⊗)" }
    ]
    axioms := [
      -- ── Linear negation is involutive ─────────────────────────────────
      { id := gid "neg_invol"
        leftPath  := .comp (.atom (gid "lneg")) (.atom (gid "lneg"))
        rightPath := .id LProp
        description := "(A^⊥)^⊥ = A" },

      -- ── De Morgan: (A ⊗ B)^⊥ = A^⊥ ⅋ B^⊥ ───────────────────────────
      { id := gid "de_morgan_tensor"
        leftPath  := .comp (.atom (gid "tensor")) (.atom (gid "lneg"))
        rightPath := .comp (.prod (.atom (gid "lneg")) (.atom (gid "lneg")))
                           (.atom (gid "par"))
        description := "(A ⊗ B)^⊥ = A^⊥ ⅋ B^⊥" },

      -- ── Cut elimination (identity): cut with id = id ──────────────────
      { id := gid "cut_id"
        leftPath  := .comp (.prod (.atom (gid "id_proof")) (.id Proof))
                           (.atom (gid "cut"))
        rightPath := .id Proof
        description := "cut(id_A, f) = f" },

      -- ── Associativity of tensor ───────────────────────────────────────
      { id := gid "tensor_assoc"
        leftPath  := .comp (.prod (.atom (gid "tensor")) (.id LProp)) (.atom (gid "tensor"))
        rightPath := .comp (.prod (.id LProp) (.atom (gid "tensor"))) (.atom (gid "tensor"))
        description := "(A ⊗ B) ⊗ C = A ⊗ (B ⊗ C)" },

      -- ── Unit law: 1 ⊗ A = A ──────────────────────────────────────────
      { id := gid "tensor_unit_left"
        leftPath  := .comp (.prod (.atom (gid "one")) (.id LProp)) (.atom (gid "tensor"))
        rightPath := .id LProp
        description := "1 ⊗ A = A" },

      -- ── Dereliction: derelict is a natural transformation !A → A ──────
      { id := gid "derelict_nat"
        leftPath  := .comp (.atom (gid "derelict")) (.atom (gid "conc"))
        rightPath := .comp (.atom (gid "bang")) (.id LProp)
        description := "conc(derelict f) = A  when f : !A ⊢ ..." },

      -- ── Exchange is its own inverse ────────────────────────────────────
      { id := gid "exchange_invol"
        leftPath  := .comp (.atom (gid "exchange")) (.atom (gid "exchange"))
        rightPath := .id Proof
        description := "exchange ∘ exchange = id" }
    ] }

end CatLab.Library
