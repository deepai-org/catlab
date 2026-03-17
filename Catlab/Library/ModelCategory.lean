/-
  CatLab -- Quillen Model Category

  A model category is a category C equipped with three distinguished classes
  of morphisms: weak equivalences W, cofibrations Cof, and fibrations Fib,
  satisfying Quillen's axioms M1–M5:
    M1. C has all finite limits and colimits.
    M2. Two-out-of-three: if two of {f, g, g∘f} ∈ W, so is the third.
    M3. W, Cof, Fib are closed under retracts.
    M4. Lifting: acyclic cofibrations (Cof ∩ W) lift against fibrations;
        cofibrations lift against acyclic fibrations (Fib ∩ W).
    M5. Factorization: every map f = p ∘ i with i ∈ Cof ∩ W, p ∈ Fib,
        and also f = q ∘ j with j ∈ Cof, q ∈ Fib ∩ W.

  The three classes are represented as sub-sorts of Mor with inclusion maps.
  Factorization is represented by functorial factorization morphisms.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfModelCategory : Theory :=
  let Ob   := Expr.atom (gid "Ob")
  let Mor  := Expr.atom (gid "Mor")
  let WE   := Expr.atom (gid "WE")    -- weak equivalences
  let Cof  := Expr.atom (gid "Cof")   -- cofibrations
  let Fib  := Expr.atom (gid "Fib")   -- fibrations
  { name     := "ModelCategory"
    doctrine := { doctrine := .ModelCategory }
    objects  := [
      { id := gid "Ob",  description := "Objects" },
      { id := gid "Mor", description := "All morphisms" },
      { id := gid "WE",  description := "Weak equivalences (W)" },
      { id := gid "Cof", description := "Cofibrations" },
      { id := gid "Fib", description := "Fibrations" }
    ]
    morphisms := [
      -- ── Underlying category structure ────────────────────────────────
      { id := gid "src",  domain := Mor, codomain := Ob,
        description := "Source: Mor → Ob" },
      { id := gid "tgt",  domain := Mor, codomain := Ob,
        description := "Target: Mor → Ob" },
      { id := gid "ident", domain := Ob, codomain := Mor,
        description := "Identity: Ob → Mor" },
      { id := gid "comp",  domain := .prod Mor Mor, codomain := Mor,
        description := "Composition: Mor × Mor → Mor" },

      -- ── Inclusions of the three classes into Mor ─────────────────────
      { id := gid "we_incl",  domain := WE,  codomain := Mor,
        description := "Weak equivalences ↪ Mor" },
      { id := gid "cof_incl", domain := Cof, codomain := Mor,
        description := "Cofibrations ↪ Mor" },
      { id := gid "fib_incl", domain := Fib, codomain := Mor,
        description := "Fibrations ↪ Mor" },

      -- ── Identities are weak equivalences ─────────────────────────────
      { id := gid "id_is_we", domain := Ob, codomain := WE,
        description := "Every identity is a weak equivalence: Ob → WE" },

      -- ── Functorial factorization: f = p ∘ i (Cof∩W then Fib) ─────────
      { id := gid "fact_i", domain := Mor, codomain := Cof,
        description := "Factorization: left factor (acyclic cofibration)" },
      { id := gid "fact_p", domain := Mor, codomain := Fib,
        description := "Factorization: right factor (fibration)" },

      -- ── Functorial factorization: f = q ∘ j (Cof then Fib∩W) ─────────
      { id := gid "fact_j", domain := Mor, codomain := Cof,
        description := "Factorization: left factor (cofibration)" },
      { id := gid "fact_q", domain := Mor, codomain := Fib,
        description := "Factorization: right factor (acyclic fibration)" },

      -- ── Lifting: diagonal filler ─────────────────────────────────────
      { id := gid "lift", domain := .prod Cof Fib, codomain := Mor,
        description := "Lifting: diagonal filler for (acyclic Cof) ⊲ Fib" },

      -- ── Terminal and initial objects (M1) ─────────────────────────────
      { id := gid "terminal", domain := .terminal, codomain := Ob,
        description := "Terminal object" },
      { id := gid "initial",  domain := .terminal, codomain := Ob,
        description := "Initial object" },

      -- ── Cofibrant/fibrant replacement ─────────────────────────────────
      { id := gid "cofibrant_repl", domain := Ob, codomain := Ob,
        description := "Cofibrant replacement QX → X" },
      { id := gid "fibrant_repl",   domain := Ob, codomain := Ob,
        description := "Fibrant replacement X → RX" }
    ]
    axioms := [
      -- ── Two-out-of-three (M2): encoded for g ∘ f, g ─────────────────
      { id := gid "two_of_three"
        leftPath  := .comp (.atom (gid "we_incl")) (.atom (gid "comp"))
        rightPath := .comp (.atom (gid "comp")) (.atom (gid "we_incl"))
        description := "Two-out-of-three: W closed under composition" },

      -- ── Factorization coherence: tgt(i) = src(p) ────────────────────
      { id := gid "fact_coherence"
        leftPath  := .comp (.atom (gid "fact_i")) (.atom (gid "tgt"))
        rightPath := .comp (.atom (gid "fact_p")) (.atom (gid "src"))
        description := "Factorization: tgt(i) = src(p) (middle object)" },

      -- ── Identities are cofibrations ───────────────────────────────────
      { id := gid "id_is_cof"
        leftPath  := .comp (.atom (gid "ident")) (.atom (gid "src"))
        rightPath := .comp (.atom (gid "id_is_we")) (.atom (gid "we_incl"))
        description := "Identity inclusions are cofibrations" },

      -- ── Lifting: src and tgt compatibility ───────────────────────────
      { id := gid "lift_src"
        leftPath  := .comp (.atom (gid "lift")) (.atom (gid "src"))
        rightPath := .comp (.atom (gid "cof_incl")) (.atom (gid "src"))
        description := "Lift source matches cofibration source" },

      { id := gid "lift_tgt"
        leftPath  := .comp (.atom (gid "lift")) (.atom (gid "tgt"))
        rightPath := .comp (.atom (gid "fib_incl")) (.atom (gid "tgt"))
        description := "Lift target matches fibration target" }
    ] }

end CatLab.Library
