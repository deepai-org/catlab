/-
  CatLab -- Locales (Pointless Topology / Frames)

  A locale is a frame viewed "from the wrong side":
    - A frame is a complete lattice  (L, ≤, ⊤, ⊥, ∧, ⋁)  satisfying
      the infinite distributive law:  a ∧ (⋁ S) = ⋁ {a ∧ s | s ∈ S}
    - A locale is the opposite of a frame  (frame morphisms go the other way)
    - Frame morphisms preserve ⊤, ∧, and arbitrary ⋁ (but not necessarily ⊥ or finite ⋁)
    - A locale morphism = a frame morphism in the opposite direction

  The category of locales is equivalent to the category of sober topological
  spaces when restricted to spatial locales.  Every topological space gives a
  locale via its frame of open sets.

  Examples:
    - Open sets of any topological space
    - Spectrum of a ring
    - Zariski locale, étale locale

  We represent a locale as a single-sorted algebra over the elements of the frame.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfLocale : Theory :=
  let L := Expr.atom (gid "L")   -- elements of the frame
  { name     := "Locale"
    doctrine := { doctrine := .Locale }
    objects  := [
      { id := gid "L", description := "Elements of the frame / open sets" }
    ]
    morphisms := [
      -- ── Top and bottom ────────────────────────────────────────────────
      { id := gid "top", domain := .terminal, codomain := L,
        description := "Top element ⊤  (whole space)" },
      { id := gid "bot", domain := .terminal, codomain := L,
        description := "Bottom element ⊥  (empty open set)" },

      -- ── Binary meet ∧ ────────────────────────────────────────────────
      { id := gid "meet", domain := .prod L L, codomain := L,
        description := "Binary meet a ∧ b" },

      -- ── Binary join ∨ ────────────────────────────────────────────────
      { id := gid "join", domain := .prod L L, codomain := L,
        description := "Binary join a ∨ b" },

      -- ── Infinitary join ⋁ (the key frame axiom uses this) ─────────────
      { id := gid "inf_join", domain := L, codomain := L,
        description := "Infinitary join ⋁S (takes a 'diagram' of opens)" },

      -- ── Ordering: a ≤ b iff a = a ∧ b (encoded as subobject) ─────────
      { id := gid "leq", domain := .prod L L, codomain := L,
        description := "Order relation: a ≤ b  (a = a ∧ b)" },

      -- ── Frame morphism (locale morphism in the opposite direction) ─────
      -- A frame morphism f : L₁ → L₂ preserves ⊤, ∧, ⋁
      { id := gid "frame_map", domain := L, codomain := L,
        description := "Frame morphism f : L → L  (self-map for endomorphisms)" },

      -- ── Pseudo-complement (Heyting implication) ──────────────────────
      -- a → b = ⋁{c | c ∧ a ≤ b}  (makes L a complete Heyting algebra)
      { id := gid "heyting_impl", domain := .prod L L, codomain := L,
        description := "Heyting implication a ⇒ b (pseudo-complement)" },

      -- ── Negation: ¬a = a ⇒ ⊥ ────────────────────────────────────────
      { id := gid "neg", domain := L, codomain := L,
        description := "Pseudo-complement ¬a = a ⇒ ⊥" }
    ]
    axioms := [
      -- ── Meet is commutative ───────────────────────────────────────────
      { id := gid "meet_comm"
        leftPath  := .comp (.prod (.id L) (.id L)) (.atom (gid "meet"))
        rightPath := .comp (.prod (.id L) (.id L)) (.atom (gid "meet"))
        description := "a ∧ b = b ∧ a" },

      -- ── Meet is associative ───────────────────────────────────────────
      { id := gid "meet_assoc"
        leftPath  := .comp (.prod (.atom (gid "meet")) (.id L)) (.atom (gid "meet"))
        rightPath := .comp (.prod (.id L) (.atom (gid "meet"))) (.atom (gid "meet"))
        description := "(a ∧ b) ∧ c = a ∧ (b ∧ c)" },

      -- ── ⊤ is unit for ∧ ──────────────────────────────────────────────
      { id := gid "meet_top"
        leftPath  := .comp (.prod (.atom (gid "top")) (.id L)) (.atom (gid "meet"))
        rightPath := .id L
        description := "⊤ ∧ a = a" },

      -- ── Join is commutative ───────────────────────────────────────────
      { id := gid "join_comm"
        leftPath  := .comp (.prod (.id L) (.id L)) (.atom (gid "join"))
        rightPath := .comp (.prod (.id L) (.id L)) (.atom (gid "join"))
        description := "a ∨ b = b ∨ a" },

      -- ── Join is associative ───────────────────────────────────────────
      { id := gid "join_assoc"
        leftPath  := .comp (.prod (.atom (gid "join")) (.id L)) (.atom (gid "join"))
        rightPath := .comp (.prod (.id L) (.atom (gid "join"))) (.atom (gid "join"))
        description := "(a ∨ b) ∨ c = a ∨ (b ∨ c)" },

      -- ── ⊥ is unit for ∨ ──────────────────────────────────────────────
      { id := gid "join_bot"
        leftPath  := .comp (.prod (.atom (gid "bot")) (.id L)) (.atom (gid "join"))
        rightPath := .id L
        description := "⊥ ∨ a = a" },

      -- ── Absorption: a ∧ (a ∨ b) = a ─────────────────────────────────
      { id := gid "absorb_meet"
        leftPath  := .comp (.prod (.id L) (.atom (gid "join"))) (.atom (gid "meet"))
        rightPath := .id L
        description := "a ∧ (a ∨ b) = a  (absorption)" },

      -- ── Frame distributivity: a ∧ ⋁S = ⋁{a ∧ s | s ∈ S} ───────────
      { id := gid "frame_distrib"
        leftPath  := .comp (.atom (gid "inf_join")) (.atom (gid "meet"))
        rightPath := .comp (.atom (gid "meet")) (.atom (gid "inf_join"))
        description := "a ∧ ⋁S = ⋁{a ∧ s | s ∈ S}  (frame distributivity)" },

      -- ── Heyting implication adjunction: a ∧ b ≤ c ↔ a ≤ b ⇒ c ───────
      { id := gid "heyting_adj"
        leftPath  := .comp (.atom (gid "heyting_impl")) (.atom (gid "meet"))
        rightPath := .comp (.atom (gid "meet")) (.atom (gid "leq"))
        description := "a ∧ (a⇒b) ≤ b  (adjunction counit)" }
    ] }

end CatLab.Library
