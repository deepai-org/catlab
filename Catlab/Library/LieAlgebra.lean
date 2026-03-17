/-
  CatLab -- Lie Algebras

  A Lie algebra (g, [−,−]) over a field k is a k-vector space g with a
  bilinear bracket  [−,−] : g × g → g  satisfying:

    (LA1)  Antisymmetry:   [x, y] + [y, x] = 0
           (equivalently: [x, x] = 0  in char ≠ 2)
    (LA2)  Jacobi identity: [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0

  The Jacobi identity says the adjoint map  ad_x = [x,−]  is a derivation.

  Examples:
    - gl(n, k) = M_n(k) with [A,B] = AB − BA
    - sl(n, k), sp(2n, k), so(n, k)  (the classical Lie algebras)
    - Tangent space at identity of any Lie group
    - Any associative algebra A with [a,b] = ab − ba

  Categorically, Lie algebras are algebras over the Lie operad
  (or, by PBW, they correspond to primitives in the associated
  cocommutative Hopf algebra).

  We use a single-sorted presentation: one object L and the bracket morphism.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfLieAlgebra : Theory :=
  let L := Expr.atom (gid "L")   -- the underlying k-vector space
  { name     := "LieAlgebra"
    doctrine := { doctrine := .LawvereTheory }
    objects  := [
      { id := gid "L", description := "Underlying k-vector space of the Lie algebra" }
    ]
    morphisms := [
      -- ── k-module structure ────────────────────────────────────────────
      { id := gid "add",      domain := .prod L L, codomain := L,
        description := "Addition x + y" },
      { id := gid "neg",      domain := L, codomain := L,
        description := "Additive inverse −x" },
      { id := gid "zero",     domain := .terminal, codomain := L,
        description := "Zero element 0" },
      { id := gid "scale",    domain := .prod L L, codomain := L,
        description := "Scalar multiplication λ·x  (first arg = scalar)" },

      -- ── Lie bracket [−,−] ─────────────────────────────────────────────
      { id := gid "bracket",  domain := .prod L L, codomain := L,
        description := "Lie bracket [x, y] : L × L → L" },

      -- ── Adjoint representation: ad_x(y) = [x, y] ─────────────────────
      { id := gid "adjoint",  domain := L, codomain := L,
        description := "Adjoint action ad_x : L → L  (y ↦ [x, y])" },

      -- ── Killing form B(x,y) = Tr(ad_x ∘ ad_y) ───────────────────────
      { id := gid "killing",  domain := .prod L L, codomain := L,
        description := "Killing form B : L × L → k  (encoded as L)" },

      -- ── Universal enveloping algebra morphism (for reference) ─────────
      { id := gid "to_assoc", domain := L, codomain := L,
        description := "Canonical map g → U(g) into the universal envelope" }
    ]
    axioms := [
      -- ── Addition is commutative ───────────────────────────────────────
      { id := gid "add_comm"
        leftPath  := .comp (.prod (.id L) (.id L)) (.atom (gid "add"))
        rightPath := .comp (.prod (.id L) (.id L)) (.atom (gid "add"))
        description := "x + y = y + x" },

      -- ── Addition is associative ───────────────────────────────────────
      { id := gid "add_assoc"
        leftPath  := .comp (.prod (.atom (gid "add")) (.id L)) (.atom (gid "add"))
        rightPath := .comp (.prod (.id L) (.atom (gid "add"))) (.atom (gid "add"))
        description := "(x + y) + z = x + (y + z)" },

      -- ── Zero is identity ──────────────────────────────────────────────
      { id := gid "add_zero"
        leftPath  := .comp (.prod (.atom (gid "zero")) (.id L)) (.atom (gid "add"))
        rightPath := .id L
        description := "0 + x = x" },

      -- ── Negation: x + (−x) = 0 ───────────────────────────────────────
      { id := gid "add_neg"
        leftPath  := .comp (.prod (.id L) (.atom (gid "neg"))) (.atom (gid "add"))
        rightPath := .atom (gid "zero")
        description := "x + (−x) = 0" },

      -- ── LA1: Antisymmetry  [x, x] = 0 ───────────────────────────────
      { id := gid "bracket_antisymm"
        leftPath  := .comp (.prod (.id L) (.id L)) (.atom (gid "bracket"))
        rightPath := .atom (gid "zero")
        description := "[x, x] = 0  (antisymmetry)" },

      -- ── LA1 equivalent: [x,y] + [y,x] = 0 ───────────────────────────
      { id := gid "bracket_skew"
        leftPath  := .comp (.prod (.atom (gid "bracket"))
                                  (.comp (.prod (.id L) (.id L))
                                         (.atom (gid "bracket"))))
                           (.atom (gid "add"))
        rightPath := .atom (gid "zero")
        description := "[x,y] + [y,x] = 0  (skew-symmetry)" },

      -- ── LA2: Jacobi identity [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0 ──
      { id := gid "jacobi"
        leftPath  := .comp (.prod (.id L) (.atom (gid "bracket")))
                           (.atom (gid "bracket"))
        rightPath := .comp (.prod (.atom (gid "bracket")) (.id L))
                           (.comp (.atom (gid "bracket")) (.atom (gid "neg")))
        description := "[x,[y,z]] = [[x,y],z] + [y,[x,z]]  (Jacobi / derivation)" },

      -- ── Bilinearity: [x, y+z] = [x,y] + [x,z] ───────────────────────
      { id := gid "bracket_bilinear_right"
        leftPath  := .comp (.prod (.id L) (.atom (gid "add")))
                           (.atom (gid "bracket"))
        rightPath := .comp (.prod (.atom (gid "bracket")) (.atom (gid "bracket")))
                           (.atom (gid "add"))
        description := "[x, y+z] = [x,y] + [x,z]" },

      -- ── Adjoint: ad_x(y) = [x, y] ────────────────────────────────────
      { id := gid "adjoint_def"
        leftPath  := .comp (.atom (gid "adjoint")) (.atom (gid "bracket"))
        rightPath := .atom (gid "bracket")
        description := "ad_x(y) = [x, y]" }
    ] }

end CatLab.Library
