/-
  CatLab -- Differential Graded Algebras (DGAs)

  A differential graded algebra (A, d) is a graded associative k-algebra

      A = ⊕_{n ∈ ℤ} Aⁿ

  equipped with a differential  d : Aⁿ → Aⁿ⁺¹  (for a cochain DGA;
  or d : Aₙ → Aₙ₋₁  for a chain DGA) satisfying:

    (DGA1)  d² = 0
    (DGA2)  Leibniz rule:  d(ab) = d(a)·b + (−1)^|a| · a·d(b)

  The degree-|a| factor (−1)^|a| is the Koszul sign convention.

  Important special cases:
    - Ω*(M): de Rham algebra of differential forms on a manifold
    - C*(A): singular cochain algebra of a space
    - Ext*(M, M): Ext-algebra in an abelian category
    - A_∞-algebras: DGAs up to coherent homotopy

  We represent the graded structure by a degree morphism  |−| : A → ℤ
  (approximated as a sort Deg) and the algebra structure over the graded
  components.  The differential is a single endomorphism with d² = 0.
-/

import Catlab.Core.Theory

namespace CatLab.Library

def TheoryOfDifferentialGradedAlgebra : Theory :=
  let A   := Expr.atom (gid "A")    -- elements of the DGA
  let Deg := Expr.atom (gid "Deg")  -- degrees (ℤ, represented as a sort)
  { name     := "DifferentialGradedAlgebra"
    doctrine := { doctrine := .DifferentialGraded }
    objects  := [
      { id := gid "A",   description := "Elements of the DGA  A = ⊕ Aⁿ" },
      { id := gid "Deg", description := "Degrees (ℤ)" }
    ]
    morphisms := [
      -- ── Degree map ───────────────────────────────────────────────────
      { id := gid "deg",    domain := A, codomain := Deg,
        description := "Degree |a| : A → ℤ" },

      -- ── k-module structure (in each degree) ──────────────────────────
      { id := gid "add",    domain := .prod A A, codomain := A,
        description := "Addition a + b  (same degree)" },
      { id := gid "neg",    domain := A, codomain := A,
        description := "Additive inverse −a" },
      { id := gid "zero",   domain := .terminal, codomain := A,
        description := "Zero element 0" },
      { id := gid "scale",  domain := .prod A A, codomain := A,
        description := "Scalar multiplication λ·a" },

      -- ── Graded multiplication (degree |a|+|b|) ────────────────────────
      { id := gid "mul",    domain := .prod A A, codomain := A,
        description := "Graded multiplication a · b  (|a·b| = |a|+|b|)" },
      { id := gid "unit",   domain := .terminal, codomain := A,
        description := "Unit element 1 ∈ A⁰" },

      -- ── Differential d : Aⁿ → Aⁿ⁺¹ (cochain convention) ─────────────
      { id := gid "diff",   domain := A, codomain := A,
        description := "Differential d : Aⁿ → Aⁿ⁺¹  (or Aₙ → Aₙ₋₁)" },

      -- ── Degree shift functor A[1] ─────────────────────────────────────
      { id := gid "shift",  domain := A, codomain := A,
        description := "Degree shift: (A[1])ⁿ = Aⁿ⁺¹" },

      -- ── Koszul sign ──────────────────────────────────────────────────
      -- Represented as a morphism that flips sign based on parity of degree
      { id := gid "koszul", domain := A, codomain := A,
        description := "Koszul sign (−1)^|a| · (−)" },

      -- ── Cohomology: ker(d)/im(d) ─────────────────────────────────────
      { id := gid "cocycle", domain := A, codomain := A,
        description := "Cocycle inclusion ker(d) ↪ A" },
      { id := gid "coboundary", domain := A, codomain := A,
        description := "Coboundary projection A ↠ im(d)" },

      -- ── Quasi-isomorphism flag (morphism between DGAs) ────────────────
      { id := gid "dga_map", domain := A, codomain := A,
        description := "DGA morphism f : A → B  (preserves mul and d)" }
    ]
    axioms := [
      -- ── d² = 0 ────────────────────────────────────────────────────────
      { id := gid "diff_sq_zero"
        leftPath  := .comp (.atom (gid "diff")) (.atom (gid "diff"))
        rightPath := .atom (gid "zero")
        description := "d² = 0  (the fundamental DGA axiom)" },

      -- ── Leibniz rule: d(ab) = d(a)b + (−1)^|a| a·d(b) ────────────────
      { id := gid "leibniz"
        leftPath  := .comp (.atom (gid "mul")) (.atom (gid "diff"))
        rightPath := .comp (.prod (.atom (gid "diff")) (.id A))
                           (.comp (.atom (gid "mul"))
                                  (.comp (.prod (.atom (gid "koszul")) (.atom (gid "diff")))
                                         (.atom (gid "add"))))
        description := "d(ab) = d(a)b + (−1)^|a| a·d(b)  (Leibniz / graded derivation)" },

      -- ── Degree of product: |ab| = |a| + |b| ──────────────────────────
      { id := gid "deg_mul"
        leftPath  := .comp (.atom (gid "mul")) (.atom (gid "deg"))
        rightPath := .comp (.prod (.atom (gid "deg")) (.atom (gid "deg")))
                           (.atom (gid "add"))
        description := "|a·b| = |a| + |b|" },

      -- ── Degree of differential: |da| = |a| + 1 ───────────────────────
      { id := gid "deg_diff"
        leftPath  := .comp (.atom (gid "diff")) (.atom (gid "deg"))
        rightPath := .comp (.atom (gid "deg")) (.atom (gid "shift"))
        description := "|da| = |a| + 1" },

      -- ── Associativity of multiplication ───────────────────────────────
      { id := gid "mul_assoc"
        leftPath  := .comp (.prod (.atom (gid "mul")) (.id A)) (.atom (gid "mul"))
        rightPath := .comp (.prod (.id A) (.atom (gid "mul"))) (.atom (gid "mul"))
        description := "(ab)c = a(bc)" },

      -- ── Unit laws ────────────────────────────────────────────────────
      { id := gid "mul_unit_left"
        leftPath  := .comp (.prod (.atom (gid "unit")) (.id A)) (.atom (gid "mul"))
        rightPath := .id A
        description := "1 · a = a" },

      { id := gid "mul_unit_right"
        leftPath  := .comp (.prod (.id A) (.atom (gid "unit"))) (.atom (gid "mul"))
        rightPath := .id A
        description := "a · 1 = a" },

      -- ── Graded commutativity (CDGA / SCGA case): ab = (−1)^{|a||b|} ba ─
      { id := gid "graded_comm"
        leftPath  := .comp (.atom (gid "mul")) (.atom (gid "koszul"))
        rightPath := .comp (.prod (.id A) (.id A)) (.atom (gid "mul"))
        description := "ab = (−1)^{|a||b|} ba  (graded commutativity, for CDGAs)" },

      -- ── d preserves addition ─────────────────────────────────────────
      { id := gid "diff_additive"
        leftPath  := .comp (.atom (gid "add")) (.atom (gid "diff"))
        rightPath := .comp (.prod (.atom (gid "diff")) (.atom (gid "diff")))
                           (.atom (gid "add"))
        description := "d(a+b) = da + db" }
    ] }

end CatLab.Library
