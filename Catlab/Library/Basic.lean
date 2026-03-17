/-
  CatLab -- Basic Theory Library

  Foundational algebraic theories: Poset, Lattice, Semiring, Field,
  Module, VectorSpace, Category (the theory of small categories).
-/

import Catlab.Core.Theory

namespace CatLab.Library

-- ============================================================
-- Poset: a category where every hom-set has at most one element
-- ============================================================

private def P : Expr := .atom ⟨"P", 0⟩

def TheoryOfPosets : Theory :=
  { name := "Poset"
    doctrine := { doctrine := .Category }
    objects := [{ id := ⟨"P", 0⟩, description := "The carrier set" }]
    morphisms := [
      { id := ⟨"≤", 0⟩, domain := .prod P P, codomain := P,
        description := "Partial order: P × P → Prop (represented as P)" }
    ]
    axioms := [
      { id := ⟨"refl", 0⟩
        leftPath := .comp (.prod (.id P) (.id P)) (.atom ⟨"≤", 0⟩)
        rightPath := .id P
        description := "Reflexivity: a ≤ a" },
      { id := ⟨"antisym", 0⟩
        leftPath := .comp (.prod (.atom ⟨"≤", 0⟩) (.atom ⟨"≤", 0⟩)) (.atom ⟨"eq", 0⟩)
        rightPath := .id P
        description := "Antisymmetry: a ≤ b ∧ b ≤ a → a = b" },
      { id := ⟨"trans", 0⟩
        leftPath := .comp (.prod (.atom ⟨"≤", 0⟩) (.atom ⟨"≤", 0⟩)) (.atom ⟨"≤", 0⟩)
        rightPath := .atom ⟨"≤", 0⟩
        description := "Transitivity: a ≤ b ∧ b ≤ c → a ≤ c" }
    ] }

-- ============================================================
-- Lattice: a poset with meets and joins
-- ============================================================

private def L : Expr := .atom ⟨"L", 0⟩

def TheoryOfLattices : Theory :=
  { name := "Lattice"
    doctrine := { doctrine := .CartesianCategory }
    objects := [{ id := ⟨"L", 0⟩, description := "The carrier lattice" }]
    morphisms := [
      { id := ⟨"∧", 0⟩, domain := .prod L L, codomain := L,
        description := "Meet: L × L → L" },
      { id := ⟨"∨", 0⟩, domain := .prod L L, codomain := L,
        description := "Join: L × L → L" },
      { id := ⟨"swap", 0⟩, domain := .prod L L, codomain := .prod L L,
        description := "Symmetry: L × L → L × L" }
    ]
    axioms := [
      { id := ⟨"meet_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∧", 0⟩) (.id L)) (.atom ⟨"∧", 0⟩)
        rightPath := .comp (.prod (.id L) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∧", 0⟩)
        description := "Meet is associative" },
      { id := ⟨"meet_comm", 0⟩
        leftPath := .atom ⟨"∧", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∧", 0⟩)
        description := "Meet is commutative" },
      { id := ⟨"meet_idem", 0⟩
        leftPath := .comp (.prod (.id L) (.id L)) (.atom ⟨"∧", 0⟩)
        rightPath := .id L
        description := "Meet is idempotent: a ∧ a = a" },
      { id := ⟨"join_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∨", 0⟩) (.id L)) (.atom ⟨"∨", 0⟩)
        rightPath := .comp (.prod (.id L) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∨", 0⟩)
        description := "Join is associative" },
      { id := ⟨"join_comm", 0⟩
        leftPath := .atom ⟨"∨", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∨", 0⟩)
        description := "Join is commutative" },
      { id := ⟨"join_idem", 0⟩
        leftPath := .comp (.prod (.id L) (.id L)) (.atom ⟨"∨", 0⟩)
        rightPath := .id L
        description := "Join is idempotent: a ∨ a = a" },
      { id := ⟨"absorption_1", 0⟩
        leftPath := .comp (.prod (.id L) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∧", 0⟩)
        rightPath := .id L
        description := "Absorption: a ∧ (a ∨ b) = a" },
      { id := ⟨"absorption_2", 0⟩
        leftPath := .comp (.prod (.id L) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∨", 0⟩)
        rightPath := .id L
        description := "Absorption: a ∨ (a ∧ b) = a" }
    ] }

-- ============================================================
-- Semiring: like Ring but no additive inverses (e.g., ℕ)
-- ============================================================

private def S : Expr := .atom ⟨"S", 0⟩

def TheoryOfSemirings : Theory :=
  { name := "Semiring"
    doctrine := { doctrine := .LawvereTheory }
    objects := [{ id := ⟨"S", 0⟩, description := "The carrier set" }]
    morphisms := [
      { id := ⟨"add", 0⟩, domain := .prod S S, codomain := S,
        description := "Addition: S × S → S" },
      { id := ⟨"zero", 0⟩, domain := .terminal, codomain := S,
        description := "Additive unit: 1 → S" },
      { id := ⟨"mul", 0⟩, domain := .prod S S, codomain := S,
        description := "Multiplication: S × S → S" },
      { id := ⟨"one", 0⟩, domain := .terminal, codomain := S,
        description := "Multiplicative unit: 1 → S" },
      { id := ⟨"swap", 0⟩, domain := .prod S S, codomain := .prod S S,
        description := "Symmetry: S × S → S × S" }
    ]
    axioms := [
      { id := ⟨"add_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"add", 0⟩) (.id S)) (.atom ⟨"add", 0⟩)
        rightPath := .comp (.prod (.id S) (.atom ⟨"add", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Addition is associative" },
      { id := ⟨"add_comm", 0⟩
        leftPath := .atom ⟨"add", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"add", 0⟩)
        description := "Addition is commutative" },
      { id := ⟨"add_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"zero", 0⟩) (.id S)) (.atom ⟨"add", 0⟩)
        rightPath := .id S
        description := "0 + a = a" },
      { id := ⟨"mul_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.id S)) (.atom ⟨"mul", 0⟩)
        rightPath := .comp (.prod (.id S) (.atom ⟨"mul", 0⟩)) (.atom ⟨"mul", 0⟩)
        description := "Multiplication is associative" },
      { id := ⟨"mul_unit", 0⟩
        leftPath := .comp (.prod (.atom ⟨"one", 0⟩) (.id S)) (.atom ⟨"mul", 0⟩)
        rightPath := .id S
        description := "1 * a = a" },
      { id := ⟨"left_distrib", 0⟩
        leftPath := .comp (.prod (.id S) (.atom ⟨"add", 0⟩)) (.atom ⟨"mul", 0⟩)
        rightPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.atom ⟨"mul", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Left distributivity" },
      { id := ⟨"left_annihilate", 0⟩
        leftPath := .comp (.prod (.atom ⟨"zero", 0⟩) (.id S)) (.atom ⟨"mul", 0⟩)
        rightPath := .atom ⟨"zero", 0⟩
        description := "0 * a = 0" }
    ] }

-- ============================================================
-- Module over a Ring R: an abelian group with scalar multiplication
-- ============================================================

def TheoryOfModules (ringName : String := "R") : Theory :=
  let R := Expr.atom ⟨ringName, 0⟩
  let MO := Expr.atom ⟨"M", 0⟩
  { name := s!"{ringName}-Module"
    doctrine := { doctrine := .LawvereTheory }
    objects := [
      { id := ⟨ringName, 0⟩, description := "The scalar ring" },
      { id := ⟨"M", 0⟩, description := "The module" }
    ]
    morphisms := [
      { id := ⟨"add", 0⟩, domain := .prod MO MO, codomain := MO,
        description := "Module addition: M × M → M" },
      { id := ⟨"zero", 0⟩, domain := .terminal, codomain := MO,
        description := "Zero vector: 1 → M" },
      { id := ⟨"neg", 0⟩, domain := MO, codomain := MO,
        description := "Negation: M → M" },
      { id := ⟨"smul", 0⟩, domain := .prod R MO, codomain := MO,
        description := s!"Scalar multiplication: {ringName} × M → M" },
      { id := ⟨"swap", 0⟩, domain := .prod MO MO, codomain := .prod MO MO,
        description := "Symmetry: M × M → M × M" }
    ]
    axioms := [
      { id := ⟨"add_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"add", 0⟩) (.id MO)) (.atom ⟨"add", 0⟩)
        rightPath := .comp (.prod (.id MO) (.atom ⟨"add", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Addition is associative" },
      { id := ⟨"add_comm", 0⟩
        leftPath := .atom ⟨"add", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"add", 0⟩)
        description := "Addition is commutative" },
      { id := ⟨"smul_distrib", 0⟩
        leftPath := .comp (.prod (.id R) (.atom ⟨"add", 0⟩)) (.atom ⟨"smul", 0⟩)
        rightPath := .comp (.prod (.atom ⟨"smul", 0⟩) (.atom ⟨"smul", 0⟩)) (.atom ⟨"add", 0⟩)
        description := "Scalar distributes over addition: r(a+b) = ra + rb" },
      { id := ⟨"smul_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"mul", 0⟩) (.id MO)) (.atom ⟨"smul", 0⟩)
        rightPath := .comp (.prod (.id R) (.atom ⟨"smul", 0⟩)) (.atom ⟨"smul", 0⟩)
        description := "Scalar associativity: (rs)m = r(sm)" }
    ] }

-- ============================================================
-- The theory of (small) categories: a theory with two sorts
-- ============================================================

def TheoryOfCategories : Theory :=
  let Ob := Expr.atom ⟨"Ob", 0⟩
  let Mor := Expr.atom ⟨"Mor", 0⟩
  { name := "Category"
    doctrine := { doctrine := .Category }
    objects := [
      { id := ⟨"Ob", 0⟩, description := "Objects" },
      { id := ⟨"Mor", 0⟩, description := "Morphisms" }
    ]
    morphisms := [
      { id := ⟨"src", 0⟩, domain := Mor, codomain := Ob,
        description := "Source: Mor → Ob" },
      { id := ⟨"tgt", 0⟩, domain := Mor, codomain := Ob,
        description := "Target: Mor → Ob" },
      { id := ⟨"ident", 0⟩, domain := Ob, codomain := Mor,
        description := "Identity: Ob → Mor" },
      { id := ⟨"comp", 0⟩, domain := .prod Mor Mor, codomain := Mor,
        description := "Composition: Mor ×_{Ob} Mor → Mor" }
    ]
    axioms := [
      { id := ⟨"src_id", 0⟩
        leftPath := .comp (.atom ⟨"ident", 0⟩) (.atom ⟨"src", 0⟩)
        rightPath := .id Ob
        description := "src(id_a) = a" },
      { id := ⟨"tgt_id", 0⟩
        leftPath := .comp (.atom ⟨"ident", 0⟩) (.atom ⟨"tgt", 0⟩)
        rightPath := .id Ob
        description := "tgt(id_a) = a" },
      { id := ⟨"comp_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"comp", 0⟩) (.id Mor)) (.atom ⟨"comp", 0⟩)
        rightPath := .comp (.prod (.id Mor) (.atom ⟨"comp", 0⟩)) (.atom ⟨"comp", 0⟩)
        description := "(f ∘ g) ∘ h = f ∘ (g ∘ h)" },
      { id := ⟨"left_id", 0⟩
        leftPath := .comp (.prod (.atom ⟨"ident", 0⟩) (.id Mor)) (.atom ⟨"comp", 0⟩)
        rightPath := .id Mor
        description := "id ∘ f = f" },
      { id := ⟨"right_id", 0⟩
        leftPath := .comp (.prod (.id Mor) (.atom ⟨"ident", 0⟩)) (.atom ⟨"comp", 0⟩)
        rightPath := .id Mor
        description := "f ∘ id = f" }
    ] }

end CatLab.Library
