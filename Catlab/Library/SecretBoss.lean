/-
  CatLab — Secret Boss Theories

  Target theories for the Secret Boss stress tests:

  1. HomotopyPullback — The fiber product Σ(a:A).Σ(b:B).path(C, f(a), g(b))
     Tests that the LLM does NOT reach for HITs when limits suffice.

  2. TypeA — A single generic type A (minimal MLTT theory).
     Used as base for quotienting by isSet (set truncation test).

  3. BasedPathSpace — Σ(x:A).path(A, a, x), the based path space.
     Should simplify to Unit (contractibility of based path spaces).

  4. LoopSpaceSquared — The type of 2-loops: path(path(X, x, x), refl(x), refl(x)).
     Used as base for the Eckmann-Hilton commutativity test.
-/

import Catlab.Core.Theory

namespace CatLab.Library

-- ============================================================
-- Boss 5: Homotopy Pullback of a Span A → C ← B
-- ============================================================

/-- The homotopy pullback (fiber product) of a span A →f C ←g B.

    This is the standard HoTT definition using Σ-types and identity types:
      A ×_C^h B := Σ(a:A). Σ(b:B). path(C, f(a), g(b))

    Crucially, this does NOT require a HIT — it's a limit, not a colimit. -/
def TheoryOfHomotopyPullback : Theory :=
  let A := Expr.atom (gid "A")
  let B := Expr.atom (gid "B")
  let C := Expr.atom (gid "C")
  let fId := { name := Name.root "f", kind := GeneratorKind.morphism : GeneratorId }
  let gId := { name := Name.root "g", kind := GeneratorKind.morphism : GeneratorId }
  let pullbackId : GeneratorId := { name := .root "HoPb", kind := .sort }
  -- HoPb := Σ(a:A). Σ(b:B). path(C, f(a), g(b))
  let _pullbackExpr :=
    Expr.sigma "a" A
      (Expr.sigma "b" (B.liftBVars 1 0)
        (Expr.path (C.liftBVars 2 0)
          (Expr.app (Expr.atom fId |>.liftBVars 2 0) (.bvar 1))
          (Expr.app (Expr.atom gId |>.liftBVars 2 0) (.bvar 0))))
  { name := "HomotopyPullback"
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects := [
      { id := gid "A", description := "Source type A" },
      { id := gid "B", description := "Source type B" },
      { id := gid "C", description := "Target type C (apex of the span)" },
      { id := pullbackId, description := "Homotopy pullback A ×_C^h B = Σ(a:A).Σ(b:B).path(C, f(a), g(b))" }
    ]
    morphisms := [
      -- f : A → C
      { id := fId, domain := A, codomain := C,
        description := "Left leg of the span: f : A → C" },
      -- g : B → C
      { id := gId, domain := B, codomain := C,
        description := "Right leg of the span: g : B → C" },
      -- π₁ : HoPb → A  (first projection)
      { id := { name := .root "pr1", kind := .morphism }
        domain := .atom pullbackId, codomain := A,
        description := "First projection: pr1 : HoPb → A" },
      -- π₂ : HoPb → B  (second projection)
      { id := { name := .root "pr2", kind := .morphism }
        domain := .atom pullbackId, codomain := B,
        description := "Second projection: pr2 : HoPb → B" },
      -- The path witness: for any p : HoPb, path(C, f(pr1(p)), g(pr2(p)))
      { id := { name := .root "commutes", kind := .morphism }
        domain := .atom pullbackId
        codomain := .prod C C  -- codomain in the path type over C
        description := "Commutativity witness: path(C, f(pr1(p)), g(pr2(p)))" }
    ]
    axioms := [
      -- f ∘ pr1 = g ∘ pr2 (the pullback square commutes up to homotopy)
      { id := gid "pullback_commutes"
        leftPath := .comp (.atom { name := .root "pr1", kind := .morphism })
                          (.atom fId)
        rightPath := .comp (.atom { name := .root "pr2", kind := .morphism })
                           (.atom gId)
        description := "f ∘ pr1 = g ∘ pr2 (pullback square commutes)" }
    ] }

-- ============================================================
-- Boss 6: TypeA — a single generic type
-- ============================================================

/-- A minimal MLTT theory with just one type A and a point.
    Used as the base for quotienting by isSet (set truncation). -/
def TheoryOfTypeA : Theory :=
  let A := Expr.atom (gid "A")
  { name := "TypeA"
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects := [
      { id := gid "A", description := "A generic type" }
    ]
    morphisms := [
      { id := { name := .root "a", kind := .morphism }
        domain := .terminal, codomain := A,
        description := "A witness element a : 1 → A" }
    ]
    axioms := [] }

-- ============================================================
-- Boss 7: Based Path Space — Σ(x:A). path(A, a, x)
-- ============================================================

/-- The based path space at a point a : A.

    BasedPathSpace(A, a) := Σ(x : A). path(A, a, x)

    This is contractible by path induction (J-elimination). The center
    of contraction is (a, refl(a)). The simplification target should
    reduce to Unit / TerminalTheory. -/
def TheoryOfBasedPathSpace : Theory :=
  let A := Expr.atom (gid "A")
  let aId : GeneratorId := { name := .root "a", kind := .morphism }
  let aExpr := Expr.app (.atom aId) .terminal
  let bpsId : GeneratorId := { name := .root "BPS", kind := .sort }
  -- BPS := Σ(x:A). path(A, a, x)
  let _bpsExpr :=
    Expr.sigma "x" A
      (Expr.path (A.liftBVars 1 0) (aExpr.liftBVars 1 0) (.bvar 0))
  { name := "BasedPathSpace"
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects := [
      { id := gid "A", description := "The ambient type" },
      { id := bpsId, description := "Based path space Σ(x:A). path(A, a, x)" }
    ]
    morphisms := [
      -- a : 1 → A  (the base point)
      { id := aId, domain := .terminal, codomain := A,
        description := "Base point a : 1 → A" },
      -- center : 1 → BPS  (the center of contraction: (a, refl(a)))
      { id := { name := .root "center", kind := .morphism }
        domain := .terminal
        codomain := .atom bpsId
        description := "Center of contraction: (a, refl(a)) : 1 → BPS" },
      -- contract : BPS → 1  (the contraction map — every point equals center)
      { id := { name := .root "contract", kind := .morphism }
        domain := .atom bpsId
        codomain := .terminal
        description := "Contraction: BPS → 1 (BPS is contractible)" }
    ]
    axioms := [
      -- contract ∘ center = id_1
      { id := gid "contr_section"
        leftPath := .comp (.atom { name := .root "center", kind := .morphism })
                          (.atom { name := .root "contract", kind := .morphism })
        rightPath := .id .terminal
        description := "center then contract = id (BPS is contractible)" },
      -- center ∘ contract = id_BPS (up to homotopy)
      { id := gid "contr_retract"
        leftPath := .comp (.atom { name := .root "contract", kind := .morphism })
                          (.atom { name := .root "center", kind := .morphism })
        rightPath := .id (.atom bpsId)
        description := "contract then center = id (BPS is contractible)" }
    ] }

-- ============================================================
-- Boss 8: Loop Space Squared — Ω²(X, x)
-- ============================================================

/-- The double loop space Ω²(X, x) = path(path(X, x, x), refl(x), refl(x)).

    The type of 2-loops at a point x in X. By the Eckmann-Hilton argument,
    composition of 2-loops is commutative. -/
def TheoryOfLoopSpaceSquared : Theory :=
  let X := Expr.atom (gid "X")
  let xId : GeneratorId := { name := .root "x", kind := .morphism }
  let xExpr := Expr.app (.atom xId) .terminal
  let _loopSpace := Expr.path X xExpr xExpr  -- Ω¹ = path(X, x, x)
  let _reflX := Expr.refl xExpr             -- refl(x) : Ω¹
  let loop2Id : GeneratorId := { name := .root "Loop2", kind := .sort }
  -- Ω² = path(path(X, x, x), refl(x), refl(x))
  -- i.e., the type of paths between refl(x) and refl(x) in the loop space
  { name := "LoopSpaceSquared"
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects := [
      { id := gid "X", description := "The ambient space" },
      { id := loop2Id, description := "Ω²(X, x) = path(Ω¹(X,x), refl(x), refl(x)) — the 2-loop space" }
    ]
    morphisms := [
      -- x : 1 → X  (the base point)
      { id := xId, domain := .terminal, codomain := X,
        description := "Base point x : 1 → X" },
      -- refl2 : 1 → Loop2  (the trivial 2-loop: refl(refl(x)))
      { id := { name := .root "refl2", kind := .morphism }
        domain := .terminal
        codomain := .atom loop2Id
        description := "Trivial 2-loop: refl(refl(x)) : 1 → Ω²" },
      -- compose2 : Loop2 × Loop2 → Loop2  (vertical composition of 2-loops)
      { id := { name := .root "compose2", kind := .morphism }
        domain := .prod (.atom loop2Id) (.atom loop2Id)
        codomain := .atom loop2Id
        description := "Vertical composition of 2-loops: compose2 : Ω² × Ω² → Ω²" }
    ]
    axioms := [
      -- Left unit: compose2(refl2, p) = p
      { id := gid "compose2_left_unit"
        leftPath := .comp
          (.prod (.atom { name := .root "refl2", kind := .morphism }) (.id (.atom loop2Id)))
          (.atom { name := .root "compose2", kind := .morphism })
        rightPath := .id (.atom loop2Id)
        description := "Left unit: compose2(refl2, p) = p" },
      -- Right unit: compose2(p, refl2) = p
      { id := gid "compose2_right_unit"
        leftPath := .comp
          (.prod (.id (.atom loop2Id)) (.atom { name := .root "refl2", kind := .morphism }))
          (.atom { name := .root "compose2", kind := .morphism })
        rightPath := .id (.atom loop2Id)
        description := "Right unit: compose2(p, refl2) = p" }
    ] }

end CatLab.Library
