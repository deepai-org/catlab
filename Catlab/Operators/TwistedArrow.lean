/-
  CatLab -- Twisted Arrow Category Tw(C)

  The twisted arrow category of C. Objects are morphisms f : A → B in C.
  A morphism from f : A → B to g : A' → B' is a pair (α : A' → A, β : B → B')
  such that g = β ∘ f ∘ α.

  This is the canonical domain for coend calculations:
    ∫^{A} F(A,A) ≅ colim_{Tw(C)} F
-/

import Catlab.Core.Theory

namespace CatLab

/-- Helper to extract the atom GeneratorId from an Expr, if it is an atom -/
private def Expr.atom? : Expr → Option GeneratorId
  | .atom gid => some gid
  | _ => none

/-- Compute the twisted arrow category Tw(C).

    Objects: one for each morphism f : A → B in C, named as (A → B : f).
    Morphisms: for each pair of morphisms (f : A → B, g : A' → B'),
      a "twisted square" (α : A' → A, β : B → B') with axiom g = β ∘ f ∘ α.
    Axioms: commutativity of each twisted square. -/
def twistedArrow (t : Theory) : Theory :=
  let gidName (e : Expr) : Name :=
    match e.atom? with | some g => g.name | none => .root "?"

  -- Helper to get the arrow name for a morphism
  let twObjName (f : Generator1) : Name :=
    Name.arrow (gidName f.domain) (gidName f.codomain) f.id.name

  -- Objects: one per morphism in C
  let twObjects := t.morphisms.map fun f =>
    { id := { name := twObjName f, index := 0, kind := .sort }
      description := s!"Tw-object: {f.id.name}" : Generator0 }

  -- Morphisms: for each pair (f, g), the source component α and target component β
  let twMorphisms := t.morphisms.flatMap fun f =>
    t.morphisms.flatMap fun g =>
      let pairName := .pair (twObjName f) (twObjName g)
      -- α : A' → A  (contravariant in the source)
      let alpha : Generator1 :=
        { id := { name := .nested pairName "α", index := 0, kind := .morphism }
          domain := g.domain
          codomain := f.domain
          description := s!"Tw-source: α for ({f.id.name} → {g.id.name})" }
      -- β : B → B'  (covariant in the target)
      let beta : Generator1 :=
        { id := { name := .nested pairName "β", index := 0, kind := .morphism }
          domain := f.codomain
          codomain := g.codomain
          description := s!"Tw-target: β for ({f.id.name} → {g.id.name})" }
      [alpha, beta]

  -- Axioms: for each pair (f, g), the twisted square commutes: g = β ∘ f ∘ α
  let twAxioms := t.morphisms.flatMap fun f =>
    t.morphisms.map fun g =>
      let pairName := .pair (twObjName f) (twObjName g)
      let alphaExpr := Expr.atom { name := .nested pairName "α", index := 0, kind := .morphism }
      let betaExpr := Expr.atom { name := .nested pairName "β", index := 0, kind := .morphism }
      let fExpr := Expr.atom f.id
      let gExpr := Expr.atom g.id
      { id := { name := .nested pairName "tw-sq", index := 0, kind := .twoCell }
        leftPath := gExpr
        rightPath := .comp betaExpr (.comp fExpr alphaExpr)
        description := s!"Twisted square: {g.id.name} = β ∘ {f.id.name} ∘ α" : Generator2 }

  { name := s!"Tw({t.name})"
    doctrine := t.doctrine
    objects := twObjects
    morphisms := twMorphisms
    axioms := twAxioms }

end CatLab
