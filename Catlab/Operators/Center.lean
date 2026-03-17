/-
  CatLab — Drinfeld Center

  The Drinfeld center Z(C) of a monoidal category C. Objects are pairs
  (A, σ) where σ is a half-braiding, and morphisms are maps compatible
  with the half-braidings. The center is always braided monoidal.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Catlab.Core.PrettyPrint

namespace CatLab

/-- Compute the Drinfeld center Z(C) of a monoidal category.

    Objects: pairs (A, σ) where A is an object of C and σ_X : A ⊗ X → X ⊗ A
    is a natural half-braiding for every object X.

    Morphisms: f : (A, σ^A) → (B, σ^B) such that
    σ^B_X ∘ (f ⊗ id_X) = (id_X ⊗ f) ∘ σ^A_X for all X.

    The center is always braided monoidal, even when C is not braided. -/
def center (t : Theory) : Theory :=
  -- For each object A, create a center object (A, σ^A)
  let centerObjects := t.objects.map fun a =>
    { id := gid s!"({a.id.name}, σ^{a.id.name})"
      description := s!"Object {a.id.name} with half-braiding σ^{a.id.name}"
        : Generator0 }

  -- For each object A and each object X, create the half-braiding morphism
  -- σ^A_X : A ⊗ X → X ⊗ A
  let halfBraidings := t.objects.flatMap fun a =>
    t.objects.map fun x =>
      { id := gid s!"σ^{a.id.name}_{x.id.name}"
        domain := .tensor (.atom a.id) (.atom x.id)
        codomain := .tensor (.atom x.id) (.atom a.id)
        description := s!"Half-braiding for {a.id.name} at {x.id.name}"
          : Generator1 }

  -- For each morphism f : A → B in C, create the center morphism
  -- with the compatibility condition
  let centerMorphisms := t.morphisms.map fun f =>
    { id := gid s!"Z({f.id.name})"
      domain := f.domain
      codomain := f.codomain
      description := s!"Center lift of {f.id.name}"
        : Generator1 }

  -- Naturality axioms: for each half-braiding σ^A and each morphism g : X → Y,
  -- (g ⊗ id_A) ∘ σ^A_X = σ^A_Y ∘ (id_A ⊗ g)
  let naturalityAxioms := t.objects.flatMap fun a =>
    t.morphisms.map fun g =>
      { id := gid s!"naturality_σ^{a.id.name}_{g.id.name}"
        leftPath := .comp
          (.atom (gid s!"σ^{a.id.name}_{g.id.name}"))
          (.tensor (.atom g.id) (Expr.id (.atom a.id)))
        rightPath := .comp
          (.tensor (Expr.id (.atom a.id)) (.atom g.id))
          (.atom (gid s!"σ^{a.id.name}_{g.id.name}"))
        description := s!"Naturality of σ^{a.id.name} at {g.id.name}"
          : Generator2 }

  -- Compatibility axioms: for each center morphism Z(f) : A → B,
  -- σ^B_X ∘ (Z(f) ⊗ id_X) = (id_X ⊗ Z(f)) ∘ σ^A_X
  let compatibilityAxioms := t.morphisms.flatMap fun f =>
    t.objects.map fun x =>
      { id := gid s!"compat_{f.id.name}_{x.id.name}"
        leftPath := .comp
          (.tensor (.atom (gid s!"Z({f.id.name})")) (Expr.id (.atom x.id)))
          (.atom (gid s!"σ^{f.codomain}_{x.id.name}"))
        rightPath := .comp
          (.atom (gid s!"σ^{f.domain}_{x.id.name}"))
          (.tensor (Expr.id (.atom x.id)) (.atom (gid s!"Z({f.id.name})")))
        description := s!"Compatibility of Z({f.id.name}) with half-braidings at {x.id.name}"
          : Generator2 }

  -- Tensor compatibility axioms: σ^A_{X⊗Y} = (id_X ⊗ σ^A_Y) ∘ (σ^A_X ⊗ id_Y)
  let tensorCompatAxioms := t.objects.flatMap fun a =>
    t.objects.flatMap fun x =>
      t.objects.map fun y =>
        { id := gid s!"tensor_compat_σ^{a.id.name}_{x.id.name}_{y.id.name}"
          leftPath := .atom (gid s!"σ^{a.id.name}_{x.id.name}⊗{y.id.name}")
          rightPath := .comp
            (.tensor (.atom (gid s!"σ^{a.id.name}_{x.id.name}")) (Expr.id (.atom y.id)))
            (.tensor (Expr.id (.atom x.id)) (.atom (gid s!"σ^{a.id.name}_{y.id.name}")))
          description := s!"Tensor compatibility for σ^{a.id.name} at ({x.id.name}, {y.id.name})"
            : Generator2 }

  -- Braiding on the center: β_{(A,σ^A),(B,σ^B)} = σ^A_B
  let braidingAxioms := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := gid s!"braiding_{a.id.name}_{b.id.name}"
        leftPath := .atom (gid s!"β_{a.id.name}_{b.id.name}")
        rightPath := .atom (gid s!"σ^{a.id.name}_{b.id.name}")
        description := s!"Braiding on Z(C) given by the half-braiding"
          : Generator2 }

  { name := s!"Z({t.name})"
    doctrine := { doctrine := .BraidedMonoidal }
    objects := centerObjects
    morphisms := halfBraidings ++ centerMorphisms
    axioms := naturalityAxioms ++ compatibilityAxioms ++ tensorCompatAxioms ++ braidingAxioms }

end CatLab
