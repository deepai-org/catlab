/-
  CatLab — Drinfeld Center (Braided Monoidal Center)

  Given a monoidal category C, computes the braided monoidal center Z(C).
  Objects are pairs (X, σ) where σ is a half-braiding: a natural family
  σ_A : X ⊗ A → A ⊗ X satisfying coherence conditions.

  This is distinct from Center.lean which uses a different construction.
  The Drinfeld center is always braided monoidal, even when C is not.
-/

import Catlab.Core.Theory
import Catlab.Core.PrettyPrint

namespace CatLab

/-- Compute the Drinfeld center Z(C) of a monoidal category.

    Objects: pairs (X, σ) where X ∈ Ob(C) and σ_A : X ⊗ A → A ⊗ X is a
    natural half-braiding for every object A.

    Morphisms: f : (X, σ^X) → (Y, σ^Y) such that
      σ^Y_A ∘ (f ⊗ id_A) = (id_A ⊗ f) ∘ σ^X_A  for all A.

    The center inherits a braided monoidal structure where the braiding
    is given by the half-braiding itself. -/
def drinfeldCenter (t : Theory) : Theory :=
  -- Objects: pairs (X, σ^X) for each base object X
  let centerObjects := t.objects.map fun x =>
    { id := { name := .pair x.id.name (.root s!"σ^{x.id.name}"), index := 0, kind := .sort }
      description := s!"Center object ({x.id.name}, σ^{x.id.name})"
        : Generator0 }

  -- Half-braiding morphisms: σ^X_A : X ⊗ A → A ⊗ X for each (X, A)
  let halfBraidings := t.objects.flatMap fun x =>
    t.objects.map fun a =>
      { id := gid s!"σ^{x.id.name}_{a.id.name}"
        domain := .tensor (.atom x.id) (.atom a.id)
        codomain := .tensor (.atom a.id) (.atom x.id)
        description := s!"Half-braiding for {x.id.name} at {a.id.name}"
          : Generator1 }

  -- Center morphisms: for each morphism f : X → Y in C, lift to Z(f) : (X,σ^X) → (Y,σ^Y)
  let centerMorphisms := t.morphisms.map fun f =>
    { id := gid s!"Z({f.id.name})"
      domain := f.domain
      codomain := f.codomain
      description := s!"Drinfeld center lift of {f.id.name}"
        : Generator1 }

  -- Naturality: for each X and each morphism f : A → B,
  -- (f ⊗ id_X) ∘ σ^X_A = σ^X_B ∘ (id_X ⊗ f)
  let naturalityAxioms := t.objects.flatMap fun x =>
    t.morphisms.map fun f =>
      { id := gid s!"nat_σ^{x.id.name}_{f.id.name}"
        leftPath := .comp
          (.atom (gid s!"σ^{x.id.name}_{f.id.name}"))
          (.tensor (.atom f.id) (Expr.id (.atom x.id)))
        rightPath := .comp
          (.tensor (Expr.id (.atom x.id)) (.atom f.id))
          (.atom (gid s!"σ^{x.id.name}_{f.id.name}"))
        description := s!"Naturality of σ^{x.id.name} at {f.id.name}"
          : Generator2 }

  -- Compatibility: for each center morphism Z(f) : X → Y and each object A,
  -- σ^Y_A ∘ (Z(f) ⊗ id_A) = (id_A ⊗ Z(f)) ∘ σ^X_A
  let compatAxioms := t.morphisms.flatMap fun f =>
    t.objects.map fun a =>
      { id := gid s!"compat_Z({f.id.name})_{a.id.name}"
        leftPath := .comp
          (.tensor (.atom (gid s!"Z({f.id.name})")) (Expr.id (.atom a.id)))
          (.atom (gid s!"σ^{f.codomain.toName}_{a.id.name}"))
        rightPath := .comp
          (.atom (gid s!"σ^{f.domain.toName}_{a.id.name}"))
          (.tensor (Expr.id (.atom a.id)) (.atom (gid s!"Z({f.id.name})")))
        description := s!"Compatibility of Z({f.id.name}) with half-braidings at {a.id.name}"
          : Generator2 }

  -- Hexagon/tensor coherence: σ^X_{A⊗B} = (id_A ⊗ σ^X_B) ∘ (σ^X_A ⊗ id_B)
  let hexagonAxioms := t.objects.flatMap fun x =>
    t.objects.flatMap fun a =>
      t.objects.map fun b =>
        { id := gid s!"hex_σ^{x.id.name}_{a.id.name}_{b.id.name}"
          leftPath := .atom (gid s!"σ^{x.id.name}_{a.id.name}⊗{b.id.name}")
          rightPath := .comp
            (.tensor (.atom (gid s!"σ^{x.id.name}_{a.id.name}")) (Expr.id (.atom b.id)))
            (.tensor (Expr.id (.atom a.id)) (.atom (gid s!"σ^{x.id.name}_{b.id.name}")))
          description := s!"Hexagon: σ^{x.id.name} at {a.id.name} ⊗ {b.id.name}"
            : Generator2 }

  -- Braiding on Z(C): β_{(X,σ^X),(Y,σ^Y)} = σ^X_Y
  let braidingAxioms := t.objects.flatMap fun x =>
    t.objects.map fun y =>
      { id := gid s!"braid_{x.id.name}_{y.id.name}"
        leftPath := .atom (gid s!"β_{x.id.name}_{y.id.name}")
        rightPath := .atom (gid s!"σ^{x.id.name}_{y.id.name}")
        description := s!"Braiding on Z(C): β = σ^{x.id.name}_{y.id.name}"
          : Generator2 }

  { name := s!"Z({t.name})"
    doctrine := { doctrine := .BraidedMonoidal }
    objects := centerObjects
    morphisms := halfBraidings ++ centerMorphisms
    axioms := naturalityAxioms ++ compatAxioms ++ hexagonAxioms ++ braidingAxioms }

end CatLab
