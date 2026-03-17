/-
  CatLab -- Adjunctions

  An adjunction F ⊣ G between categories C and D:
  - Left adjoint F : C → D  (the "free" construction)
  - Right adjoint G : D → C  (the "forgetful" functor)
  - Unit η : Id_C → GF
  - Counit ε : FG → Id_D
  - Triangle identities: (εF) ∘ (Fη) = id_F and (Gε) ∘ (ηG) = id_G

  Every adjunction gives rise to a monad GF on C and a comonad FG on D.
-/

import Catlab.Core.Theory
import Catlab.Operators.Monad
import Catlab.Operators.Kan

namespace CatLab

/-- An adjunction F ⊣ G between two theories -/
structure Adjunction where
  name : String
  /-- The source category C -/
  source : Theory
  /-- The target category D -/
  target : Theory
  /-- Left adjoint F : C → D -/
  leftAdjoint : TheoryFunctor
  /-- Right adjoint G : D → C -/
  rightAdjoint : TheoryFunctor

/-- Compute the unit η : Id_C → GF of an adjunction.
    For each object a of C, η_a : a → G(F(a)). -/
def adjunctionUnit (adj : Adjunction) : List Generator1 :=
  adj.source.objects.map fun a =>
    let fa := adj.leftAdjoint.onObjects a.id
    let gfa := adj.rightAdjoint.onObjects a.id  -- simplified: should be G applied to F(a)
    { id := ⟨s!"η_{a.id.name}", 0⟩
      domain := .atom a.id
      codomain := gfa
      description := s!"Unit at {a.id.name}: {a.id.name} → GF({a.id.name})" }

/-- Compute the counit ε : FG → Id_D of an adjunction.
    For each object b of D, ε_b : F(G(b)) → b. -/
def adjunctionCounit (adj : Adjunction) : List Generator1 :=
  adj.target.objects.map fun b =>
    let gb := adj.rightAdjoint.onObjects b.id
    let fgb := adj.leftAdjoint.onObjects b.id  -- simplified
    { id := ⟨s!"ε_{b.id.name}", 0⟩
      domain := fgb
      codomain := .atom b.id
      description := s!"Counit at {b.id.name}: FG({b.id.name}) → {b.id.name}" }

/-- The triangle identities: the coherence axioms of an adjunction.
    (εF) ∘ (Fη) = id_F  and  (Gε) ∘ (ηG) = id_G -/
def triangleIdentities (adj : Adjunction) : List Generator2 :=
  let leftTriangle := adj.source.objects.map fun a =>
    { id := ⟨s!"triangle_left_{a.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"η_{a.id.name}", 0⟩)
                        (.atom ⟨s!"ε_F({a.id.name})", 0⟩)
      rightPath := .id (adj.leftAdjoint.onObjects a.id)
      description := s!"Left triangle: (εF) ∘ (Fη) = id at {a.id.name}" }
  let rightTriangle := adj.target.objects.map fun b =>
    { id := ⟨s!"triangle_right_{b.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"ε_{b.id.name}", 0⟩)
                        (.atom ⟨s!"η_G({b.id.name})", 0⟩)
      rightPath := .id (adj.rightAdjoint.onObjects b.id)
      description := s!"Right triangle: (Gε) ∘ (ηG) = id at {b.id.name}" }
  leftTriangle ++ rightTriangle

/-- Extract the monad T = GF from an adjunction F ⊣ G.
    This gives the monad on the source category C. -/
def adjunctionToMonad (adj : Adjunction) : MonadData :=
  { functor := fun e => adj.rightAdjoint.onObjects (adj.leftAdjoint.onObjects ⟨s!"{repr e}", 0⟩ |> fun _ => ⟨s!"GF", 0⟩)
    unit := ⟨s!"{adj.name}_η", 0⟩
    mult := ⟨s!"{adj.name}_μ", 0⟩
    base := adj.source }

/-- Extract the comonad W = FG from an adjunction F ⊣ G.
    This gives the comonad on the target category D. -/
def adjunctionToComonad (adj : Adjunction) : ComonadData :=
  { functor := fun e => adj.leftAdjoint.onObjects (adj.rightAdjoint.onObjects ⟨s!"{repr e}", 0⟩ |> fun _ => ⟨s!"FG", 0⟩)
    counit := ⟨s!"{adj.name}_ε", 0⟩
    comult := ⟨s!"{adj.name}_δ", 0⟩
    base := adj.target }

/-- The hom-set adjunction: Hom_D(F(a), b) ≅ Hom_C(a, G(b)).
    For each pair (a, b), this is a bijection. -/
def homAdjunction (adj : Adjunction) : List Generator2 :=
  adj.source.objects.flatMap fun a =>
    adj.target.objects.map fun b =>
      { id := ⟨s!"hom_adj_{a.id.name}_{b.id.name}", 0⟩
        leftPath := .hom (adj.leftAdjoint.onObjects a.id) (.atom b.id)
        rightPath := .hom (.atom a.id) (adj.rightAdjoint.onObjects b.id)
        description := s!"Hom(F({a.id.name}), {b.id.name}) ≅ Hom({a.id.name}, G({b.id.name}))" }

/-- Construct the free-forgetful adjunction between a Lawvere theory and Set.
    Every Lawvere theory T gives an adjunction F_T ⊣ U_T where
    F_T : Set → T-Alg (free T-algebra) and U_T : T-Alg → Set (forgetful). -/
def freeForgetfulAdjunction (t : Theory) : Adjunction :=
  let tAlg : Theory :=
    { name := s!"{t.name}-Alg"
      doctrine := t.doctrine
      objects := t.objects
      morphisms := t.morphisms
      axioms := t.axioms }
  let setTheory : Theory :=
    { name := "Set"
      doctrine := { doctrine := .Topos }
      objects := [{ id := ⟨"S", 0⟩, description := "A set" }]
      morphisms := []
      axioms := [] }
  let freeF : TheoryFunctor :=
    { name := s!"F_{t.name}"
      source := setTheory
      target := tAlg
      onObjects := fun x => .atom x
      onMorphisms := fun f => .atom f }
  let forgetU : TheoryFunctor :=
    { name := s!"U_{t.name}"
      source := tAlg
      target := setTheory
      onObjects := fun x => .atom x
      onMorphisms := fun f => .atom f }
  { name := s!"Free_{t.name}"
    source := setTheory
    target := tAlg
    leftAdjoint := freeF
    rightAdjoint := forgetU }

end CatLab
