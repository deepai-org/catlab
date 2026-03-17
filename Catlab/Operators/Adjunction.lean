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
    let fa := adj.leftAdjoint.onObjects.apply a.id
    let gfa := adj.rightAdjoint.onObjects.liftExpr fa  -- G applied to F(a)
    { id := gid s!"η_{a.id.name}"
      domain := .atom a.id
      codomain := gfa
      description := s!"Unit at {a.id.name}: {a.id.name} → GF({a.id.name})" }

/-- Compute the counit ε : FG → Id_D of an adjunction.
    For each object b of D, ε_b : F(G(b)) → b. -/
def adjunctionCounit (adj : Adjunction) : List Generator1 :=
  adj.target.objects.map fun b =>
    let gb := adj.rightAdjoint.onObjects.apply b.id
    let fgb := adj.leftAdjoint.onObjects.liftExpr gb  -- F applied to G(b)
    { id := gid s!"ε_{b.id.name}"
      domain := fgb
      codomain := .atom b.id
      description := s!"Counit at {b.id.name}: FG({b.id.name}) → {b.id.name}" }

/-- The triangle identities: the coherence axioms of an adjunction.
    (εF) ∘ (Fη) = id_F  and  (Gε) ∘ (ηG) = id_G -/
def triangleIdentities (adj : Adjunction) : List Generator2 :=
  let leftTriangle := adj.source.objects.map fun a =>
    { id := gid s!"triangle_left_{a.id.name}"
      leftPath := .comp (.atom (gid s!"η_{a.id.name}"))
                        (.atom (gid s!"ε_F({a.id.name})"))
      rightPath := .id (adj.leftAdjoint.onObjects.apply a.id)
      description := s!"Left triangle: (εF) ∘ (Fη) = id at {a.id.name}" }
  let rightTriangle := adj.target.objects.map fun b =>
    { id := gid s!"triangle_right_{b.id.name}"
      leftPath := .comp (.atom (gid s!"ε_{b.id.name}"))
                        (.atom (gid s!"η_G({b.id.name})"))
      rightPath := .id (adj.rightAdjoint.onObjects.apply b.id)
      description := s!"Right triangle: (Gε) ∘ (ηG) = id at {b.id.name}" }
  leftTriangle ++ rightTriangle

/-- Extract the monad T = GF from an adjunction F ⊣ G.
    This gives the monad on the source category C. -/
def adjunctionToMonad (adj : Adjunction) : MonadData :=
  { functor := fun e => adj.rightAdjoint.onObjects.liftExpr (adj.leftAdjoint.onObjects.liftExpr e)
    unit := gid s!"{adj.name}_η"
    mult := gid s!"{adj.name}_μ"
    base := adj.source }

/-- Extract the comonad W = FG from an adjunction F ⊣ G.
    This gives the comonad on the target category D. -/
def adjunctionToComonad (adj : Adjunction) : ComonadData :=
  { functor := fun e => adj.leftAdjoint.onObjects.liftExpr (adj.rightAdjoint.onObjects.liftExpr e)
    counit := gid s!"{adj.name}_ε"
    comult := gid s!"{adj.name}_δ"
    base := adj.target }

/-- The hom-set adjunction: Hom_D(F(a), b) ≅ Hom_C(a, G(b)).
    For each pair (a, b), this is a bijection. -/
def homAdjunction (adj : Adjunction) : List Generator2 :=
  adj.source.objects.flatMap fun a =>
    adj.target.objects.map fun b =>
      { id := gid s!"hom_adj_{a.id.name}_{b.id.name}"
        leftPath := .hom (adj.leftAdjoint.onObjects.apply a.id) (.atom b.id)
        rightPath := .hom (.atom a.id) (adj.rightAdjoint.onObjects.apply b.id)
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
      objects := [{ id := gid "S", description := "A set" }]
      morphisms := []
      axioms := [] }
  -- Identity maps: each generator maps to its own atom
  let idObjMap := GeneratorMap.ofList (setTheory.objects.map fun o => (o.id, .atom o.id))
  let idMorphMap := GeneratorMap.ofList (setTheory.morphisms.map fun m => (m.id, .atom m.id))
  let idAlgObjMap := GeneratorMap.ofList (tAlg.objects.map fun o => (o.id, .atom o.id))
  let idAlgMorphMap := GeneratorMap.ofList (tAlg.morphisms.map fun m => (m.id, .atom m.id))
  let freeF : TheoryFunctor :=
    { name := s!"F_{t.name}"
      source := setTheory
      target := tAlg
      onObjects := idObjMap
      onMorphisms := idMorphMap }
  let forgetU : TheoryFunctor :=
    { name := s!"U_{t.name}"
      source := tAlg
      target := setTheory
      onObjects := idAlgObjMap
      onMorphisms := idAlgMorphMap }
  { name := s!"Free_{t.name}"
    source := setTheory
    target := tAlg
    leftAdjoint := freeF
    rightAdjoint := forgetU }

end CatLab
