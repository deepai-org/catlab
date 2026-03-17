/-
  CatLab -- Functor Categories [C, D]

  The category of functors from C to D:
  - Objects: functors F : C → D
  - Morphisms: natural transformations α : F ⟹ G

  Special cases:
  - [C, Set] = PSh(C) (presheaf category, already in Yoneda.lean)
  - [1, C] ≅ C
  - [2, C] ≅ Arr(C) (arrow category)
-/

import Catlab.Core.Theory
import Catlab.Operators.Kan

namespace CatLab

/-- Compute the functor category [C, D].

    Given two theories C and D, [C, D] has:
    - Objects: theory functors C → D (one for each compatible assignment)
    - Morphisms: natural transformations (families of D-morphisms with naturality) -/
def functorCategory (source target : Theory) : Theory :=
  -- For a finite presentation, we represent functors by their action on generators.
  -- A functor F : C → D is determined by:
  --   F on objects: each object of C maps to an object of D
  --   F on morphisms: each morphism of C maps to a morphism of D
  --   Preserving composition and identities

  -- We create a "generic functor" object for each possible assignment
  -- In practice this is the internal hom in the 2-category Cat
  let funcObj := { id := ⟨s!"[{source.name},{target.name}]", 0⟩
                   description := s!"Functor category [{source.name}, {target.name}]" }

  -- Natural transformation components: for each object a of C,
  -- a morphism α_a : F(a) → G(a) in D
  let natTransComponents := source.objects.map fun a =>
    { id := ⟨s!"α_{a.id.name}", 0⟩
      domain := .atom ⟨s!"F({a.id.name})", 0⟩
      codomain := .atom ⟨s!"G({a.id.name})", 0⟩
      description := s!"Component of natural transformation at {a.id.name}" }

  -- Naturality squares: for each morphism f : a → b in C,
  -- G(f) ∘ α_a = α_b ∘ F(f)
  let naturalityAxioms := source.morphisms.map fun f =>
    { id := ⟨s!"naturality_{f.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"α_{repr f.domain}", 0⟩)
                        (.atom ⟨s!"G({f.id.name})", 0⟩)
      rightPath := .comp (.atom ⟨s!"F({f.id.name})", 0⟩)
                         (.atom ⟨s!"α_{repr f.codomain}", 0⟩)
      description := s!"Naturality: G({f.id.name}) ∘ α = α ∘ F({f.id.name})" }

  { name := s!"[{source.name}, {target.name}]"
    doctrine := target.doctrine
    objects := [funcObj]
    morphisms := natTransComponents
    axioms := naturalityAxioms }

/-- The evaluation functor ev : [C, D] × C → D
    sending (F, a) ↦ F(a). -/
def evalFunctor (source target : Theory) : List Generator1 :=
  source.objects.map fun a =>
    { id := ⟨s!"ev_{a.id.name}", 0⟩
      domain := .prod (.atom ⟨s!"[{source.name},{target.name}]", 0⟩) (.atom a.id)
      codomain := .atom ⟨s!"F({a.id.name})", 0⟩
      description := s!"Evaluation at {a.id.name}" }

/-- Compute the natural transformation category Nat(F, G)
    for two specific functors F, G : C → D.
    This is the hom-set in [C, D], made into an object of D. -/
def natTransformations (source : Theory)
    (fOnObj gOnObj : GeneratorId → Expr) : Theory :=
  let natObj := { id := ⟨"Nat(F,G)", 0⟩
                  description := "Natural transformations F ⟹ G" }

  let components := source.objects.map fun a =>
    { id := ⟨s!"α_{a.id.name}", 0⟩
      domain := fOnObj a.id
      codomain := gOnObj a.id
      description := s!"Component at {a.id.name}" }

  let naturality := source.morphisms.map fun f =>
    { id := ⟨s!"nat_{f.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"α_{repr f.domain}", 0⟩) (gOnObj f.id)
      rightPath := .comp (fOnObj f.id) (.atom ⟨s!"α_{repr f.codomain}", 0⟩)
      description := s!"Naturality square for {f.id.name}" }

  { name := "Nat(F,G)"
    doctrine := { doctrine := .Category }
    objects := [natObj]
    morphisms := components
    axioms := naturality }

end CatLab
