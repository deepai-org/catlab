/-
  CatLab — Ind and Pro Completions

  Ind(C) is the free completion of C under filtered colimits.
  Pro(C) is the free completion of C under cofiltered limits (dual of Ind).
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute the Ind-completion of a theory.

    For each object A, we adjoin Ind(A) with a canonical morphism η_A : A → Ind(A).
    For each morphism f : A → B, we adjoin Ind(f) : Ind(A) → Ind(B) with naturality. -/
def indCompletion (t : Theory) : Theory :=
  let indObjects : List Generator0 := t.objects.map fun obj =>
    { id := ⟨s!"Ind({obj.id.name})", 0⟩
      description := s!"Ind-completion of {obj.id.name}" }

  let canonicalMaps : List Generator1 := t.objects.map fun obj =>
    { id := ⟨s!"η_{obj.id.name}", 0⟩
      domain := .atom obj.id
      codomain := .atom ⟨s!"Ind({obj.id.name})", 0⟩
      description := s!"Canonical map {obj.id.name} → Ind({obj.id.name})" }

  -- For each morphism f : A → B, add Ind(f) : Ind(A) → Ind(B)
  -- We use the morphism id name to construct the Ind morphism
  let indMorphisms : List Generator1 := t.morphisms.map fun m =>
    { id := ⟨s!"Ind({m.id.name})", 0⟩
      domain := .atom ⟨s!"Ind({m.id.name}_dom)", 0⟩
      codomain := .atom ⟨s!"Ind({m.id.name}_cod)", 0⟩
      description := s!"Ind-completion of morphism {m.id.name}" }

  -- Naturality: Ind(f) ∘ η_A = η_B ∘ f
  let naturalityAxioms : List Generator2 := t.morphisms.map fun m =>
    { id := ⟨s!"Ind_nat_{m.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"η_{m.id.name}_dom", 0⟩)
                        (.atom ⟨s!"Ind({m.id.name})", 0⟩)
      rightPath := .comp (.atom m.id)
                         (.atom ⟨s!"η_{m.id.name}_cod", 0⟩)
      description := s!"Naturality of η at {m.id.name}" }

  { name := s!"Ind({t.name})"
    doctrine := t.doctrine
    objects := t.objects ++ indObjects
    morphisms := t.morphisms ++ canonicalMaps ++ indMorphisms
    axioms := t.axioms ++ naturalityAxioms }

/-- Compute the Pro-completion of a theory.

    Pro(C) is the dual of Ind: adjoin cofiltered limits.
    For each object A, we get Pro(A) with ε_A : Pro(A) → A. -/
def proCompletion (t : Theory) : Theory :=
  let proObjects : List Generator0 := t.objects.map fun obj =>
    { id := ⟨s!"Pro({obj.id.name})", 0⟩
      description := s!"Pro-completion of {obj.id.name}" }

  let canonicalMaps : List Generator1 := t.objects.map fun obj =>
    { id := ⟨s!"ε_{obj.id.name}", 0⟩
      domain := .atom ⟨s!"Pro({obj.id.name})", 0⟩
      codomain := .atom obj.id
      description := s!"Canonical map Pro({obj.id.name}) → {obj.id.name}" }

  let proMorphisms : List Generator1 := t.morphisms.map fun m =>
    { id := ⟨s!"Pro({m.id.name})", 0⟩
      domain := .atom ⟨s!"Pro({m.id.name}_dom)", 0⟩
      codomain := .atom ⟨s!"Pro({m.id.name}_cod)", 0⟩
      description := s!"Pro-completion of morphism {m.id.name}" }

  -- Naturality: ε_B ∘ Pro(f) = f ∘ ε_A
  let naturalityAxioms : List Generator2 := t.morphisms.map fun m =>
    { id := ⟨s!"Pro_nat_{m.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"Pro({m.id.name})", 0⟩)
                        (.atom ⟨s!"ε_{m.id.name}_cod", 0⟩)
      rightPath := .comp (.atom ⟨s!"ε_{m.id.name}_dom", 0⟩)
                         (.atom m.id)
      description := s!"Naturality of ε at {m.id.name}" }

  { name := s!"Pro({t.name})"
    doctrine := t.doctrine
    objects := t.objects ++ proObjects
    morphisms := t.morphisms ++ canonicalMaps ++ proMorphisms
    axioms := t.axioms ++ naturalityAxioms }

end CatLab
