/-
  CatLab — Yoneda Embedding

  The "bootstrap function": embeds any small theory C into its presheaf
  category PSh(C) = [Cᵒᵖ, Set]. Every object A becomes the representable
  presheaf Hom(-, A).

  This is the foundation for Day convolution, sheafification, and
  the Grothendieck construction.
-/

import Catlab.Core.Theory
import Catlab.Operators.Mirror

namespace CatLab

/-- The representable presheaf Hom(-, A) for a given object A.
    This creates a new theory representing the functor Cᵒᵖ → Set. -/
def representable (t : Theory) (a : Generator0) : Theory :=
  -- For each object B in C, we get a "set" Hom(B, A)
  let homSets := t.objects.map fun b =>
    { id := ⟨s!"Hom({b.id.name},{a.id.name})", 0⟩
      description := s!"Hom-set from {b.id.name} to {a.id.name}" }

  -- For each morphism f : B → C in C, we get a function
  -- f* : Hom(C, A) → Hom(B, A) (precomposition, contravariant)
  let precompMaps := t.morphisms.map fun f =>
    { id := ⟨s!"{f.id.name}*", 0⟩
      domain := .atom ⟨s!"Hom({repr f.codomain},{repr (Expr.atom a.id)})", 0⟩  -- simplified
      codomain := .atom ⟨s!"Hom({repr f.domain},{repr (Expr.atom a.id)})", 0⟩
      description := s!"Precomposition by {f.id.name}" }

  { name := s!"y({a.id.name})"
    doctrine := { doctrine := .Category }
    objects := homSets
    morphisms := precompMaps
    axioms := [] }

/-- The full Yoneda embedding: map every object to its representable presheaf.
    Returns a list of (original object, presheaf theory) pairs. -/
def yonedaEmbedding (t : Theory) : List (Generator0 × Theory) :=
  t.objects.map fun a => (a, representable t a)

/-- The presheaf category PSh(C) as a theory.
    Objects are functors Cᵒᵖ → Set (here approximated by their action on generators).
    This is the "free cocompletion" of C. -/
def presheafCategory (t : Theory) : Theory :=
  let repObjects := t.objects.map fun a =>
    { id := ⟨s!"y({a.id.name})", 0⟩
      description := s!"Representable presheaf for {a.id.name}" }
  -- Natural transformations between representables are morphisms of C (Yoneda lemma)
  let natTransMorphisms := t.morphisms.map fun f =>
    { id := ⟨s!"y({f.id.name})", 0⟩
      domain := .atom ⟨s!"y({repr f.domain})", 0⟩
      codomain := .atom ⟨s!"y({repr f.codomain})", 0⟩
      description := s!"Yoneda image of {f.id.name}" }
  { name := s!"PSh({t.name})"
    doctrine := { doctrine := .GrothendieckTopos }  -- presheaf categories are topoi
    objects := repObjects
    morphisms := natTransMorphisms
    axioms := t.axioms.map fun a =>
      { a with id := ⟨s!"y({a.id.name})", 0⟩, proofName := none } }

end CatLab
