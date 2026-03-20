/-
  CatLab — Yoneda Embedding

  The "bootstrap function": embeds any small theory C into its presheaf
  category PSh(C) = [Cᵒᵖ, Set]. Every object A becomes the representable
  presheaf Hom(-, A).

  This is the foundation for Day convolution, sheafification, and
  the Grothendieck construction.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Catlab.Operators.Mirror

namespace CatLab

/-- The representable presheaf Hom(-, A) for a given object A.
    This creates a new theory representing the functor Cᵒᵖ → Set. -/
def representable (t : Theory) (a : Generator0) : Theory :=
  -- For each object B in C, we get a "set" Hom(B, A)
  let homSets := t.objects.map fun b =>
    { id := { name := .root s!"Hom({b.id.name},{a.id.name})", index := 0 }
      description := s!"Hom-set from {b.id.name} to {a.id.name}" }

  -- For each morphism f : B → C in C, we get a function
  -- f* : Hom(C, A) → Hom(B, A) (precomposition, contravariant)
  let aName := a.id.name.toString
  let precompMaps := t.morphisms.map fun f =>
    let domName := f.domain.toName.toString
    let codName := f.codomain.toName.toString
    { id := { name := .root s!"{f.id.name}*", index := 0 }
      domain := .atom { name := .root s!"Hom({codName},{aName})", index := 0 }
      codomain := .atom { name := .root s!"Hom({domName},{aName})", index := 0 }
      description := s!"Precomposition by {f.id.name}" }

  -- Functoriality: id* = id (identity preservation)
  let idAxioms := t.objects.map fun b =>
    { id := { name := .root s!"y_id_{b.id.name}", index := 0, kind := .twoCell }
      leftPath := .id (.atom { name := .root s!"Hom({b.id.name.toString},{a.id.name.toString})", index := 0 })
      rightPath := .id (.atom { name := .root s!"Hom({b.id.name.toString},{a.id.name.toString})", index := 0 })
      description := s!"Functoriality: id* = id at {b.id.name}" : Generator2 }

  -- Functoriality: (g ∘ f)* = f* ∘ g* (contravariant composition)
  let compAxioms := t.morphisms.flatMap fun f =>
    t.morphisms.filterMap fun g =>
      -- Only emit axiom when f and g are composable: cod(f) == dom(g)
      if f.codomain == g.domain then
        let fDomName := f.domain.toName.toString
        let gCodName := g.codomain.toName.toString
        let fCodName := f.codomain.toName.toString
        let aName := a.id.name.toString
        some { id := { name := .root s!"y_comp_{f.id.name}_{g.id.name}", index := 0, kind := .twoCell }
               leftPath := .atom { name := .root s!"comp({f.id.name},{g.id.name})*", index := 0, kind := .morphism }
               rightPath := .comp
                 (.atom { name := .root s!"{g.id.name}*", index := 0, kind := .morphism })
                 (.atom { name := .root s!"{f.id.name}*", index := 0, kind := .morphism })
               description := s!"Functoriality: ({g.id.name} ∘ {f.id.name})* = {f.id.name}* ∘ {g.id.name}*" : Generator2 }
      else none

  { name := s!"y({a.id.name})"
    doctrine := { doctrine := .Category }
    objects := homSets
    morphisms := precompMaps
    axioms := idAxioms ++ compAxioms }

/-- The full Yoneda embedding: map every object to its representable presheaf.
    Returns a list of (original object, presheaf theory) pairs. -/
def yonedaEmbedding (t : Theory) : List (Generator0 × Theory) :=
  t.objects.map fun a => (a, representable t a)

/-- The presheaf category PSh(C) as a theory.
    Objects are functors Cᵒᵖ → Set (here approximated by their action on generators).
    This is the "free cocompletion" of C. -/
def presheafCategory (t : Theory) : Theory :=
  let repObjects := t.objects.map fun a =>
    { id := { name := .root s!"y({a.id.name})", index := 0 }
      description := s!"Representable presheaf for {a.id.name}" }
  -- Natural transformations between representables are morphisms of C (Yoneda lemma)
  let natTransMorphisms := t.morphisms.map fun f =>
    let domName := f.domain.toName.toString
    let codName := f.codomain.toName.toString
    { id := { name := .root s!"y({f.id.name})", index := 0 }
      domain := .atom { name := .root s!"y({domName})", index := 0 }
      codomain := .atom { name := .root s!"y({codName})", index := 0 }
      description := s!"Yoneda image of {f.id.name}" }
  { name := s!"PSh({t.name})"
    doctrine := { doctrine := .Category }  -- only claim Category; topos structure not encoded
    objects := repObjects
    morphisms := natTransMorphisms
    axioms := t.axioms.map fun a =>
      { a with id := { name := .root s!"y({a.id.name})", index := 0 }, proofName := none } }

end CatLab
