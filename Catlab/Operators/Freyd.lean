/-
  CatLab — Freyd Cover (Scone / Sierpinski Cone)

  Given a category C with finite limits and a global sections functor
  Γ: C → Set, the scone (Freyd cover) has:
  - Objects: pairs (X, x ∈ Γ(X))
  - Morphisms: morphisms f : X → Y in C such that Γ(f)(x) = y
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute the Freyd cover (scone) of a theory.

    The scone of C with respect to the global sections functor Γ
    is the comma category (1 ↓ Γ). Objects are pairs (X, x) where
    X is an object of C and x ∈ Γ(X) is a chosen global section.
    Morphisms (X, x) → (Y, y) are morphisms f : X → Y in C
    such that Γ(f)(x) = y. -/
def scone (t : Theory) : Theory :=
  -- Objects of the scone: for each object X in C, create (X, x)
  let sconeObjects := t.objects.map fun a =>
    { id := { name := Name.pair a.id.name (.root "x"), index := 0, kind := .sort }
      description := s!"Scone object: ({a.id.name}, x ∈ Γ({a.id.name}))" : Generator0 }

  let exprName (e : Expr) : Name := match e with | .atom g => g.name | _ => .root "?"

  -- Morphisms: for each morphism f : A → B in C, a scone morphism
  -- (A, x) → (B, y) preserving global sections
  let sconeMorphisms := t.morphisms.map fun f =>
    let dn := exprName f.domain
    let cn := exprName f.codomain
    let morphName := Name.arrow dn cn f.id.name
    { id := { name := morphName, index := 0, kind := .morphism }
      domain := .atom { name := Name.pair dn (.root "x"), index := 0, kind := .sort }
      codomain := .atom { name := Name.pair cn (.root "x"), index := 0, kind := .sort }
      description := s!"Scone morphism lifting {f.id.name}" : Generator1 }

  -- Section-preservation axioms: Γ(f)(x) = y for each scone morphism
  let preservationAxioms := t.morphisms.map fun f =>
    let cn := exprName f.codomain
    { id := gid s!"section_pres_{f.id.name}" (k := .twoCell)
      leftPath := .app (.atom (gid s!"Γ" (k := .morphism))) (.atom f.id)
      rightPath := .id (.atom { name := Name.pair cn (.root "x"), index := 0, kind := .sort })
      description := s!"Γ(f) preserves chosen section for {f.id.name}" : Generator2 }

  { name := s!"Scone({t.name})"
    doctrine := { doctrine := .FinitelyComplete }
    objects := sconeObjects
    morphisms := sconeMorphisms
    axioms := preservationAxioms }

/-- The forgetful functor from the scone to the base category:
    (X, x) ↦ X -/
def sconeForgetful (t : Theory) : List Generator1 :=
  t.objects.map fun a =>
    { id := gid s!"π_{a.id.name}" (k := .morphism)
      domain := .atom { name := Name.pair a.id.name (.root "x"), index := 0, kind := .sort }
      codomain := .atom a.id
      description := s!"Forgetful: ({a.id.name}, x) ↦ {a.id.name}" }

end CatLab
