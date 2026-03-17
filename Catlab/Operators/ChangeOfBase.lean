/-
  CatLab — Change of Base (Enrichment Transfer)

  Given a lax monoidal functor F : V → W between monoidal categories,
  and a V-enriched category C, produce the W-enriched category F_*(C).

  Objects remain the same; hom-objects become F(C(a,b)).
  Composition transfers via the lax monoidal structure maps.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Data for a lax monoidal functor F : V → W used for enrichment transfer.
    The functor maps hom-objects and the lax structure maps handle composition. -/
structure LaxMonoidalFunctor where
  /-- Name of the functor -/
  name : String
  /-- The source enrichment base V -/
  source : Theory
  /-- The target enrichment base W -/
  target : Theory
  /-- How the functor acts on objects (hom-object expressions) -/
  mapObj : Expr → Expr

/-- An enriched category represented as a theory with typed hom-objects -/
structure EnrichedCategory where
  /-- The underlying theory -/
  theory : Theory
  /-- The enrichment base -/
  base : Theory

/-- Compute the change-of-base F_*(C): transfer enrichment along a lax monoidal functor.

    Given:
    - F : V → W, a lax monoidal functor
    - C, a V-enriched category

    Produces: F_*(C), a W-enriched category with
    - Same objects as C
    - Hom-objects: F(C(a,b))
    - Composition: F(C(b,c)) ⊗_W F(C(a,b)) → F(C(b,c) ⊗_V C(a,b)) → F(C(a,c))
      using the lax structure map φ and F applied to composition in C -/
def changeOfBase (func : LaxMonoidalFunctor) (enriched : EnrichedCategory) : Theory :=
  let t := enriched.theory

  -- Objects stay the same
  let newObjects := t.objects

  -- Morphisms: apply F to each hom-type (domain/codomain)
  let applyF (e : Expr) : Expr := func.mapObj e

  let newMorphisms := t.morphisms.map fun m =>
    { id := gid s!"F_*({m.id.name})"
      domain := applyF m.domain
      codomain := applyF m.codomain
      description := s!"Image of {m.id.name} under {func.name}_*"
        : Generator1 }

  -- Lax structure maps: φ_{a,b} : F(C(b,c)) ⊗ F(C(a,b)) → F(C(b,c) ⊗ C(a,b))
  let laxMaps := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.map fun c =>
        { id := gid s!"φ_{a.id.name}_{b.id.name}_{c.id.name}"
          domain := .tensor
            (applyF (.hom (.atom b.id) (.atom c.id)))
            (applyF (.hom (.atom a.id) (.atom b.id)))
          codomain := applyF (.tensor
            (.hom (.atom b.id) (.atom c.id))
            (.hom (.atom a.id) (.atom b.id)))
          description := s!"Lax monoidal structure map for ({a.id.name},{b.id.name},{c.id.name})"
            : Generator1 }

  -- Composition in F_*(C): uses φ then F(composition in C)
  let compositionMaps := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.map fun c =>
        { id := gid s!"comp_F_*_{a.id.name}_{b.id.name}_{c.id.name}"
          domain := .tensor
            (applyF (.hom (.atom b.id) (.atom c.id)))
            (applyF (.hom (.atom a.id) (.atom b.id)))
          codomain := applyF (.hom (.atom a.id) (.atom c.id))
          description := s!"Composition in F_*(C) from {a.id.name} through {b.id.name} to {c.id.name}"
            : Generator1 }

  -- Unit map: φ₀ : I_W → F(I_V)
  let unitMap :=
    { id := gid s!"φ₀_{func.name}"
      domain := .unit
      codomain := applyF .unit
      description := s!"Lax monoidal unit map for {func.name}"
        : Generator1 }

  -- Functoriality axiom: composition in F_*(C) factors through φ
  -- comp_F_* = F(comp_C) ∘ φ
  let functorialityAxioms := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.map fun c =>
        { id := gid s!"functoriality_{a.id.name}_{b.id.name}_{c.id.name}"
          leftPath := .atom (gid s!"comp_F_*_{a.id.name}_{b.id.name}_{c.id.name}")
          rightPath := .comp
            (.atom (gid s!"φ_{a.id.name}_{b.id.name}_{c.id.name}"))
            (applyF (.atom (gid s!"comp_{a.id.name}_{b.id.name}_{c.id.name}")))
          description := s!"Functoriality: F_* composition factors through lax structure"
            : Generator2 }

  -- Associativity axiom for the lax structure maps
  let assocAxioms := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.flatMap fun c =>
        t.objects.map fun d =>
          { id := gid s!"lax_assoc_{a.id.name}_{b.id.name}_{c.id.name}_{d.id.name}"
            leftPath := .comp
              (.tensor
                (.atom (gid s!"φ_{b.id.name}_{c.id.name}_{d.id.name}"))
                (Expr.id (applyF (.hom (.atom a.id) (.atom b.id)))))
              (.atom (gid s!"φ_{a.id.name}_{b.id.name}_{d.id.name}"))
            rightPath := .comp
              (.tensor
                (Expr.id (applyF (.hom (.atom c.id) (.atom d.id))))
                (.atom (gid s!"φ_{a.id.name}_{b.id.name}_{c.id.name}")))
              (.atom (gid s!"φ_{a.id.name}_{c.id.name}_{d.id.name}"))
            description := s!"Lax associativity coherence"
              : Generator2 }

  { name := s!"{func.name}_*({t.name})"
    doctrine := { doctrine := .MonoidalCategory }
    objects := newObjects
    morphisms := newMorphisms ++ laxMaps ++ compositionMaps ++ [unitMap]
    axioms := functorialityAxioms ++ assocAxioms }

end CatLab
