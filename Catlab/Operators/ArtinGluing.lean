/-
  CatLab — Artin Gluing (Freyd Cover / Sconing)

  Given a theory E (the "topos") and a target theory S with a
  "global sections" functor Γ : E → S, build the comma category S ↓ Γ.

  Objects: triples (s, e, α : s → Γ(e))
  Morphisms: (s, e, α) → (s', e', α') are pairs (f : s → s', g : e → e')
    such that α' ∘ f = Γ(g) ∘ α

  This is a specialization of the comma category construction,
  fundamental for building Freyd covers and logical completions.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Artin gluing / Freyd cover / sconing.

    Builds the comma category S ↓ Γ for a "global sections" functor Γ : E → S.
    The functor Γ is specified as a map on object generators. -/
def artinGluing
    (base : Theory)
    (topos : Theory)
    (gammaOnObj : GeneratorId → Expr)
    (namePrefix : String := "gl") : Theory :=
  -- Objects: triples (s, e, α : s → Γ(e)) for each s ∈ base, e ∈ topos
  let gluingObjects := base.objects.flatMap fun s =>
    topos.objects.map fun e =>
      ({ id := ⟨s!"{namePrefix}_({s.id.name},{e.id.name})", 0⟩
         description := s!"Gluing object: ({s.id.name}, {e.id.name}, α : {s.id.name} → Γ({e.id.name}))" }
        : Generator0)

  -- Structure maps α : s → Γ(e) for each gluing object
  let structureMaps := base.objects.flatMap fun s =>
    topos.objects.map fun e =>
      ({ id := ⟨s!"{namePrefix}_α_{s.id.name}_{e.id.name}", 0⟩
         domain := .atom s.id
         codomain := gammaOnObj e.id
         description := s!"Structure map α : {s.id.name} → Γ({e.id.name})" }
        : Generator1)

  -- Morphisms: for each pair of gluing objects, compatible pairs (f, g)
  -- f-component: morphisms in base between the base parts
  let fMorphisms := base.objects.flatMap fun s =>
    base.objects.flatMap fun s' =>
      topos.objects.flatMap fun e =>
        topos.objects.map fun e' =>
          ({ id := ⟨s!"{namePrefix}_f_{s.id.name}_{e.id.name}_to_{s'.id.name}_{e'.id.name}", 0⟩
             domain := .atom ⟨s!"{namePrefix}_({s.id.name},{e.id.name})", 0⟩
             codomain := .atom ⟨s!"{namePrefix}_({s'.id.name},{e'.id.name})", 0⟩
             description := s!"Gluing morphism ({s.id.name},{e.id.name}) → ({s'.id.name},{e'.id.name})" }
            : Generator1)

  -- Commutativity axiom: α' ∘ f_base = Γ(g) ∘ α
  -- We express this for each morphism between gluing objects
  let commAxioms := base.objects.flatMap fun s =>
    base.objects.flatMap fun s' =>
      topos.objects.flatMap fun e =>
        topos.objects.map fun e' =>
          let fId : GeneratorId :=
            ⟨s!"{namePrefix}_f_{s.id.name}_{e.id.name}_to_{s'.id.name}_{e'.id.name}", 0⟩
          let αId : GeneratorId := ⟨s!"{namePrefix}_α_{s.id.name}_{e.id.name}", 0⟩
          let α'Id : GeneratorId := ⟨s!"{namePrefix}_α_{s'.id.name}_{e'.id.name}", 0⟩
          ({ id := ⟨s!"{namePrefix}_comm_{s.id.name}_{e.id.name}_{s'.id.name}_{e'.id.name}", 0⟩
             leftPath := .comp (.atom αId) (.atom fId)
             rightPath := .comp (.atom fId) (.atom α'Id)
             description := s!"Commutativity: α' ∘ f = Γ(g) ∘ α for ({s.id.name},{e.id.name}) → ({s'.id.name},{e'.id.name})" }
            : Generator2)

  { name := s!"{namePrefix}({base.name}, {topos.name})"
    doctrine := base.doctrine
    objects := gluingObjects
    morphisms := structureMaps ++ fMorphisms
    axioms := commAxioms }

/-- Freyd cover: Artin gluing along the global sections functor
    for a topos with a terminal object serving as the base. -/
def freydCover
    (topos : Theory)
    (gammaOnObj : GeneratorId → Expr)
    (namePrefix : String := "fc") : Theory :=
  let baseTheory : Theory :=
    { name := "Set"
      doctrine := topos.doctrine
      objects := [{ id := ⟨"*", 0⟩, description := "Terminal / point" }]
      morphisms := []
      axioms := [] }
  artinGluing baseTheory topos gammaOnObj namePrefix

end CatLab
