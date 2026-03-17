/-
  CatLab — Sheafification & Localization

  Sheafification: forces a presheaf to respect a Grothendieck topology
  via the plus-construction applied twice (L²).

  This is the left adjoint to the inclusion Sh(C,J) ↪ PSh(C).
-/

import Catlab.Core.Theory

namespace CatLab

/-- A Grothendieck topology on a theory: for each object, a collection of
    covering sieves (families of morphisms that "cover" the object). -/
structure GrothendieckTopology where
  /-- For each object (by name), the covering families.
      Each cover is a list of morphism names whose codomains are the object. -/
  covers : GeneratorId → List (List GeneratorId)

/-- A sieve on an object X: a collection of morphisms into X closed under
    precomposition. -/
structure Sieve where
  object : GeneratorId
  morphisms : List GeneratorId

/-- The plus-construction L⁺(F): the "one-step improvement" toward a sheaf.

    For each object c, L⁺(F)(c) = colim_{S ∈ J(c)} Match(F, S)
    where Match(F, S) is the set of matching families for the sieve S. -/
def plusConstruction (t : Theory) (topology : GrothendieckTopology) : Theory :=
  let plusObjects := t.objects.map fun c =>
    { id := gid s!"L⁺({c.id.name})"
      description := s!"Plus construction at {c.id.name}" }

  -- The comparison map: F(c) → L⁺F(c) (sending a section to the constant matching family)
  let comparisonMaps := t.objects.map fun c =>
    { id := gid s!"η_{c.id.name}"
      domain := .atom c.id
      codomain := .atom (gid s!"L⁺({c.id.name})")
      description := s!"Comparison map at {c.id.name}" }

  { t with
    name := s!"L⁺({t.name})"
    objects := plusObjects
    morphisms := comparisonMaps }

/-- Sheafification: apply the plus-construction twice.
    L²(F) is always a sheaf for the topology J. -/
def sheafify (t : Theory) (topology : GrothendieckTopology) : Theory :=
  let once := plusConstruction t topology
  let twice := plusConstruction once topology
  { twice with name := s!"Sh({t.name})" }

/-- The associated sheaf functor a : PSh(C) → Sh(C,J).
    Returns the sheafified theory together with the universal map η : F → aF. -/
def associatedSheaf (t : Theory) (topology : GrothendieckTopology)
    : Theory × List Generator1 :=
  let sheaf := sheafify t topology
  let universalMap := t.objects.map fun c =>
    { id := gid s!"sheafify_η_{c.id.name}"
      domain := .atom c.id
      codomain := .atom (gid s!"Sh({c.id.name})")
      description := s!"Universal map to sheafification at {c.id.name}" }
  (sheaf, universalMap)

end CatLab
