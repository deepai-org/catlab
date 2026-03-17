/-
  CatLab — Core (Maximal Groupoid)

  Takes a category and returns its core: same objects, but only
  the isomorphisms are kept as morphisms. Since we cannot computationally
  determine isomorphisms from a finite presentation, the caller provides
  an explicit list of generator IDs that are invertible.
-/

import Catlab.Core.Theory
import Catlab.Core.Validate

namespace CatLab

/-- Compute the core (maximal groupoid) of a category.

    Objects: same as t.
    Morphisms: only those whose id is in `isos`, plus formal inverses.
    Axioms: invertibility axioms (f ∘ f⁻¹ = id, f⁻¹ ∘ f = id),
            plus any original axioms that reference only kept morphisms.

    Since determining which morphisms are isomorphisms is undecidable
    from a presentation, the caller must supply the list explicitly. -/
def core (t : Theory) (isos : List GeneratorId) : Theory :=
  let isoNames := isos.map (·.name)

  -- Keep only the specified isomorphisms
  let keptMorphisms := t.morphisms.filter fun m =>
    isoNames.any (· == m.id.name)

  -- Create formal inverses for each iso
  let inverses := keptMorphisms.map fun m =>
    { id := { m.id with name := .op m.id.name }
      domain := m.codomain
      codomain := m.domain
      description := s!"Inverse of {m.id.name}" : Generator1 }

  -- Invertibility axioms: f ∘ f⁻¹ = id_cod, f⁻¹ ∘ f = id_dom
  let invertAxioms := keptMorphisms.flatMap fun m =>
    let fAtom := Expr.atom m.id
    let fInvAtom := Expr.atom { m.id with name := .op m.id.name }
    [ { id := { name := Name.app (.root "inv_r") m.id.name, index := 0, kind := .twoCell }
        leftPath := .comp fAtom fInvAtom
        rightPath := .id m.codomain
        description := s!"Right inverse: {m.id.name} ∘ {m.id.name}⁻¹ = id" : Generator2 },
      { id := { name := Name.app (.root "inv_l") m.id.name, index := 0, kind := .twoCell }
        leftPath := .comp fInvAtom fAtom
        rightPath := .id m.domain
        description := s!"Left inverse: {m.id.name}⁻¹ ∘ {m.id.name} = id" : Generator2 } ]

  -- Keep original axioms that only reference kept generators
  let allKeptNames := (keptMorphisms.map (·.id.name)) ++
                      (inverses.map (·.id.name)) ++
                      (t.objects.map (·.id.name))
  let keptAxioms := t.axioms.filter fun ax =>
    let lAtoms := ax.leftPath.atoms
    let rAtoms := ax.rightPath.atoms
    (lAtoms ++ rAtoms).all fun a => allKeptNames.any (· == a)

  { name := s!"Core({t.name})"
    doctrine := { doctrine := .Category }
    objects := t.objects
    morphisms := keptMorphisms ++ inverses
    axioms := keptAxioms ++ invertAxioms }

end CatLab
