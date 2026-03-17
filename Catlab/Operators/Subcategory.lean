/-
  CatLab — Full Subcategory

  Given a theory and a predicate on object GeneratorIds, extracts the
  full subcategory on those objects satisfying the predicate. All
  morphisms between kept objects are retained, and all axioms
  referencing only kept generators are preserved.
-/

import Catlab.Core.Theory
import Catlab.Core.Validate

namespace CatLab

/-- Compute the full subcategory of t on objects satisfying pred.

    Objects: those whose GeneratorId satisfies pred.
    Morphisms: those whose domain and codomain atoms all refer to kept objects
               (full subcategory keeps all morphisms between kept objects).
    Axioms: those whose left and right paths reference only kept generators. -/
def fullSubcategory (t : Theory) (pred : GeneratorId → Bool) : Theory :=
  let keptObjects := t.objects.filter fun o => pred o.id

  let keptObjectNames := keptObjects.map (·.id.name)

  -- A morphism is kept if all object-atoms in its domain and codomain
  -- refer to kept objects.
  let keptMorphisms := t.morphisms.filter fun m =>
    let domAtoms := m.domain.atoms
    let codAtoms := m.codomain.atoms
    (domAtoms ++ codAtoms).all fun a => keptObjectNames.any (· == a)

  -- Collect all kept generator names (objects + morphisms)
  let allKeptNames := keptObjectNames ++ (keptMorphisms.map (·.id.name))

  -- An axiom is kept if all atoms in its paths refer to kept generators
  let keptAxioms := t.axioms.filter fun ax =>
    let allAtoms := ax.leftPath.atoms ++ ax.rightPath.atoms
    allAtoms.all fun a => allKeptNames.any (· == a)

  { name := s!"Sub({t.name})"
    doctrine := t.doctrine
    objects := keptObjects
    morphisms := keptMorphisms
    axioms := keptAxioms }

end CatLab
