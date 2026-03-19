/-
  CatLab — Isbell Duality / Conjugation

  For a category C, the Isbell adjunction relates:
  - Presheaves  [C^op, Set]  (contravariant functors)
  - Copresheaves [C, Set]^op  (covariant functors, opposite)

  The adjunction Spec ⊣ Cospec yields:
  - isbellSpec (left adjoint): presheaf ↦ copresheaf ("spectrum")
  - isbellCospec (right adjoint): copresheaf ↦ presheaf ("costructure")

  Objects fixed by the induced monad are "Isbell self-dual".
-/

import Catlab.Core.Theory

namespace CatLab

/-- The Isbell spectrum functor (left adjoint):
    Takes a presheaf P : C^op → Set and produces a copresheaf Spec(P) : C → Set
    defined by Spec(P)(c) = Nat(P, Hom(-, c)) — natural transformations from P
    to the representable presheaf at c. -/
def isbellSpec (t : Theory) : Theory :=
  -- For each presheaf (approximated by objects of C), Spec maps it to a copresheaf
  let specObjects := t.objects.map fun a =>
    { id := gid s!"Spec({a.id.name})"
      description := s!"Isbell spectrum of {a.id.name}: Nat(P, Hom(-,{a.id.name}))" : Generator0 }

  -- For each morphism f : a → b in C, Spec is covariant:
  -- Spec(P)(f) : Spec(P)(a) → Spec(P)(b) by postcomposition
  let specMorphisms := (t.morphisms.filter fun f =>
    match f.domain, f.codomain with
    | .atom _, .atom _ => true
    | _, _ => false
  ).map fun f =>
    { id := gid s!"Spec({f.id.name})"
      domain := .atom (gid s!"Spec({f.domain.toName})")
      codomain := .atom (gid s!"Spec({f.codomain.toName})")
      description := s!"Spec applied to {f.id.name} (covariant)" : Generator1 }

  { name := s!"Spec({t.name})"
    doctrine := { doctrine := .Category }
    objects := specObjects
    morphisms := specMorphisms
    axioms := [] }

/-- The Isbell costructure functor (right adjoint):
    Takes a copresheaf Q : C → Set and produces a presheaf Cospec(Q) : C^op → Set
    defined by Cospec(Q)(c) = Nat(Hom(c, -), Q) — natural transformations from the
    corepresentable to Q. -/
def isbellCospec (t : Theory) : Theory :=
  let cospecObjects := t.objects.map fun a =>
    { id := gid s!"Cospec({a.id.name})"
      description := s!"Isbell costructure at {a.id.name}: Nat(Hom({a.id.name},-), Q)" : Generator0 }

  let cospecMorphisms := (t.morphisms.filter fun f =>
    match f.domain, f.codomain with
    | .atom _, .atom _ => true
    | _, _ => false
  ).map fun f =>
    { id := gid s!"Cospec({f.id.name})"
      -- Contravariant: reverses direction
      domain := .atom (gid s!"Cospec({f.codomain.toName})")
      codomain := .atom (gid s!"Cospec({f.domain.toName})")
      description := s!"Cospec applied to {f.id.name} (contravariant)" : Generator1 }

  { name := s!"Cospec({t.name})"
    doctrine := { doctrine := .Category }
    objects := cospecObjects
    morphisms := cospecMorphisms
    axioms := [] }

/-- The full Isbell adjunction: Spec ⊣ Cospec.

    Constructs a theory representing the adjunction data between
    presheaves and copresheaves on C. Includes the unit and counit. -/
def isbellAdjunction (t : Theory) : Theory :=
  let specT := isbellSpec t
  let cospecT := isbellCospec t

  -- Composite objects: Cospec(Spec(A)) and Spec(Cospec(A))
  let cospecSpecObjs := t.objects.map fun a =>
    { id := gid s!"Cospec(Spec({a.id.name}))"
      description := s!"Cospec(Spec({a.id.name}))" : Generator0 }
  let specCospecObjs := t.objects.map fun a =>
    { id := gid s!"Spec(Cospec({a.id.name}))"
      description := s!"Spec(Cospec({a.id.name}))" : Generator0 }

  -- Unit η : P → Cospec(Spec(P))
  let unitMorphisms := t.objects.map fun a =>
    { id := gid s!"η_isbell_{a.id.name}"
      domain := .atom a.id
      codomain := .atom (gid s!"Cospec(Spec({a.id.name}))")
      description := s!"Isbell unit at {a.id.name}: P → Cospec(Spec(P))" : Generator1 }

  -- Counit ε : Spec(Cospec(Q)) → Q
  let counitMorphisms := t.objects.map fun a =>
    { id := gid s!"ε_isbell_{a.id.name}"
      domain := .atom (gid s!"Spec(Cospec({a.id.name}))")
      codomain := .atom a.id
      description := s!"Isbell counit at {a.id.name}: Spec(Cospec(Q)) → Q" : Generator1 }

  { name := s!"Isbell({t.name})"
    doctrine := { doctrine := .Category }
    objects := t.objects ++ specT.objects ++ cospecT.objects ++ cospecSpecObjs ++ specCospecObjs
    morphisms := unitMorphisms ++ counitMorphisms ++
                 specT.morphisms ++ cospecT.morphisms
    axioms := [] }

/-- Check if an object is Isbell self-dual: fixed by the Cospec ∘ Spec monad.
    Returns the self-duality axiom name for the given object. -/
def isbellSelfDualCheck (t : Theory) (objName : String) : Option GeneratorId :=
  let adj := isbellAdjunction t
  adj.axioms.find? (fun ax => ax.id.name == .root s!"isbell_fixed_{objName}")
  |>.map (·.id)

end CatLab
