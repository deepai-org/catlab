/-
  CatLab — Day Convolution

  Given a monoidal category (C, ⊗, I), Day convolution lifts the monoidal
  structure to the presheaf category PSh(C).

  For presheaves F, G : Cᵒᵖ → Set:
    (F ⊗_Day G)(c) = ∫^{a,b} Hom(a ⊗ b, c) × F(a) × G(b)

  This is essential for resource-sensitive theories (linear logic, quantum).
-/

import Catlab.Core.Theory

namespace CatLab

/-- Monoidal structure data on a theory -/
structure MonoidalStructure where
  /-- The tensor bifunctor, mapping pairs of objects to their tensor -/
  tensor : Expr → Expr → Expr
  /-- The monoidal unit -/
  unit : Expr
  /-- The underlying theory -/
  theory : Theory

/-- Compute the Day convolution of two presheaves F and G
    over a monoidal base category.

    The result is a new presheaf (F ⊗_Day G) defined by the coend formula. -/
def dayConvolution (ms : MonoidalStructure) (f g : Theory) : Theory :=
  -- For each object c in the base, (F ⊗_Day G)(c) is the coend
  -- ∫^{a,b} Hom(a ⊗ b, c) × F(a) × G(b)
  let dayObjects := ms.theory.objects.map fun c =>
    { id := { name := .tensor (.root s!"({f.name}⊗{g.name})") c.id.name, index := 0 }
      description := s!"Day convolution at {c.id.name}" }

  -- The coend structure: for each pair (a, b), we have a component
  let dayMorphisms := ms.theory.objects.flatMap fun a =>
    ms.theory.objects.map fun b =>
      let ab := ms.tensor (.atom a.id) (.atom b.id)
      { id := { name := .root s!"day_component_{a.id.name}_{b.id.name}", index := 0 }
        domain := .prod (.prod (.hom ab (.var "c")) (.atom { name := .tensor (.root f.name) a.id.name, index := 0 }))
                        (.atom { name := .tensor (.root g.name) b.id.name, index := 0 })
        codomain := .atom { name := .tensor (.root s!"({f.name}⊗{g.name})") (.root "c"), index := 0 }
        description := s!"Day component for ({a.id.name},{b.id.name})" }

  { name := s!"{f.name} ⊗_Day {g.name}"
    doctrine := { doctrine := .SymmetricMonoidal }
    objects := dayObjects
    morphisms := dayMorphisms
    axioms := [] }

/-- The tensor product of two theories via Day convolution.
    This is the operator that produces "every operation of T₁ commutes
    with every operation of T₂" (the Eckmann-Hilton phenomenon). -/
def tensorTheories (t1 t2 : Theory) : Theory :=
  let tensorObjects := t1.objects.flatMap fun a =>
    t2.objects.map fun b =>
      { id := { name := .tensor a.id.name b.id.name, index := 0 }
        description := s!"Tensor of {a.id.name} and {b.id.name}" }

  -- Build the rewrite function for t1 generators
  let rewriteExpr1 (e : Expr) : Expr := match e with
    | .atom gi =>
      if t1.morphisms.any (fun m => m.id == gi) then .atom { gi with name := .tensor gi.name (.root "id") }
      else if t1.objects.any (fun o => o.id == gi) then
        match t2.objects[0]? with
        | some b => .atom { gi with name := .tensor gi.name b.id.name }
        | none => e
      else e
    | other => other

  let rewriteExpr2 (e : Expr) : Expr := match e with
    | .atom gi =>
      if t2.morphisms.any (fun m => m.id == gi) then .atom { gi with name := .tensor (.root "id") gi.name }
      else if t2.objects.any (fun o => o.id == gi) then
        match t1.objects[0]? with
        | some a => .atom { gi with name := .tensor a.id.name gi.name }
        | none => e
      else e
    | other => other

  let t1Morphisms := t1.morphisms.map fun f =>
    { id := { name := .tensor f.id.name (.root "id"), index := 0 }
      domain := f.domain.mapAtoms rewriteExpr1
      codomain := f.codomain.mapAtoms rewriteExpr1
      description := s!"{f.id.name} tensored with identity" }

  let t2Morphisms := t2.morphisms.map fun g =>
    { id := { name := .tensor (.root "id") g.id.name, index := 0 }
      domain := g.domain.mapAtoms rewriteExpr2
      codomain := g.codomain.mapAtoms rewriteExpr2
      description := s!"Identity tensored with {g.id.name}" }

  -- The key: interchange axioms (Eckmann-Hilton)
  let interchangeAxioms := t1.morphisms.flatMap fun f =>
    t2.morphisms.map fun g =>
      { id := { name := .root s!"interchange_{f.id.name}_{g.id.name}", index := 0 }
        leftPath := .comp (.atom { name := .tensor f.id.name (.root "id"), index := 0 }) (.atom { name := .tensor (.root "id") g.id.name, index := 0 })
        rightPath := .comp (.atom { name := .tensor (.root "id") g.id.name, index := 0 }) (.atom { name := .tensor f.id.name (.root "id"), index := 0 })
        description := s!"Interchange: {f.id.name} and {g.id.name} commute" }

  -- Rewrite and prefix axiom names to avoid duplicates
  let t1Axioms := t1.axioms.map fun ax =>
    { id := { name := .root s!"{t1.name}_L_{ax.id.name}", index := 0 }
      leftPath := ax.leftPath.mapAtoms rewriteExpr1
      rightPath := ax.rightPath.mapAtoms rewriteExpr1
      description := ax.description }
  let t2Axioms := t2.axioms.map fun ax =>
    { id := { name := .root s!"{t2.name}_R_{ax.id.name}", index := 0 }
      leftPath := ax.leftPath.mapAtoms rewriteExpr2
      rightPath := ax.rightPath.mapAtoms rewriteExpr2
      description := ax.description }

  { name := s!"{t1.name} ⊗ {t2.name}"
    doctrine := t1.doctrine  -- inherit from first theory
    objects := tensorObjects
    morphisms := t1Morphisms ++ t2Morphisms
    axioms := t1Axioms ++ t2Axioms ++ interchangeAxioms }

end CatLab
