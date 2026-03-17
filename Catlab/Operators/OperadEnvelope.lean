/-
  CatLab — Operadic Envelope

  Translates between multicategories/operads and strict symmetric monoidal
  categories. Given a theory where morphisms may have multi-object domains
  (product types), computes the free strict symmetric monoidal category.

  Objects: formal tensor products of base objects (including the unit I).
  Morphisms: lifted from the multicategory, plus braiding morphisms.
  Axioms: hexagon and triangle coherence for the symmetric braiding.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute the operadic envelope of a multicategory/operad presented as a theory.

    Objects are formal tensor products of base objects (singletons and the
    monoidal unit I). For each morphism f : A₁ × ... × Aₙ → B, we get
    f : A₁ ⊗ ... ⊗ Aₙ → B in the strict symmetric monoidal category.
    Braiding morphisms σ_{A,B} : A ⊗ B → B ⊗ A are added for all pairs,
    together with hexagon coherence axioms. -/
def operadicEnvelope (t : Theory) : Theory :=
  -- The monoidal unit
  let unitObj : Generator0 :=
    { id := gid "I"
      description := "Monoidal unit" }

  -- Singleton objects (one per base object)
  let singletonObjects := t.objects.map fun a =>
    { id := a.id
      description := s!"Singleton tensor {a.id.name}" : Generator0 }

  -- Binary tensor product objects A ⊗ B for each pair
  let tensorObjects := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := { name := .tensor a.id.name b.id.name, index := 0, kind := .sort }
        description := s!"{a.id.name} ⊗ {b.id.name}" : Generator0 }

  -- Lift each morphism from the multicategory.
  -- Domain is rewritten: product types become tensor products.
  let liftedMorphisms := t.morphisms.map fun f =>
    let tensorDomain := match f.domain with
      | .prod l r => .tensor l r
      | other => other
    { id := gid s!"env({f.id.name})"
      domain := tensorDomain
      codomain := f.codomain
      description := s!"Envelope lift of {f.id.name}" : Generator1 }

  -- Braiding morphisms σ_{A,B} : A ⊗ B → B ⊗ A for each pair
  let braidings := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := gid s!"σ_{a.id.name}_{b.id.name}"
        domain := .tensor (.atom a.id) (.atom b.id)
        codomain := .tensor (.atom b.id) (.atom a.id)
        description := s!"Braiding {a.id.name} ⊗ {b.id.name} → {b.id.name} ⊗ {a.id.name}"
          : Generator1 }

  -- Left unitor: λ_A : I ⊗ A → A
  let leftUnitors := t.objects.map fun a =>
    { id := gid s!"λ_{a.id.name}"
      domain := .tensor (.atom (gid "I")) (.atom a.id)
      codomain := .atom a.id
      description := s!"Left unitor for {a.id.name}" : Generator1 }

  -- Right unitor: ρ_A : A ⊗ I → A
  let rightUnitors := t.objects.map fun a =>
    { id := gid s!"ρ_{a.id.name}"
      domain := .tensor (.atom a.id) (.atom (gid "I"))
      codomain := .atom a.id
      description := s!"Right unitor for {a.id.name}" : Generator1 }

  -- Involutivity: σ_{B,A} ∘ σ_{A,B} = id_{A⊗B}
  let involutivityAxioms := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := gid s!"involutivity_{a.id.name}_{b.id.name}"
        leftPath := .comp
          (.atom (gid s!"σ_{a.id.name}_{b.id.name}"))
          (.atom (gid s!"σ_{b.id.name}_{a.id.name}"))
        rightPath := Expr.id (.tensor (.atom a.id) (.atom b.id))
        description := s!"σ_{b.id.name},{a.id.name} ∘ σ_{a.id.name},{b.id.name} = id"
          : Generator2 }

  -- Hexagon axiom 1: σ_{A,B⊗C} = (id_B ⊗ σ_{A,C}) ∘ (σ_{A,B} ⊗ id_C)
  let hexagonAxioms1 := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.map fun c =>
        { id := gid s!"hexagon1_{a.id.name}_{b.id.name}_{c.id.name}"
          leftPath := .atom (gid s!"σ_{a.id.name}_{b.id.name}⊗{c.id.name}")
          rightPath := .comp
            (.tensor (.atom (gid s!"σ_{a.id.name}_{b.id.name}")) (Expr.id (.atom c.id)))
            (.tensor (Expr.id (.atom b.id)) (.atom (gid s!"σ_{a.id.name}_{c.id.name}")))
          description := s!"Hexagon 1 for ({a.id.name},{b.id.name},{c.id.name})"
            : Generator2 }

  -- Hexagon axiom 2: σ_{A⊗B,C} = (σ_{A,C} ⊗ id_B) ∘ (id_A ⊗ σ_{B,C})
  let hexagonAxioms2 := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      t.objects.map fun c =>
        { id := gid s!"hexagon2_{a.id.name}_{b.id.name}_{c.id.name}"
          leftPath := .atom (gid s!"σ_{a.id.name}⊗{b.id.name}_{c.id.name}")
          rightPath := .comp
            (.tensor (Expr.id (.atom a.id)) (.atom (gid s!"σ_{b.id.name}_{c.id.name}")))
            (.tensor (.atom (gid s!"σ_{a.id.name}_{c.id.name}")) (Expr.id (.atom b.id)))
          description := s!"Hexagon 2 for ({a.id.name},{b.id.name},{c.id.name})"
            : Generator2 }

  -- Triangle axiom: ρ_A = (id_A ⊗ λ_I⁻¹) — in strict case, unitors compose trivially
  -- σ_{A,I} ∘ ρ_A-side = λ_A-side (unit coherence with braiding)
  let triangleAxioms := t.objects.map fun a =>
    { id := gid s!"triangle_{a.id.name}"
      leftPath := .comp
        (.atom (gid s!"σ_{a.id.name}_I"))
        (.atom (gid s!"λ_{a.id.name}"))
      rightPath := .atom (gid s!"ρ_{a.id.name}")
      description := s!"Triangle axiom: lambda_A composed with sigma_(A,I) = rho_A"
        : Generator2 }

  { name := s!"Env({t.name})"
    doctrine := { doctrine := .SymmetricMonoidal }
    objects := [unitObj] ++ singletonObjects ++ tensorObjects
    morphisms := liftedMorphisms ++ braidings ++ leftUnitors ++ rightUnitors
    axioms := involutivityAxioms ++ hexagonAxioms1 ++ hexagonAxioms2 ++ triangleAxioms }

end CatLab
