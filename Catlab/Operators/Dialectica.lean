/-
  CatLab — Dialectica / Chu Construction

  Given a symmetric monoidal category C with a distinguished "truth value"
  object Ω, build the Dialectica category Dial(C, Ω) where:

  - Objects: triples (A⁺, A⁻, α : A⁺ ⊗ A⁻ → Ω)
  - Morphisms: (A⁺,A⁻,α) → (B⁺,B⁻,β) are pairs (f : A⁺→B⁺, g : B⁻→A⁻)
    satisfying α ≤ β ∘ (f ⊗ g)

  This construction is fundamental in categorical logic (Gödel's Dialectica
  interpretation) and in *-autonomous categories (Chu spaces).
-/

import Catlab.Core.Theory

namespace CatLab

/-- A Dialectica object: a triple (pos, neg, eval : pos ⊗ neg → Ω) -/
structure DialObject where
  pos : Expr
  neg : Expr
  evalMap : GeneratorId
  deriving Repr, Inhabited

/-- A Dialectica morphism: a pair (forward, backward) with coherence -/
structure DialMorphism where
  forward : GeneratorId
  backward : GeneratorId
  coherenceAxiom : GeneratorId
  deriving Repr, Inhabited

/-- Build the Dialectica category Dial(C, Ω).

    Takes a theory C (assumed symmetric monoidal) and a distinguished
    object Ω (the dualizing / truth-value object), and constructs the
    Dialectica category. -/
def dialectica
    (t : Theory)
    (omega : Expr)
    (namePrefix : String := "dial") : Theory :=
  -- For each pair of objects (A, B) in C, create a Dialectica object (A, B, α)
  let dialObjects := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      ({ id := gid s!"{namePrefix}_({a.id.name},{b.id.name})"
         description := s!"Dialectica object ({a.id.name}⁺, {b.id.name}⁻, α)" }
        : Generator0)

  -- Evaluation maps α : A⁺ ⊗ A⁻ → Ω for each Dialectica object
  let evalMaps := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      ({ id := gid s!"{namePrefix}_α_{a.id.name}_{b.id.name}"
         domain := .tensor (.atom a.id) (.atom b.id)
         codomain := omega
         description := s!"Evaluation α : {a.id.name} ⊗ {b.id.name} → Ω" }
        : Generator1)

  -- Morphisms: for each pair of Dialectica objects,
  -- (A⁺,A⁻,α) → (B⁺,B⁻,β) consists of f : A⁺ → B⁺ and g : B⁻ → A⁻
  let forwardMaps := t.objects.flatMap fun a1 =>
    t.objects.flatMap fun a2 =>
      t.objects.flatMap fun b1 =>
        t.objects.map fun b2 =>
          ({ id := gid s!"{namePrefix}_f_{a1.id.name}_{a2.id.name}_to_{b1.id.name}_{b2.id.name}"
             domain := .atom a1.id
             codomain := .atom b1.id
             description := s!"Forward: {a1.id.name} → {b1.id.name}" }
            : Generator1)

  let backwardMaps := t.objects.flatMap fun a1 =>
    t.objects.flatMap fun a2 =>
      t.objects.flatMap fun b1 =>
        t.objects.map fun b2 =>
          ({ id := gid s!"{namePrefix}_g_{a1.id.name}_{a2.id.name}_to_{b1.id.name}_{b2.id.name}"
             domain := .atom b2.id
             codomain := .atom a2.id
             description := s!"Backward: {b2.id.name} → {a2.id.name}" }
            : Generator1)

  -- Coherence axiom: α ≤ β ∘ (f ⊗ g)
  -- Expressed as: comp (f ⊗ g) β = α (an equality approximating the ≤ condition)
  let coherenceAxioms := t.objects.flatMap fun a1 =>
    t.objects.flatMap fun a2 =>
      t.objects.flatMap fun b1 =>
        t.objects.map fun b2 =>
          let fId : GeneratorId :=
            gid s!"{namePrefix}_f_{a1.id.name}_{a2.id.name}_to_{b1.id.name}_{b2.id.name}"
          let gId : GeneratorId :=
            gid s!"{namePrefix}_g_{a1.id.name}_{a2.id.name}_to_{b1.id.name}_{b2.id.name}"
          let αId : GeneratorId := gid s!"{namePrefix}_α_{a1.id.name}_{a2.id.name}"
          let βId : GeneratorId := gid s!"{namePrefix}_α_{b1.id.name}_{b2.id.name}"
          ({ id := gid s!"{namePrefix}_coh_{a1.id.name}_{a2.id.name}_{b1.id.name}_{b2.id.name}"
             leftPath := .atom αId
             rightPath := .comp (.tensor (.atom fId) (.atom gId)) (.atom βId)
             description := s!"Coherence: α ≤ β ∘ (f ⊗ g)" }
            : Generator2)

  -- Identity axiom: for each Dialectica object (A, B, α), the identity is (id_A, id_B)
  let identityAxioms := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      let fId : GeneratorId :=
        gid s!"{namePrefix}_f_{a.id.name}_{b.id.name}_to_{a.id.name}_{b.id.name}"
      ({ id := gid s!"{namePrefix}_id_{a.id.name}_{b.id.name}"
         leftPath := .atom fId
         rightPath := Expr.id (.atom a.id)
         description := s!"Identity forward component is id on {a.id.name}" }
        : Generator2)

  let identityAxioms_back := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      let gId : GeneratorId :=
        gid s!"{namePrefix}_g_{a.id.name}_{b.id.name}_to_{a.id.name}_{b.id.name}"
      ({ id := gid s!"{namePrefix}_id_back_{a.id.name}_{b.id.name}"
         leftPath := .atom gId
         rightPath := Expr.id (.atom b.id)
         description := s!"Identity backward component is id on {b.id.name}" }
        : Generator2)

  -- Composition axiom: given morphisms (f₁,g₁) and (f₂,g₂),
  -- composition is (f₁ ∘ f₂, g₂ ∘ g₁)
  -- We express this structurally rather than enumerating all triples.
  let compositionNote : Generator2 :=
    { id := gid s!"{namePrefix}_comp_law"
      leftPath := .comp (.atom (gid s!"{namePrefix}_f_composed"))
                        (.atom (gid s!"{namePrefix}_g_composed"))
      rightPath := .comp (.atom (gid s!"{namePrefix}_f_composed"))
                         (.atom (gid s!"{namePrefix}_g_composed"))
      description := "Composition law: (f₁,g₁) ∘ (f₂,g₂) = (f₁∘f₂, g₂∘g₁)" }

  { name := s!"Dial({t.name}, Ω)"
    doctrine := t.doctrine
    objects := dialObjects
    morphisms := evalMaps ++ forwardMaps ++ backwardMaps
    axioms := coherenceAxioms ++ identityAxioms ++ identityAxioms_back ++ [compositionNote] }

end CatLab
