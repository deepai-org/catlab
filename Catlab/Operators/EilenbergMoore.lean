/-
  CatLab — Eilenberg-Moore Category of Algebras

  Given a monad T on a category C, the Eilenberg-Moore category C^T has:
  - Objects: T-algebras (A, a : TA → A) satisfying unit and associativity
  - Morphisms: algebra homomorphisms (maps commuting with structure maps)
-/

import Catlab.Core.Theory
import Catlab.Operators.Monad

namespace CatLab

/-- Compute the Eilenberg-Moore category C^T for a monad T.

    Objects are T-algebras: pairs (A, a : TA → A) where
    - a ∘ η_A = id_A            (unit law)
    - a ∘ μ_A = a ∘ T(a)        (associativity law)

    Morphisms are algebra homomorphisms: f : (A, a) → (B, b) is
    a morphism f : A → B in C such that f ∘ a = b ∘ T(f). -/
def eilenbergMooreCategory (m : MonadData) : Theory :=
  -- Objects: one T-algebra for each base object
  let emObjects := m.base.objects.map fun a =>
    let ta := m.functor (.atom a.id)
    { id := { name := .pair a.id.name (.arrow (.app (.root "T") a.id.name) a.id.name (.root "α"))
              kind := .sort }
      description := s!"T-algebra ({a.id.name}, α : T({a.id.name}) → {a.id.name})" }

  -- Structure maps: α_A : TA → A for each algebra
  let structureMaps := m.base.objects.map fun a =>
    let ta := m.functor (.atom a.id)
    let algName := .pair a.id.name (.arrow (.app (.root "T") a.id.name) a.id.name (.root "α"))
    { id := { name := .nested algName "α", kind := .morphism }
      domain := ta
      codomain := .atom a.id
      description := s!"Structure map α : T({a.id.name}) → {a.id.name}" }

  -- Algebra homomorphisms: for each base morphism f : A → B,
  -- an algebra homomorphism (A, a) → (B, b) when f ∘ a = b ∘ T(f)
  let homomorphisms := m.base.morphisms.map fun f =>
    let domAlg := match f.domain with
      | .atom g => .pair g.name (.arrow (.app (.root "T") g.name) g.name (.root "α"))
      | _ => .root "?"
    let codAlg := match f.codomain with
      | .atom g => .pair g.name (.arrow (.app (.root "T") g.name) g.name (.root "α"))
      | _ => .root "?"
    { id := { name := .app (.root "hom") f.id.name, kind := .morphism }
      domain := .atom { name := domAlg, kind := .sort }
      codomain := .atom { name := codAlg, kind := .sort }
      description := s!"Algebra homomorphism from {f.id.name}" }

  -- Unit laws: α ∘ η = id for each algebra
  let unitLaws := m.base.objects.map fun a =>
    let algName := .pair a.id.name (.arrow (.app (.root "T") a.id.name) a.id.name (.root "α"))
    let αId := { name := .nested algName "α", kind := .morphism }
    { id := gid s!"unit_law_{a.id.name}"
      leftPath := .comp (.atom m.unit) (.atom αId)
      rightPath := .id (.atom a.id)
      description := s!"Unit law: α ∘ η = id for {a.id.name}" }

  -- Associativity laws: α ∘ μ = α ∘ T(α) for each algebra
  let assocLaws := m.base.objects.map fun a =>
    let algName := .pair a.id.name (.arrow (.app (.root "T") a.id.name) a.id.name (.root "α"))
    let αId := { name := .nested algName "α", kind := .morphism }
    { id := gid s!"assoc_law_{a.id.name}"
      leftPath := .comp (.atom m.mult) (.atom αId)
      rightPath := .comp (m.functor (.atom αId)) (.atom αId)
      description := s!"Associativity: α ∘ μ = α ∘ T(α) for {a.id.name}" }

  -- Homomorphism axioms: f ∘ α_A = α_B ∘ T(f) for each base morphism
  let homAxioms := m.base.morphisms.map fun f =>
    let domAlg := match f.domain with
      | .atom g => .pair g.name (.arrow (.app (.root "T") g.name) g.name (.root "α"))
      | _ => .root "?"
    let codAlg := match f.codomain with
      | .atom g => .pair g.name (.arrow (.app (.root "T") g.name) g.name (.root "α"))
      | _ => .root "?"
    let αA := { name := .nested domAlg "α", kind := .morphism }
    let αB := { name := .nested codAlg "α", kind := .morphism }
    let homF := { name := .app (.root "hom") f.id.name, kind := .morphism }
    { id := gid s!"hom_compat_{f.id.name}"
      leftPath := .comp (.atom αA) (.atom homF)
      rightPath := .comp (m.functor (.atom homF)) (.atom αB)
      description := s!"Homomorphism condition: f ∘ α_A = α_B ∘ T(f) for {f.id.name}" }

  { name := s!"{m.base.name}^T"
    doctrine := m.base.doctrine
    objects := emObjects
    morphisms := structureMaps ++ homomorphisms
    axioms := unitLaws ++ assocLaws ++ homAxioms }

end CatLab
