/-
  CatLab — Realizability Topos

  Constructs the realizability topos from a Partial Combinatory Algebra (PCA).

  Objects are "assemblies": sets equipped with a realizability relation
  assigning to each element a nonempty set of realizers from the PCA.
  Morphisms are functions tracked by a realizer.

  Includes the subobject classifier Ω of realized propositions.
-/

import Catlab.Core.Theory

namespace CatLab

/-- A Partial Combinatory Algebra (PCA): a set A with partial application
    and combinators K and S satisfying the usual axioms.

    K a b = a  (constant combinator)
    S a b c = (a c) (b c)  (substitution combinator) -/
structure PCA where
  /-- Name of the PCA -/
  name : String
  /-- The carrier set, represented as a theory with a single sort -/
  carrier : Theory
  /-- The combinator K (constant) -/
  kComb : GeneratorId
  /-- The combinator S (substitution) -/
  sComb : GeneratorId

/-- An assembly over a PCA: a set |X| together with a realizability
    relation ⦃-⦄ : |X| → P(A) assigning realizers to elements. -/
structure Assembly where
  /-- Name of the assembly -/
  name : String
  /-- The underlying set (as a sort) -/
  underlyingSet : GeneratorId
  /-- The realizability map: each element has a nonempty set of realizers -/
  realizability : GeneratorId

/-- Construct the realizability topos from a PCA.

    Objects: assemblies (|X|, ⦃-⦄ : |X| → P(A))
    Morphisms: tracked functions — f : X → Y tracked by realizer e ∈ A,
               meaning for all x ∈ X and all a ∈ ⦃x⦄, e·a is defined and e·a ∈ ⦃f(x)⦄
    Includes: subobject classifier Ω, terminal object, products. -/
def realizabilityTopos (pca : PCA) : Theory :=
  -- The PCA carrier as an assembly over itself (the "generic" assembly)
  let carrierAssembly : Generator0 :=
    { id := ⟨s!"Asm({pca.name})", 0⟩
      description := s!"PCA carrier {pca.name} as assembly over itself" }

  -- Terminal object: one-element set, realized by K
  let terminalObj : Generator0 :=
    { id := ⟨"1", 0⟩
      description := "Terminal assembly: one element, realized by K" }

  -- Subobject classifier Ω: realized propositions
  -- Elements are "realizability predicates" i.e. subsets of A
  -- ⦃p⦄ = p itself (a proposition is realized by its own realizers)
  let omega : Generator0 :=
    { id := ⟨"Ω_rt", 0⟩
      description := "Subobject classifier: realized propositions (subsets of A)" }

  -- Natural number object (PCAs give rise to toposes with NNO)
  let natObj : Generator0 :=
    { id := ⟨"N_rt", 0⟩
      description := "Natural number object in the realizability topos" }

  -- True: 1 → Ω (the total predicate, realized by K)
  let trueMap : Generator1 :=
    { id := ⟨"⊤_rt", 0⟩
      domain := .terminal
      codomain := .atom ⟨"Ω_rt", 0⟩
      description := "True morphism: the always-realized proposition" }

  -- Application morphism: A × A → A (partial, but we model it as total on its domain)
  let appMorphism : Generator1 :=
    { id := ⟨"app", 0⟩
      domain := .prod (.atom ⟨s!"Asm({pca.name})", 0⟩)
                      (.atom ⟨s!"Asm({pca.name})", 0⟩)
      codomain := .atom ⟨s!"Asm({pca.name})", 0⟩
      description := "Partial application in the PCA" }

  -- K combinator as a global element
  let kMap : Generator1 :=
    { id := ⟨"K_elem", 0⟩
      domain := .terminal
      codomain := .atom ⟨s!"Asm({pca.name})", 0⟩
      description := "K combinator as global element" }

  -- S combinator as a global element
  let sMap : Generator1 :=
    { id := ⟨"S_elem", 0⟩
      domain := .terminal
      codomain := .atom ⟨s!"Asm({pca.name})", 0⟩
      description := "S combinator as global element" }

  -- Characteristic morphism: for each mono, a map to Ω
  let charMap : Generator1 :=
    { id := ⟨"char_rt", 0⟩
      domain := .atom ⟨s!"Asm({pca.name})", 0⟩
      codomain := .atom ⟨"Ω_rt", 0⟩
      description := "Generic characteristic morphism to Ω" }

  -- K axiom: K a b = a
  let kAxiom : Generator2 :=
    { id := ⟨"K_axiom", 0⟩
      leftPath := .comp (.atom ⟨"K_elem", 0⟩)
                        (.comp (.atom ⟨"app", 0⟩) (.atom ⟨"app", 0⟩))
      rightPath := .proj 0 (.prod (.atom ⟨s!"Asm({pca.name})", 0⟩)
                                   (.atom ⟨s!"Asm({pca.name})", 0⟩))
      description := "K combinator axiom: K a b = a" }

  -- S axiom: S a b c = (a c)(b c)
  let sAxiom : Generator2 :=
    { id := ⟨"S_axiom", 0⟩
      leftPath := .comp (.atom ⟨"S_elem", 0⟩)
                        (.comp (.atom ⟨"app", 0⟩)
                               (.comp (.atom ⟨"app", 0⟩) (.atom ⟨"app", 0⟩)))
      rightPath := .comp (.atom ⟨"app", 0⟩) (.atom ⟨"app", 0⟩)
      description := "S combinator axiom: S a b c = (a c)(b c)" }

  -- Subobject classifier axiom
  let omegaAxiom : Generator2 :=
    { id := ⟨"subobj_classifier_rt", 0⟩
      leftPath := .comp (.atom ⟨"mono", 0⟩) (.atom ⟨"char_rt", 0⟩)
      rightPath := .comp (.atom ⟨"!_rt", 0⟩) (.atom ⟨"⊤_rt", 0⟩)
      description := "Subobject classifier: monos correspond to maps to Ω" }

  { name := s!"RT({pca.name})"
    doctrine := { doctrine := .Topos }
    objects := [carrierAssembly, terminalObj, omega, natObj]
    morphisms := [trueMap, appMorphism, kMap, sMap, charMap]
    axioms := [kAxiom, sAxiom, omegaAxiom] }

/-- The Kleene first algebra: the standard PCA on natural numbers
    with partial recursive application. -/
def kleeneFirstAlgebra : PCA :=
  { name := "K₁"
    carrier :=
      { name := "ℕ"
        doctrine := { doctrine := .Category }
        objects := [{ id := ⟨"ℕ", 0⟩, description := "Natural numbers" }]
        morphisms := []
        axioms := [] }
    kComb := ⟨"K", 0⟩
    sComb := ⟨"S", 0⟩ }

/-- The effective topos: the realizability topos over Kleene's first algebra.
    This is the "home" of computable mathematics. -/
def effectiveTopos : Theory := realizabilityTopos kleeneFirstAlgebra

end CatLab
