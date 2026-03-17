/-
  CatLab — Partial Equivalence Relations (PERs)

  The category of PERs over a Partial Combinatory Algebra (PCA).

  Objects are partial equivalence relations on the PCA carrier: symmetric
  and transitive (but not necessarily reflexive) relations on A × A.
  Morphisms are realizer-tracked functions respecting the PER.

  PER(A) is a regular category and in fact a quasitopos. It sits between
  the realizability topos and the category of assemblies via a canonical chain:
    PER(A) → Asm(A) → RT(A)
-/

import Catlab.Core.Theory
import Catlab.Operators.Realizability

namespace CatLab

/-- A partial equivalence relation on a PCA carrier: a symmetric, transitive
    relation. The domain of the PER (elements related to themselves) determines
    the "extent" of the type it represents. -/
structure PERObj where
  /-- Name of this PER -/
  name : String
  /-- The symmetry witness: a realizer s such that a ~R b implies s·a ~R b ~R a -/
  symmetryRealizer : GeneratorId
  /-- The transitivity witness: a realizer t such that a ~R b and b ~R c
      implies (t·a·b·c) witnesses a ~R c -/
  transitivityRealizer : GeneratorId
  deriving Repr, Inhabited

/-- Construct the category of PERs over a PCA.

    Objects: PERs on the carrier A — each given by (symmetry realizer, transitivity realizer).
    Morphisms: tracked functions — f : R → S tracked by realizer e ∈ A meaning
               for all a, b: a R b → (e·a) S (e·b).
    The theory includes:
    - Symmetry and transitivity axioms for each PER
    - Composition of tracked functions (via the S combinator)
    - Identity tracked function (via the identity combinator SKK)
    - The canonical functor PER → Asm sending R to its domain -/
def perCategory (pca : PCA) : Theory :=
  let carrierName := s!"A({pca.name})"

  -- The generic PER object: a relation on A × A
  let perObj : Generator0 :=
    { id := gid s!"PER({pca.name})"
      description := s!"Generic PER on {pca.name}" }

  -- The domain/extent: {a ∈ A | a R a} — the set of self-related elements
  let domainObj : Generator0 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "dom"
              kind := .sort }
      description := "Domain of a PER: elements related to themselves" }

  -- The relation morphism: A × A → Ω (the PER as a predicate)
  let perRelation : Generator1 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "rel"
              kind := .morphism }
      domain := .prod (.atom (gid carrierName)) (.atom (gid carrierName))
      codomain := .atom (gid "Ω_per")
      description := "The PER relation as a morphism to truth values" }

  -- Symmetry morphism: a realizer witnessing a~b → b~a
  let symMorphism : Generator1 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "sym"
              kind := .morphism }
      domain := .atom (gid carrierName)
      codomain := .atom (gid carrierName)
      description := "Symmetry realizer: witnesses a~b → b~a" }

  -- Transitivity morphism: a realizer witnessing a~b ∧ b~c → a~c
  let transMorphism : Generator1 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "trans"
              kind := .morphism }
      domain := .prod (.atom (gid carrierName)) (.atom (gid carrierName))
      codomain := .atom (gid carrierName)
      description := "Transitivity realizer: witnesses a~b ∧ b~c → a~c" }

  -- Identity tracked morphism: SKK witnesses id : R → R
  let idTracked : Generator1 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "id_tracked"
              kind := .morphism }
      domain := .atom (gid s!"PER({pca.name})")
      codomain := .atom (gid s!"PER({pca.name})")
      description := "Identity morphism tracked by SKK" }

  -- Composition of tracked morphisms: S combinator composes realizers
  let compTracked : Generator1 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "comp_tracked"
              kind := .morphism }
      domain := .prod (.atom (gid s!"PER({pca.name})"))
                      (.atom (gid s!"PER({pca.name})"))
      codomain := .atom (gid s!"PER({pca.name})")
      description := "Composition of tracked morphisms via S combinator" }

  -- Truth values for PERs
  let omegaPer : Generator0 :=
    { id := gid "Ω_per"
      description := "Truth-value object for PER category" }

  -- Equality PER: the discrete PER where a~b iff a=b
  let eqPer : Generator0 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "eq"
              kind := .sort }
      description := "Equality PER (discrete): a ~ b iff a = b in the PCA" }

  -- Symmetry axiom: sym witnesses a~b → b~a
  let symAxiom : Generator2 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "sym_ax"
              kind := .twoCell }
      leftPath := .comp (.atom perRelation.id)
                        (.atom symMorphism.id)
      rightPath := .comp (.atom (gid "swap"))
                         (.atom perRelation.id)
      description := "Symmetry: R(a,b) implies R(b,a) via symmetry realizer" }

  -- Transitivity axiom
  let transAxiom : Generator2 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "trans_ax"
              kind := .twoCell }
      leftPath := .comp (.prod (.atom perRelation.id) (.atom perRelation.id))
                        (.atom transMorphism.id)
      rightPath := .atom perRelation.id
      description := "Transitivity: R(a,b) ∧ R(b,c) implies R(a,c)" }

  -- Identity tracking axiom: SKK · a ~ a for all a in dom(R)
  let idTrackAxiom : Generator2 :=
    { id := { name := .nested (.root s!"PER({pca.name})") "id_track_ax"
              kind := .twoCell }
      leftPath := .atom idTracked.id
      rightPath := .id (.atom (gid s!"PER({pca.name})"))
      description := "Identity tracking: SKK realizes the identity function" }

  -- Canonical functor: PER → Asm, sending R ↦ (dom(R), realizability from R)
  let perToAsm : FunctorDecl :=
    { id := gid s!"PER_to_Asm({pca.name})"
      source := .root s!"PER({pca.name})"
      target := .root s!"Asm({pca.name})"
      onObjects := .atom domainObj.id
      onMorphisms := .var "f"  -- tracked function restricts to domain
      description := "Canonical functor PER → Asm: R ↦ (dom(R), ⦃-⦄)" }

  { name := s!"PER({pca.name})"
    doctrine := { doctrine := .FinitelyComplete
                  constraints := ["regular", "quasitopos"] }
    objects := [perObj, domainObj, omegaPer, eqPer]
    morphisms := [perRelation, symMorphism, transMorphism,
                  idTracked, compTracked]
    axioms := [symAxiom, transAxiom, idTrackAxiom]
    functors := [perToAsm] }

/-- The PER category over Kleene's first algebra. -/
def perOverKleene : Theory := perCategory kleeneFirstAlgebra

end CatLab
