/-
  CatLab — Lawvere Theory Models

  Given a Lawvere theory T (a category with finite products) and a target
  category C (also with finite products), Mod(T, C) is the category of
  product-preserving functors T → C.

  Objects: models — assignments of C-objects to T-sorts and C-morphisms to T-operations
  Morphisms: natural transformations (homomorphisms of models)

  Special case: Mod(T, Set) is the "variety of algebras" presented by T.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab

/-- Compute the category of models Mod(T, C) for a Lawvere theory T in a target category C.

    A model M : T → C assigns:
    - To each sort s of T, an object M(s) of C
    - To each operation f : s₁ × ... × sₙ → s of T, a morphism M(f) : M(s₁) × ... × M(sₙ) → M(s)
    preserving finite products.

    A homomorphism α : M → N is a natural transformation: for each sort s,
    a morphism αₛ : M(s) → N(s) commuting with all operations. -/
def lawvereModelCategory (lawvereTheory target : Theory) : Theory :=
  -- Objects: two generic models M and N (representing the hom-set)
  let modelObj := { id := gid s!"Mod({lawvereTheory.name},{target.name})"
                    description := s!"Category of models of {lawvereTheory.name} in {target.name}" }

  -- For each sort s in T, a model M assigns an object M(s) in C
  -- We represent components of the model as morphism generators
  -- For each operation f : dom → cod in T, M(f) is a morphism M(dom) → M(cod)
  let modelMorphisms := lawvereTheory.morphisms.map fun f =>
    { id := gid s!"M({f.id.name})"
      domain := .atom (gid s!"M({repr f.domain})")
      codomain := .atom (gid s!"M({repr f.codomain})")
      description := s!"Model image of {f.id.name}" }

  -- Natural transformation components: for each sort s of T,
  -- α_s : M(s) → N(s)
  let natTransComponents := lawvereTheory.objects.map fun s =>
    { id := gid s!"α_{s.id.name}"
      domain := .atom (gid s!"M({s.id.name})")
      codomain := .atom (gid s!"N({s.id.name})")
      description := s!"Homomorphism component at sort {s.id.name}" }

  -- Naturality axioms: for each operation f : dom → cod in T,
  -- N(f) ∘ α_dom = α_cod ∘ M(f)
  let naturalityAxioms := lawvereTheory.morphisms.map fun f =>
    { id := gid s!"naturality_{f.id.name}"
      leftPath := .comp (.atom (gid s!"α_{repr f.domain}"))
                        (.atom (gid s!"N({f.id.name})"))
      rightPath := .comp (.atom (gid s!"M({f.id.name})"))
                         (.atom (gid s!"α_{repr f.codomain}"))
      description := s!"Naturality: N({f.id.name}) ∘ α = α ∘ M({f.id.name})" }

  -- Product preservation axioms: M preserves products
  -- For each pair of sorts s₁, s₂, M(s₁ × s₂) = M(s₁) × M(s₂)
  let productAxioms := lawvereTheory.objects.flatMap fun s1 =>
    lawvereTheory.objects.map fun s2 =>
      { id := gid s!"prod_pres_{s1.id.name}_{s2.id.name}"
        leftPath := .atom (gid s!"M({s1.id.name}×{s2.id.name})")
        rightPath := .prod (.atom (gid s!"M({s1.id.name})"))
                           (.atom (gid s!"M({s2.id.name})"))
        description := s!"Product preservation: M({s1.id.name} × {s2.id.name}) = M({s1.id.name}) × M({s2.id.name})" }

  -- Terminal preservation: M(1) = 1
  let terminalAxiom : Generator2 :=
    { id := gid "terminal_pres"
      leftPath := .atom (gid "M(terminal)")
      rightPath := .terminal
      description := "Product preservation: M(1) = 1" }

  -- Rewrite axioms from T into model axioms
  let rewriteToModel (e : Expr) : Expr := match e with
    | .atom g =>
      if lawvereTheory.morphisms.any (fun m => m.id == g)
      then .atom (gid s!"M({g.name})")
      else e
    | other => other
  let theoryAxioms := lawvereTheory.axioms.map fun ax =>
    { id := gid s!"model_{ax.id.name}"
      leftPath := ax.leftPath.mapAtoms rewriteToModel
      rightPath := ax.rightPath.mapAtoms rewriteToModel
      description := s!"Model satisfies: {ax.id.name}" }

  { name := s!"Mod({lawvereTheory.name}, {target.name})"
    doctrine := target.doctrine
    objects := [modelObj]
    morphisms := modelMorphisms ++ natTransComponents
    axioms := naturalityAxioms ++ productAxioms ++ [terminalAxiom] ++ theoryAxioms }

/-- The category of set-valued models: Mod(T, Set).
    This is the "variety of algebras" for the Lawvere theory T —
    e.g., if T is the theory of groups, this gives Grp. -/
def algebraCategory (lawvereTheory : Theory) : Theory :=
  let setTheory : Theory :=
    { name := "Set"
      doctrine := { doctrine := .CartesianClosed }
      objects := [{ id := gid "Set", description := "The category of sets" }]
      morphisms := []
      axioms := [] }
  let result := lawvereModelCategory lawvereTheory setTheory
  { result with
    name := s!"Alg({lawvereTheory.name})"
    doctrine := { doctrine := .CartesianClosed } }

end CatLab
