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
  let modelObj := { id := ⟨s!"Mod({lawvereTheory.name},{target.name})", 0⟩
                    description := s!"Category of models of {lawvereTheory.name} in {target.name}" }

  -- For each sort s in T, a model M assigns an object M(s) in C
  -- We represent components of the model as morphism generators
  -- For each operation f : dom → cod in T, M(f) is a morphism M(dom) → M(cod)
  let modelMorphisms := lawvereTheory.morphisms.map fun f =>
    { id := ⟨s!"M({f.id.name})", 0⟩
      domain := .atom ⟨s!"M({repr f.domain})", 0⟩
      codomain := .atom ⟨s!"M({repr f.codomain})", 0⟩
      description := s!"Model image of {f.id.name}" }

  -- Natural transformation components: for each sort s of T,
  -- α_s : M(s) → N(s)
  let natTransComponents := lawvereTheory.objects.map fun s =>
    { id := ⟨s!"α_{s.id.name}", 0⟩
      domain := .atom ⟨s!"M({s.id.name})", 0⟩
      codomain := .atom ⟨s!"N({s.id.name})", 0⟩
      description := s!"Homomorphism component at sort {s.id.name}" }

  -- Naturality axioms: for each operation f : dom → cod in T,
  -- N(f) ∘ α_dom = α_cod ∘ M(f)
  let naturalityAxioms := lawvereTheory.morphisms.map fun f =>
    { id := ⟨s!"naturality_{f.id.name}", 0⟩
      leftPath := .comp (.atom ⟨s!"α_{repr f.domain}", 0⟩)
                        (.atom ⟨s!"N({f.id.name})", 0⟩)
      rightPath := .comp (.atom ⟨s!"M({f.id.name})", 0⟩)
                         (.atom ⟨s!"α_{repr f.codomain}", 0⟩)
      description := s!"Naturality: N({f.id.name}) ∘ α = α ∘ M({f.id.name})" }

  -- Product preservation axioms: M preserves products
  -- For each pair of sorts s₁, s₂, M(s₁ × s₂) = M(s₁) × M(s₂)
  let productAxioms := lawvereTheory.objects.flatMap fun s1 =>
    lawvereTheory.objects.map fun s2 =>
      { id := ⟨s!"prod_pres_{s1.id.name}_{s2.id.name}", 0⟩
        leftPath := .atom ⟨s!"M({s1.id.name}×{s2.id.name})", 0⟩
        rightPath := .prod (.atom ⟨s!"M({s1.id.name})", 0⟩)
                           (.atom ⟨s!"M({s2.id.name})", 0⟩)
        description := s!"Product preservation: M({s1.id.name} × {s2.id.name}) = M({s1.id.name}) × M({s2.id.name})" }

  -- Terminal preservation: M(1) = 1
  let terminalAxiom : Generator2 :=
    { id := ⟨"terminal_pres", 0⟩
      leftPath := .atom ⟨"M(terminal)", 0⟩
      rightPath := .terminal
      description := "Product preservation: M(1) = 1" }

  -- Rewrite axioms from T into model axioms
  let rewriteToModel (e : Expr) : Expr := match e with
    | .atom gid =>
      if lawvereTheory.morphisms.any (fun m => m.id == gid)
      then .atom ⟨s!"M({gid.name})", 0⟩
      else e
    | other => other
  let theoryAxioms := lawvereTheory.axioms.map fun ax =>
    { id := ⟨s!"model_{ax.id.name}", 0⟩
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
      objects := [{ id := ⟨"Set", 0⟩, description := "The category of sets" }]
      morphisms := []
      axioms := [] }
  let result := lawvereModelCategory lawvereTheory setTheory
  { result with
    name := s!"Alg({lawvereTheory.name})"
    doctrine := { doctrine := .CartesianClosed } }

end CatLab
