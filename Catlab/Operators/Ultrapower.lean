/-
  CatLab — Ultrapower / Łoś's Transformation

  Given a theory C and an ultrafilter U on an index set I, constructs the
  internal ultrapower category C^I/U.

  Objects: for each object A, an ultrapower object A^I/U.
  Morphisms: for each morphism f, an ultrapower morphism f^I/U.
  Diagonal embedding: d_A : A → A^I/U for each object.
  Transfer axioms: by Łoś's theorem, every first-order property of C
  transfers to C^I/U.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Specification of an ultrafilter on an index set. -/
structure UltrafilterSpec where
  name : String
  indexSet : GeneratorId  -- the index set I

/-- Construct the ultrapower category C^I/U.

    For each object A in the base theory, we create the ultrapower object
    A^I/U (equivalence classes of I-indexed families of A-elements mod U).
    For each morphism f, we lift it pointwise to f^I/U.
    Diagonal embeddings d_A : A → A^I/U witness the elementary embedding. -/
def ultrapower (t : Theory) (uf : UltrafilterSpec) : Theory :=
  -- Ultrapower objects: A^I/U for each object A
  let ultraObjects : List Generator0 := t.objects.map fun a =>
    { id := { name := .app (.root "ultra") a.id.name, kind := .sort }
      description := s!"{a.id.name}^I/U under ultrafilter {uf.name}" }

  -- Ultrapower morphisms: f^I/U for each morphism f
  let ultraMorphisms : List Generator1 := t.morphisms.map fun f =>
    let domName := .app (.root "ultra") f.domain.toName
    let codName := .app (.root "ultra") f.codomain.toName
    { id := { name := .app (.root "ultra") f.id.name, kind := .morphism }
      domain := .atom { name := domName, kind := .sort }
      codomain := .atom { name := codName, kind := .sort }
      description := s!"{f.id.name}^I/U lifted morphism" }

  -- Diagonal embeddings: d_A : A → A^I/U for each object
  let diagonals : List Generator1 := t.objects.map fun a =>
    let ultraName := .app (.root "ultra") a.id.name
    { id := gid s!"d_{a.id.name}" (k := .morphism)
      domain := .atom a.id
      codomain := .atom { name := ultraName, kind := .sort }
      description := s!"Diagonal embedding {a.id.name} → {a.id.name}^I/U" }

  -- Diagonal naturality: for each morphism f : A → B,
  -- d_B ∘ f = f^I/U ∘ d_A
  let naturalityAxioms : List Generator2 := t.morphisms.map fun f =>
    let domObj := f.domain.toName
    let codObj := f.codomain.toName
    { id := gid s!"diag_nat_{f.id.name}" (k := .twoCell)
      leftPath := .comp (.atom (gid s!"d_{codObj}" (k := .morphism)))
                        (.atom f.id)
      rightPath := .comp (.atom { name := .app (.root "ultra") f.id.name, kind := .morphism })
                         (.atom (gid s!"d_{domObj}" (k := .morphism)))
      description := s!"Diagonal naturality: d_B ∘ f = f^I/U ∘ d_A for {f.id.name}" }

  -- Transfer axioms (Łoś's theorem): each axiom in the base theory
  -- lifts to the ultrapower
  let transferAxioms : List Generator2 := t.axioms.map fun ax =>
    let liftExpr (e : Expr) : Expr := match e with
      | .atom g => .atom { name := .app (.root "ultra") g.name, kind := g.kind }
      | .id obj => .id (liftExpr obj)
      | .comp f g => .comp (liftExpr f) (liftExpr g)
      | other => other
    { id := gid s!"los_{ax.id.name}" (k := .twoCell)
      leftPath := liftExpr ax.leftPath
      rightPath := liftExpr ax.rightPath
      description := s!"Łoś transfer of {ax.id.name}" }
  where
    liftExpr (e : Expr) : Expr := match e with
      | .atom g => .atom { name := .app (.root "ultra") g.name, kind := g.kind }
      | .id obj => .id (liftExpr obj)
      | .comp f g => .comp (liftExpr f) (liftExpr g)
      | other => other

  { name := s!"{t.name}^{uf.name}"
    doctrine := t.doctrine
    objects := t.objects ++ ultraObjects
    morphisms := t.morphisms ++ ultraMorphisms ++ diagonals
    axioms := t.axioms ++ naturalityAxioms ++ transferAxioms }

end CatLab
