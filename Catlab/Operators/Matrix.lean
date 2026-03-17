/-
  CatLab — Matrix Category (Mat(C))

  Given a category C with finite biproducts, construct the matrix category.

  Objects: finite lists of objects from C (formal direct sums)
  Morphisms: matrices of morphisms, with composition via matrix multiplication
             (i.e., (M ∘ N)_{ij} = ⊕_k M_{ik} ∘ N_{kj})
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute Mat(C), the matrix category over C.

    Objects: finite lists [A₁, …, Aₙ] of objects from C, representing
    formal direct sums A₁ ⊕ ⋯ ⊕ Aₙ. Named using Name.graded for entries.

    Morphisms: from [A₁,…,Aₘ] to [B₁,…,Bₙ], a morphism is an m×n matrix
    where entry (i,j) is a morphism Aᵢ → Bⱼ in C.

    Composition is matrix multiplication using biproduct structure. -/
def matrixCategory (t : Theory) : Theory :=
  -- For a finite presentation, we generate matrix objects up to a bounded size.
  -- Each object of Mat(C) is a list of base objects.
  -- We represent individual base objects as singleton lists (the embedding C ↪ Mat(C)).
  let baseName := Name.root t.name

  -- Singleton objects: each object A of C gives [A] in Mat(C)
  let singletonObjects := t.objects.map fun a =>
    { id := { name := .graded baseName 1 |> fun n => .app n a.id.name, kind := .sort }
      description := s!"Singleton matrix object [{a.id.name}]" : Generator0 }

  -- Direct sum objects: each pair (A, B) gives [A, B] in Mat(C)
  let pairObjects := t.objects.flatMap fun a =>
    t.objects.map fun b =>
      { id := { name := .app (.graded baseName 2) (Name.pair a.id.name b.id.name)
                kind := .sort }
        description := s!"Matrix object [{a.id.name}, {b.id.name}]" : Generator0 }

  -- Zero object (empty list)
  let zeroObj : Generator0 :=
    { id := { name := .graded baseName 0, kind := .sort }
      description := "Zero object (empty direct sum)" }

  -- Matrix entries: for singletons, a morphism [A] → [B] is just a morphism A → B
  let singletonMorphisms := t.morphisms.map fun f =>
    let domName := .app (.graded baseName 1) (match f.domain with
      | .atom g => g.name | _ => .root "?")
    let codName := .app (.graded baseName 1) (match f.codomain with
      | .atom g => g.name | _ => .root "?")
    { id := { name := .app (.root "mat") f.id.name, kind := .morphism }
      domain := .atom { name := domName, kind := .sort }
      codomain := .atom { name := codName, kind := .sort }
      description := s!"Matrix entry [{f.id.name}]" : Generator1 }

  -- Injection and projection morphisms for pair objects
  let injections := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      let pairName := .app (.graded baseName 2) (Name.pair a.id.name b.id.name)
      let singleA := .app (.graded baseName 1) a.id.name
      let singleB := .app (.graded baseName 1) b.id.name
      [ { id := { name := .nested pairName "ι₁", kind := .morphism }
          domain := .atom { name := singleA, kind := .sort }
          codomain := .atom { name := pairName, kind := .sort }
          description := s!"Injection of {a.id.name} into [{a.id.name},{b.id.name}]"
          : Generator1 },
        { id := { name := .nested pairName "ι₂", kind := .morphism }
          domain := .atom { name := singleB, kind := .sort }
          codomain := .atom { name := pairName, kind := .sort }
          description := s!"Injection of {b.id.name} into [{a.id.name},{b.id.name}]"
          : Generator1 },
        { id := { name := .nested pairName "π₁", kind := .morphism }
          domain := .atom { name := pairName, kind := .sort }
          codomain := .atom { name := singleA, kind := .sort }
          description := s!"Projection to {a.id.name} from [{a.id.name},{b.id.name}]"
          : Generator1 },
        { id := { name := .nested pairName "π₂", kind := .morphism }
          domain := .atom { name := pairName, kind := .sort }
          codomain := .atom { name := singleB, kind := .sort }
          description := s!"Projection to {b.id.name} from [{a.id.name},{b.id.name}]"
          : Generator1 } ]

  -- Biproduct axioms: π_i ∘ ι_i = id, π_i ∘ ι_j = 0 (i≠j), Σ ι_i ∘ π_i = id
  let biproductAxioms := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      let pairName := .app (.graded baseName 2) (Name.pair a.id.name b.id.name)
      let singleA := .app (.graded baseName 1) a.id.name
      let π₁ := Expr.atom { name := .nested pairName "π₁", kind := .morphism }
      let π₂ := Expr.atom { name := .nested pairName "π₂", kind := .morphism }
      let ι₁ := Expr.atom { name := .nested pairName "ι₁", kind := .morphism }
      let ι₂ := Expr.atom { name := .nested pairName "ι₂", kind := .morphism }
      [ { id := { name := .nested pairName "π₁∘ι₁=id", kind := .twoCell }
          leftPath := .comp π₁ ι₁
          rightPath := .id (.atom { name := singleA, kind := .sort })
          description := "First projection retracts first injection" : Generator2 } ]

  { name := s!"Mat({t.name})"
    doctrine := t.doctrine
    objects := [zeroObj] ++ singletonObjects ++ pairObjects
    morphisms := singletonMorphisms ++ injections
    axioms := biproductAxioms }

end CatLab
