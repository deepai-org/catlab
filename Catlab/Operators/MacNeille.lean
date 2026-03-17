/-
  CatLab — MacNeille Completion

  Adjoins all meets and joins to a poset/category so that the original
  is dense and codense. The MacNeille completion of a poset P is the
  smallest complete lattice containing P as a dense sublattice.

  For each pair of objects (A, B) we add:
    - A formal meet A ∧ B with projections π₁, π₂ and universal property
    - A formal join A ∨ B with injections ι₁, ι₂ and universal property
    - Density axioms: each object is both a join of things below it
      and a meet of things above it
-/

import Catlab.Core.Theory

namespace CatLab

/-- MacNeille completion: freely adjoin all binary meets and joins,
    with density and codensity. -/
def macneilleCompletion (t : Theory) : Theory :=
  -- For each pair of objects (A, B), add meet A ∧ B and join A ∨ B
  let objectPairs := t.objects.flatMap fun a =>
    t.objects.map fun b => (a, b)

  -- Meet objects: A ∧ B
  let meetObjects := objectPairs.map fun (a, b) =>
    let meetName : Name := .pair a.id.name b.id.name
    ({ id := { name := .nested meetName "meet", kind := .sort }
       description := s!"{a.id.name} ∧ {b.id.name}" }
      : Generator0)

  -- Join objects: A ∨ B
  let joinObjects := objectPairs.map fun (a, b) =>
    let joinName : Name := .pair a.id.name b.id.name
    ({ id := { name := .nested joinName "join", kind := .sort }
       description := s!"{a.id.name} ∨ {b.id.name}" }
      : Generator0)

  -- Projections: π₁ : A∧B → A, π₂ : A∧B → B
  let pi1Morphisms := objectPairs.map fun (a, b) =>
    let meetId : GeneratorId :=
      { name := .nested (.pair a.id.name b.id.name) "meet", kind := .sort }
    ({ id := { name := .nested (.pair a.id.name b.id.name) "π₁", kind := .morphism }
       domain := .atom meetId
       codomain := .atom a.id
       description := s!"First projection from {a.id.name} ∧ {b.id.name}" }
      : Generator1)

  let pi2Morphisms := objectPairs.map fun (a, b) =>
    let meetId : GeneratorId :=
      { name := .nested (.pair a.id.name b.id.name) "meet", kind := .sort }
    ({ id := { name := .nested (.pair a.id.name b.id.name) "π₂", kind := .morphism }
       domain := .atom meetId
       codomain := .atom b.id
       description := s!"Second projection from {a.id.name} ∧ {b.id.name}" }
      : Generator1)

  -- Injections: ι₁ : A → A∨B, ι₂ : B → A∨B
  let iota1Morphisms := objectPairs.map fun (a, b) =>
    let joinId : GeneratorId :=
      { name := .nested (.pair a.id.name b.id.name) "join", kind := .sort }
    ({ id := { name := .nested (.pair a.id.name b.id.name) "ι₁", kind := .morphism }
       domain := .atom a.id
       codomain := .atom joinId
       description := s!"First injection into {a.id.name} ∨ {b.id.name}" }
      : Generator1)

  let iota2Morphisms := objectPairs.map fun (a, b) =>
    let joinId : GeneratorId :=
      { name := .nested (.pair a.id.name b.id.name) "join", kind := .sort }
    ({ id := { name := .nested (.pair a.id.name b.id.name) "ι₂", kind := .morphism }
       domain := .atom b.id
       codomain := .atom joinId
       description := s!"Second injection into {a.id.name} ∨ {b.id.name}" }
      : Generator1)

  -- Universal property of meets: for any C with f : C → A and g : C → B,
  -- there exists a unique ⟨f,g⟩ : C → A∧B such that π₁ ∘ ⟨f,g⟩ = f and π₂ ∘ ⟨f,g⟩ = g
  -- Expressed as an axiom schema quantified over f, g.
  let meetUnivAxioms := objectPairs.map fun (a, b) =>
    let pairName : Name := .pair a.id.name b.id.name
    let pi1Id : GeneratorId := { name := .nested pairName "π₁", kind := .morphism }
    let pi2Id : GeneratorId := { name := .nested pairName "π₂", kind := .morphism }
    ({ id := { name := .nested pairName "meet_univ", kind := .twoCell }
       quantifiers := [
         { name := "f", kind := .morphism },
         { name := "g", kind := .morphism },
         { name := "h", kind := .morphism }
       ]
       leftPath := .comp (.var "h") (.atom pi1Id)
       rightPath := .var "f"
       description := s!"Universal property of {a.id.name} ∧ {b.id.name}: π₁ ∘ h = f" }
      : Generator2)

  let meetUnivAxioms2 := objectPairs.map fun (a, b) =>
    let pairName : Name := .pair a.id.name b.id.name
    let pi2Id : GeneratorId := { name := .nested pairName "π₂", kind := .morphism }
    ({ id := { name := .nested pairName "meet_univ₂", kind := .twoCell }
       quantifiers := [
         { name := "f", kind := .morphism },
         { name := "g", kind := .morphism },
         { name := "h", kind := .morphism }
       ]
       leftPath := .comp (.var "h") (.atom pi2Id)
       rightPath := .var "g"
       description := s!"Universal property of {a.id.name} ∧ {b.id.name}: π₂ ∘ h = g" }
      : Generator2)

  -- Universal property of joins: for any C with f : A → C and g : B → C,
  -- there exists a unique [f,g] : A∨B → C such that [f,g] ∘ ι₁ = f and [f,g] ∘ ι₂ = g
  let joinUnivAxioms := objectPairs.map fun (a, b) =>
    let pairName : Name := .pair a.id.name b.id.name
    let iota1Id : GeneratorId := { name := .nested pairName "ι₁", kind := .morphism }
    ({ id := { name := .nested pairName "join_univ", kind := .twoCell }
       quantifiers := [
         { name := "f", kind := .morphism },
         { name := "g", kind := .morphism },
         { name := "h", kind := .morphism }
       ]
       leftPath := .comp (.atom iota1Id) (.var "h")
       rightPath := .var "f"
       description := s!"Universal property of {a.id.name} ∨ {b.id.name}: h ∘ ι₁ = f" }
      : Generator2)

  let joinUnivAxioms2 := objectPairs.map fun (a, b) =>
    let pairName : Name := .pair a.id.name b.id.name
    let iota2Id : GeneratorId := { name := .nested pairName "ι₂", kind := .morphism }
    ({ id := { name := .nested pairName "join_univ₂", kind := .twoCell }
       quantifiers := [
         { name := "f", kind := .morphism },
         { name := "g", kind := .morphism },
         { name := "h", kind := .morphism }
       ]
       leftPath := .comp (.atom iota2Id) (.var "h")
       rightPath := .var "g"
       description := s!"Universal property of {a.id.name} ∨ {b.id.name}: h ∘ ι₂ = g" }
      : Generator2)

  -- Density: for each object X, X = ∨{A : A ≤ X}
  -- We express this as: for each morphism f : A → X in the theory,
  -- the injection ι₁ composed with the join projection covers X.
  -- Formally: the join of all subobjects equals X.
  -- We encode density per-object as: the identity on X factors through
  -- the join of all objects mapping into X.
  let densityAxioms := t.objects.map fun x =>
    let pairName : Name := .pair x.id.name x.id.name
    let joinId : GeneratorId :=
      { name := .nested pairName "join", kind := .sort }
    let iota1Id : GeneratorId :=
      { name := .nested pairName "ι₁", kind := .morphism }
    -- Density: ι₁ : X → X∨X has a retraction, i.e., X∨X collapses to X
    -- Express as: there exists r : X∨X → X with r ∘ ι₁ = id_X
    ({ id := { name := .nested x.id.name "dense", kind := .twoCell }
       leftPath := .comp (.atom iota1Id)
                         (.atom { name := .nested pairName "fold", kind := .morphism })
       rightPath := Expr.id (.atom x.id)
       description := s!"Density: {x.id.name} is the join of its lower set" }
      : Generator2)

  -- Fold morphisms: fold : X∨X → X (the codiagonal)
  let foldMorphisms := t.objects.map fun x =>
    let pairName : Name := .pair x.id.name x.id.name
    let joinId : GeneratorId :=
      { name := .nested pairName "join", kind := .sort }
    ({ id := { name := .nested pairName "fold", kind := .morphism }
       domain := .atom joinId
       codomain := .atom x.id
       description := s!"Fold (codiagonal) for {x.id.name} ∨ {x.id.name} → {x.id.name}" }
      : Generator1)

  -- Codensity: for each object X, X = ∧{B : X ≤ B}
  -- Similarly, the diagonal Δ : X → X∧X with π₁ ∘ Δ = id_X
  let codensityAxioms := t.objects.map fun x =>
    let pairName : Name := .pair x.id.name x.id.name
    let pi1Id : GeneratorId :=
      { name := .nested pairName "π₁", kind := .morphism }
    ({ id := { name := .nested x.id.name "codense", kind := .twoCell }
       leftPath := .comp (.atom { name := .nested pairName "diag", kind := .morphism })
                         (.atom pi1Id)
       rightPath := Expr.id (.atom x.id)
       description := s!"Codensity: {x.id.name} is the meet of its upper set" }
      : Generator2)

  -- Diagonal morphisms: diag : X → X∧X
  let diagMorphisms := t.objects.map fun x =>
    let pairName : Name := .pair x.id.name x.id.name
    let meetId : GeneratorId :=
      { name := .nested pairName "meet", kind := .sort }
    ({ id := { name := .nested pairName "diag", kind := .morphism }
       domain := .atom x.id
       codomain := .atom meetId
       description := s!"Diagonal for {x.id.name} → {x.id.name} ∧ {x.id.name}" }
      : Generator1)

  { t with
    name := s!"MacNeille({t.name})"
    objects := t.objects ++ meetObjects ++ joinObjects
    morphisms := t.morphisms ++ pi1Morphisms ++ pi2Morphisms
                 ++ iota1Morphisms ++ iota2Morphisms
                 ++ foldMorphisms ++ diagMorphisms
    axioms := t.axioms ++ meetUnivAxioms ++ meetUnivAxioms2
              ++ joinUnivAxioms ++ joinUnivAxioms2
              ++ densityAxioms ++ codensityAxioms }

end CatLab
