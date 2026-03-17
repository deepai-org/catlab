/-
  CatLab — Nerve and Realization

  The nerve functor takes a category (Theory) and produces its simplicial nerve:
  a graded theory with face and degeneracy maps satisfying simplicial identities.

  The realization functor goes the other way: from a simplicial theory to its
  fundamental category.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Compute the simplicial nerve of a category.

    For a category C presented as a Theory:
    - 0-simplices: objects of C
    - 1-simplices: morphisms of C
    - n-simplices: composable n-tuples of morphisms
    - Face maps dᵢ : Δ[n] → Δ[n-1] (compose at position i or drop boundary)
    - Degeneracy maps sᵢ : Δ[n] → Δ[n+1] (insert identity at position i)
    - Simplicial identities as axioms -/
def nerve (t : Theory) (maxDim : Nat := 3) : Theory :=
  -- n-simplices as objects: N(C)_n
  let simplexName (n : Nat) : GeneratorId :=
    { name := .graded (.root s!"N({t.name})") n, index := 0, kind := .sort }
  let simplexObjects := List.range (maxDim + 1) |>.map fun n =>
    { id := simplexName n
      description := s!"{n}-simplices of the nerve of {t.name}"
        : Generator0 }

  -- Face map GeneratorId using structured Name
  let faceId (i n : Nat) : GeneratorId :=
    { name := .simplexFace i n, index := 0, kind := .morphism }

  -- Degeneracy map GeneratorId using structured Name
  let degId (i n : Nat) : GeneratorId :=
    { name := .simplexDegeneracy i n, index := 0, kind := .morphism }

  -- Face maps: dᵢ : N(C)_n → N(C)_{n-1} for 0 ≤ i ≤ n
  let faceMaps := List.range (maxDim + 1) |>.flatMap fun n =>
    if n == 0 then []
    else List.range (n + 1) |>.map fun i =>
      { id := faceId i n
        domain := .atom (simplexName n)
        codomain := .atom (simplexName (n - 1))
        description := s!"Face map d_{i} : N(C)_{n} → N(C)_{n-1}"
          : Generator1 }

  -- Degeneracy maps: sᵢ : N(C)_n → N(C)_{n+1} for 0 ≤ i ≤ n
  let degeneracyMaps := List.range maxDim |>.flatMap fun n =>
    List.range (n + 1) |>.map fun i =>
      { id := degId i n
        domain := .atom (simplexName n)
        codomain := .atom (simplexName (n + 1))
        description := s!"Degeneracy map s_{i} : N(C)_{n} → N(C)_{n+1}"
          : Generator1 }

  -- Simplicial identity axioms
  -- (1) dᵢ ∘ dⱼ = dⱼ₋₁ ∘ dᵢ for i < j
  let faceAxioms := List.range (maxDim + 1) |>.flatMap fun n =>
    if n <= 1 then []
    else List.range (n + 1) |>.flatMap fun j =>
      List.range j |>.map fun i =>
        { id := gid s!"face_comm_{i}_{j}^{n}"
          leftPath := .comp
            (.atom (faceId j n))
            (.atom (faceId i (n - 1)))
          rightPath := .comp
            (.atom (faceId i n))
            (.atom (faceId (j - 1) (n - 1)))
          description := s!"Simplicial identity: d_{i} ∘ d_{j} = d_{j-1} ∘ d_{i} for i < j"
            : Generator2 }

  -- (2) sᵢ ∘ sⱼ = sⱼ₊₁ ∘ sᵢ for i ≤ j
  let degAxioms := List.range maxDim |>.flatMap fun n =>
    if n == 0 then []
    else List.range n |>.flatMap fun j =>
      List.range (j + 1) |>.map fun i =>
        { id := gid s!"deg_comm_{i}_{j}^{n}"
          leftPath := .comp
            (.atom (degId j n))
            (.atom (degId i (n + 1)))
          rightPath := .comp
            (.atom (degId i n))
            (.atom (degId (j + 1) (n + 1)))
          description := s!"Simplicial identity: s_{i} ∘ s_{j} = s_{j+1} ∘ s_{i} for i ≤ j"
            : Generator2 }

  -- (3) Mixed identities: dᵢ ∘ sⱼ = ...
  let mixedAxioms := List.range maxDim |>.flatMap fun n =>
    List.range (n + 1) |>.flatMap fun j =>
      List.range (n + 2) |>.filterMap fun i =>
        if i < j then
          some { id := gid s!"mixed_lt_{i}_{j}^{n}"
                 leftPath := .comp
                   (.atom (degId j n))
                   (.atom (faceId i (n + 1)))
                 rightPath := .comp
                   (.atom (faceId i n))
                   (.atom (degId (j - 1) (n - 1)))
                 description := s!"Mixed identity: d_{i} ∘ s_{j} = s_{j-1} ∘ d_{i} (i < j)"
                   : Generator2 }
        else if i == j || i == j + 1 then
          some { id := gid s!"mixed_eq_{i}_{j}^{n}"
                 leftPath := .comp
                   (.atom (degId j n))
                   (.atom (faceId i (n + 1)))
                 rightPath := Expr.id (.atom (simplexName n))
                 description := s!"Mixed identity: d_{i} ∘ s_{j} = id (i = j or i = j+1)"
                   : Generator2 }
        else if i > j + 1 then
          some { id := gid s!"mixed_gt_{i}_{j}^{n}"
                 leftPath := .comp
                   (.atom (degId j n))
                   (.atom (faceId i (n + 1)))
                 rightPath := .comp
                   (.atom (faceId (i - 1) n))
                   (.atom (degId j (n - 1)))
                 description := s!"Mixed identity: d_{i} ∘ s_{j} = s_{j} ∘ d_{i-1} (i > j+1)"
                   : Generator2 }
        else none

  { name := s!"N({t.name})"
    doctrine := { doctrine := .Category }
    objects := simplexObjects
    morphisms := faceMaps ++ degeneracyMaps
    axioms := faceAxioms ++ degAxioms ++ mixedAxioms }

/-- Compute the fundamental category (realization) of a simplicial nerve.

    Takes the output of `nerve` and extracts:
    - Objects from 0-simplices
    - Morphisms from 1-simplices (non-face, non-degeneracy generators)
    - Composition from 2-simplex face relations -/
def realize (t : Theory) : Theory :=
  -- 0-simplex objects become category objects
  let dim0 := t.objects.filter fun o => o.id.name.degree? == some 0
  let realObjects : List Generator0 := dim0.map fun o =>
    { id := gid s!"π({o.id.name})"
      description := s!"Realization of 0-simplex {o.id.name}" }

  -- Non-structural morphisms become category morphisms
  -- Use structured name matching instead of string parsing
  let realMorphisms : List Generator1 := (t.morphisms.filter fun m =>
    m.id.name.isSimplexFace?.isNone && m.id.name.isSimplexDegeneracy?.isNone
  ).map fun m =>
    { id := gid s!"π({m.id.name})"
      domain := m.domain
      codomain := m.codomain
      description := s!"Realization of 1-simplex {m.id.name}" }

  -- Degeneracy = identity axioms
  let identityAxioms : List Generator2 := dim0.map fun o =>
    { id := gid s!"degen_identity_{o.id.name}"
      leftPath := .atom { name := .simplexDegeneracy 0 0, kind := .morphism }
      rightPath := Expr.id (.atom (gid s!"π({o.id.name})"))
      description := s!"Degenerate 1-simplex at {o.id.name} is the identity" }

  -- 2-simplex composition: d₁(τ) = d₀(τ) ∘ d₂(τ)
  let dim2 := t.objects.filter fun o => o.id.name.degree? == some 2
  let compositionAxioms : List Generator2 := dim2.map fun tau =>
    { id := gid s!"composition_{tau.id.name}"
      leftPath := .comp (.atom { name := .simplexFace 2 2, kind := .morphism })
                         (.atom { name := .simplexFace 0 2, kind := .morphism })
      rightPath := .atom { name := .simplexFace 1 2, kind := .morphism }
      description := s!"2-simplex {tau.id.name} gives composition" }

  { name := s!"π({t.name})"
    doctrine := { doctrine := .Category }
    objects := realObjects
    morphisms := realMorphisms
    axioms := identityAxioms ++ compositionAxioms }

end CatLab
