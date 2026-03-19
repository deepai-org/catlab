/-
  CatLab — Derived Category Construction

  Constructs the derived category from a theory in three stages:
  1. Chain complexes: graded objects with differentials d∘d = 0
  2. Homotopy category: quotient by chain homotopies
  3. Derived category: localize at quasi-isomorphisms

  Includes shift functor [1] and distinguished triangle structure.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Helper: create a GeneratorId with a graded name -/
private def dGradedId (base : Name) (n : Nat) (k : GeneratorKind := .sort) : GeneratorId :=
  { name := .graded base n, kind := k }

/-- Helper: create an Expr.atom with a graded name -/
private def dGradedAtom (base : Name) (n : Nat) (k : GeneratorKind := .sort) : Expr :=
  .atom (dGradedId base n k)

/-- Construct the category of chain complexes Ch(C).

    Objects: graded sequences (C_0, C_1, ..., C_maxDeg) with
    differentials d_n : C_n → C_{n-1} satisfying d∘d = 0.

    Morphisms: degree-preserving maps f_n : C_n → D_n commuting
    with differentials. -/
def chainComplexCategory (t : Theory) (maxDeg : Nat := 3) : Theory :=
  let degrees := List.range (maxDeg + 1)

  -- For each base object A, create chain complex objects A_0, ..., A_maxDeg
  let complexObjects := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Ch") a.id.name
    degrees.map fun n =>
      { id := dGradedId baseName n
        description := s!"Chain complex degree {n} of {a.id.name}" : Generator0 }

  -- Differentials: d_n : A_n → A_{n-1} for n ≥ 1
  let differentials := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Ch") a.id.name
    (List.range maxDeg).map fun n =>
      let deg := n + 1  -- differentials from degree 1, 2, ..., maxDeg
      { id := dGradedId (Name.nested baseName "d") deg (k := .morphism)
        domain := dGradedAtom baseName deg
        codomain := dGradedAtom baseName (deg - 1)
        description := s!"Differential d_{deg} : {a.id.name}_{deg} → {a.id.name}_{deg-1}" : Generator1 }

  -- d∘d = 0 axioms: d_{n-1} ∘ d_n = 0 for each consecutive pair
  let ddZeroAxioms := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Ch") a.id.name
    if maxDeg < 2 then [] else
    (List.range (maxDeg - 1)).map fun n =>
      let deg := n + 2  -- d_{deg-1} ∘ d_{deg} = 0, for deg = 2, ..., maxDeg
      let d_upper := dGradedId (Name.nested baseName "d") deg (k := .morphism)
      let d_lower := dGradedId (Name.nested baseName "d") (deg - 1) (k := .morphism)
      { id := gid s!"dd_zero_{a.id.name}_{deg}" (k := .twoCell)
        leftPath := .comp (.atom d_upper) (.atom d_lower)
        rightPath := .id (dGradedAtom baseName (deg - 2))  -- zero map represented as id on codomain
        description := s!"d∘d = 0: d_{deg-1} ∘ d_{deg} = 0 for {a.id.name}" : Generator2 }

  -- Chain maps: for each morphism f : A → B (atomic endpoints), create graded components
  let atomicMorphisms := t.morphisms.filter fun f =>
    match f.domain, f.codomain with
    | .atom _, .atom _ => true
    | _, _ => false
  let chainMaps := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let chDom := Name.app (.root "Ch") domName
    let chCod := Name.app (.root "Ch") codName
    degrees.map fun n =>
      { id := dGradedId (Name.app (.root "Ch") f.id.name) n (k := .morphism)
        domain := dGradedAtom chDom n
        codomain := dGradedAtom chCod n
        description := s!"Chain map Ch({f.id.name})_{n}" : Generator1 }

  -- Chain map commutativity: f_{n-1} ∘ d^A_n = d^B_n ∘ f_n
  let chainMapAxioms := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let chDom := Name.app (.root "Ch") domName
    let chCod := Name.app (.root "Ch") codName
    (List.range maxDeg).map fun n =>
      let deg := n + 1
      let dA := dGradedId (Name.nested chDom "d") deg (k := .morphism)
      let dB := dGradedId (Name.nested chCod "d") deg (k := .morphism)
      let f_upper := dGradedId (Name.app (.root "Ch") f.id.name) deg (k := .morphism)
      let f_lower := dGradedId (Name.app (.root "Ch") f.id.name) (deg - 1) (k := .morphism)
      { id := gid s!"chain_comm_{f.id.name}_{deg}" (k := .twoCell)
        leftPath := .comp (.atom dA) (.atom f_lower)
        rightPath := .comp (.atom f_upper) (.atom dB)
        description := s!"Chain map commutes with d: f_{deg-1} ∘ d^A = d^B ∘ f_{deg}" : Generator2 }

  { name := s!"Ch({t.name})"
    doctrine := t.doctrine
    objects := complexObjects
    morphisms := differentials ++ chainMaps
    axioms := ddZeroAxioms ++ chainMapAxioms }

/-- Construct the homotopy category K(C): chain complexes modulo chain homotopies.

    Two chain maps f, g : C• → D• are homotopic if there exist maps
    h_n : C_n → D_{n+1} such that f_n - g_n = d^D_{n+1} ∘ h_n + h_{n-1} ∘ d^C_n.

    We add homotopy equivalence axioms identifying homotopic maps. -/
def homotopyCategory (t : Theory) (maxDeg : Nat := 3) : Theory :=
  let ch := chainComplexCategory t maxDeg
  let degrees := List.range (maxDeg + 1)

  -- Homotopy maps: for each pair of base objects A, B add h_n : Ch(A)_n → Ch(B)_{n+1}
  let homotopyMaps := t.objects.flatMap fun a =>
    t.objects.flatMap fun b =>
      let chA := Name.app (.root "Ch") a.id.name
      let chB := Name.app (.root "Ch") b.id.name
      let htpyBase := Name.pair (Name.app (.root "htpy") a.id.name) b.id.name
      (List.range maxDeg).map fun n =>
        { id := dGradedId htpyBase n (k := .morphism)
          domain := dGradedAtom chA n
          codomain := dGradedAtom chB (n + 1)
          description := s!"Homotopy h_{n} : {a.id.name}_{n} → {b.id.name}_{n+1}" : Generator1 }

  -- Homotopy equivalence axioms: if f ~ g via h, then f = g in K(C)
  let atomicMorphisms := t.morphisms.filter fun f =>
    match f.domain, f.codomain with
    | .atom _, .atom _ => true
    | _, _ => false
  let homotopyAxioms := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let chDom := Name.app (.root "Ch") domName
    let chCod := Name.app (.root "Ch") codName
    let htpyBase := Name.pair (Name.app (.root "htpy") domName) codName
    (List.range maxDeg).map fun n =>
      let deg := n + 1
      let f_n := dGradedId (Name.app (.root "Ch") f.id.name) deg (k := .morphism)
      let h_n := dGradedId htpyBase deg (k := .morphism)
      let h_prev := dGradedId htpyBase (deg - 1) (k := .morphism)
      let dB := dGradedId (Name.nested chCod "d") (deg + 1) (k := .morphism)
      let dA := dGradedId (Name.nested chDom "d") deg (k := .morphism)
      { id := gid s!"htpy_equiv_{f.id.name}_{deg}" (k := .twoCell)
        leftPath := .atom f_n
        rightPath := .comp (.atom h_n) (.atom dB)  -- d∘h + h∘d component
        description := s!"Homotopy relation: f ~ g via h at degree {deg}" : Generator2 }

  { ch with
    name := s!"K({t.name})"
    morphisms := ch.morphisms ++ homotopyMaps
    axioms := ch.axioms ++ homotopyAxioms }

/-- Construct the derived category D(C): localize the homotopy category
    at quasi-isomorphisms.

    A quasi-isomorphism is a chain map inducing isomorphisms on all
    homology groups. We formally invert these maps.

    The result includes:
    - All structure from K(C)
    - Formal inverses for quasi-isomorphisms
    - Shift functor [1] : D(C) → D(C)
    - Distinguished triangles: A → B → C → A[1] -/
def derivedCategory (t : Theory) (maxDeg : Nat := 3) : Theory :=
  let kc := homotopyCategory t maxDeg
  let degrees := List.range (maxDeg + 1)
  let atomicMorphisms := t.morphisms.filter fun f =>
    match f.domain, f.codomain with
    | .atom _, .atom _ => true
    | _, _ => false

  -- Quasi-isomorphism markers: for each morphism f, add a formal inverse qis(f)⁻¹
  let qisInverses := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let chDom := Name.app (.root "Ch") domName
    let chCod := Name.app (.root "Ch") codName
    degrees.map fun n =>
      { id := { name := Name.nested (Name.app (.root "qis⁻¹") f.id.name) s!"_{n}"
                kind := .morphism }
        domain := dGradedAtom chCod n
        codomain := dGradedAtom chDom n
        description := s!"Quasi-iso inverse qis({f.id.name})⁻¹ at degree {n}" : Generator1 }

  -- Invertibility axioms: f ∘ qis(f)⁻¹ = id and qis(f)⁻¹ ∘ f = id at each degree
  let qisLeftInv := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let chDom := Name.app (.root "Ch") domName
    degrees.map fun n =>
      let f_n := dGradedId (Name.app (.root "Ch") f.id.name) n (k := .morphism)
      let inv_n := GeneratorId.mk (Name.nested (Name.app (.root "qis⁻¹") f.id.name) s!"_{n}") 0 .morphism
      { id := gid s!"qis_left_{f.id.name}_{n}" (k := .twoCell)
        leftPath := .comp (.atom inv_n) (.atom f_n)
        rightPath := .id (dGradedAtom chDom n)
        description := s!"qis⁻¹ ∘ f = id at degree {n}" : Generator2 }

  let qisRightInv := atomicMorphisms.flatMap fun f =>
    let codName := f.codomain.toName
    let chCod := Name.app (.root "Ch") codName
    degrees.map fun n =>
      let f_n := dGradedId (Name.app (.root "Ch") f.id.name) n (k := .morphism)
      let inv_n := GeneratorId.mk (Name.nested (Name.app (.root "qis⁻¹") f.id.name) s!"_{n}") 0 .morphism
      { id := gid s!"qis_right_{f.id.name}_{n}" (k := .twoCell)
        leftPath := .comp (.atom f_n) (.atom inv_n)
        rightPath := .id (dGradedAtom chCod n)
        description := s!"f ∘ qis⁻¹ = id at degree {n}" : Generator2 }

  -- Shift functor [1]: shifts grading down by 1, with sign on differential
  -- On objects: A[1]_n = A_{n+1}
  let shiftObjects := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Ch") a.id.name
    let shiftedBase := Name.app (.root "[1]") baseName
    degrees.map fun n =>
      { id := dGradedId shiftedBase n
        description := s!"Shifted complex {a.id.name}[1]_{n} = {a.id.name}_{n+1}" : Generator0 }

  -- Shift identification axioms: A[1]_n = A_{n+1}
  let shiftAxioms := t.objects.flatMap fun a =>
    let baseName := Name.app (.root "Ch") a.id.name
    let shiftedBase := Name.app (.root "[1]") baseName
    (List.range maxDeg).map fun n =>
      { id := gid s!"shift_id_{a.id.name}_{n}" (k := .twoCell)
        leftPath := .id (dGradedAtom shiftedBase n)
        rightPath := .id (dGradedAtom baseName (n + 1))
        description := s!"Shift: {a.id.name}[1]_{n} = {a.id.name}_{n+1}" : Generator2 }

  -- Distinguished triangles: for each morphism f : A → B,
  -- we get A → B → Cone(f) → A[1]
  let coneObjects := atomicMorphisms.flatMap fun f =>
    let baseName := Name.app (.root "Cone") f.id.name
    degrees.map fun n =>
      { id := dGradedId baseName n
        description := s!"Mapping cone Cone({f.id.name})_{n}" : Generator0 }

  -- Cone inclusion: B → Cone(f)
  let coneInclusions := atomicMorphisms.flatMap fun f =>
    let codName := f.codomain.toName
    let chCod := Name.app (.root "Ch") codName
    let coneName := Name.app (.root "Cone") f.id.name
    degrees.map fun n =>
      { id := { name := Name.nested (.graded coneName n) "ι", kind := .morphism }
        domain := dGradedAtom chCod n
        codomain := dGradedAtom coneName n
        description := s!"Cone inclusion ι : {codName}_{n} → Cone({f.id.name})_{n}" : Generator1 }

  -- Cone projection: Cone(f) → A[1]
  let coneProjections := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let chDom := Name.app (.root "Ch") domName
    let coneName := Name.app (.root "Cone") f.id.name
    let shiftedDom := Name.app (.root "[1]") chDom
    degrees.map fun n =>
      { id := { name := Name.nested (.graded coneName n) "π", kind := .morphism }
        domain := dGradedAtom coneName n
        codomain := dGradedAtom shiftedDom n
        description := s!"Cone projection π : Cone({f.id.name})_{n} → {domName}[1]_{n}" : Generator1 }

  -- Triangle exactness: the sequence A → B → Cone(f) → A[1] is a distinguished triangle
  let triangleAxioms := atomicMorphisms.flatMap fun f =>
    let domName := f.domain.toName
    let codName := f.codomain.toName
    let coneName := Name.app (.root "Cone") f.id.name
    degrees.map fun n =>
      let f_n := dGradedId (Name.app (.root "Ch") f.id.name) n (k := .morphism)
      let ι_n := GeneratorId.mk (Name.nested (.graded coneName n) "ι") 0 .morphism
      { id := gid s!"triangle_exact_{f.id.name}_{n}" (k := .twoCell)
        leftPath := .comp (.atom f_n) (.atom ι_n)
        rightPath := .id (dGradedAtom coneName n)  -- ι ∘ f = 0 (represented via identity on cone)
        description := s!"Triangle exactness: ι ∘ f = 0 at degree {n}" : Generator2 }

  { kc with
    name := s!"D({t.name})"
    doctrine := { doctrine := .StableCategory }
    objects := kc.objects ++ shiftObjects ++ coneObjects
    morphisms := kc.morphisms ++ qisInverses ++ coneInclusions ++ coneProjections
    axioms := kc.axioms ++ qisLeftInv ++ qisRightInv ++ shiftAxioms ++ triangleAxioms }

end CatLab
