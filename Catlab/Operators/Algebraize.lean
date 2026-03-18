/-
  CatLab — Algebraize: Fine-Grained Algebraic Combinators

  Operators for building algebraic theories incrementally by adding structure
  to an existing theory.  Together these form a compositional toolkit:

    addCommutativity  — swap axiom: op = swap ∘ op
    addInverse        — inverse morphism + left/right inverse axioms
    addUnit           — unit morphism + left/right unit axioms
    addIdempotent     — idempotency: op(a, a) = a
    addAbsorption     — absorption pair: a ∧ (a ∨ b) = a  and  a ∨ (a ∧ b) = a
    addDistributivity — left/right distributivity of mul over add
    addAdjoint        — right adjoint to a binary operation (e.g., → for ∧)
    renameGenerator   — rename morphism/axiom IDs and their references

  Derivation examples:
    Group         = addInverse(Monoid, "μ", "η")
    AbelianGroup  = addCommutativity(Group, "μ")
    HeytingAlgebra = addAdjoint(Lattice, "∧", "→")
    CommRing      = addCommutativity(Ring, "mul")
-/

import Catlab.Core.Theory

namespace CatLab

-- ============================================================
-- addCommutativity
-- ============================================================

/-- Add commutativity to a named binary operation  op : A × A → A.
    Adds a swap morphism  swap : A × A → A × A  (if absent) and the axiom
      comm_<opName> :  op = swap ∘ op.
    Used to derive AbelianGroup from Group, CommRing from Ring, etc. -/
def addCommutativity (t : Theory) (opName : String) : Theory :=
  match t.findMorphism (.root opName) with
  | none => t
  | some op =>
    let carrier := op.codomain
    let hasSwap := t.morphisms.any (fun m => m.id.name == .root "swap")
    let swapMor : Generator1 :=
      { id := gid "swap"
        domain   := .prod carrier carrier
        codomain := .prod carrier carrier
        description := "Symmetry swap for commutativity" }
    let commAx : Generator2 :=
      { id := gid s!"comm_{opName}"
        leftPath  := .atom op.id
        rightPath := .comp (.atom (gid "swap")) (.atom op.id)
        description := s!"{opName} is commutative: op = swap ∘ op" }
    { t with
      morphisms := if hasSwap then t.morphisms else t.morphisms ++ [swapMor]
      axioms    := t.axioms ++ [commAx] }

-- ============================================================
-- addInverse
-- ============================================================

/-- Add an inverse morphism  ι : A → A  for the operation  op : A × A → A
    with unit  unitName : 1 → A.  Adds left and right inverse axioms:
      left_inv  :  op(ι(a), a) = unit
      right_inv :  op(a, ι(a)) = unit
    Used to derive Group from Monoid. -/
def addInverse (t : Theory) (opName : String) (unitName : String) : Theory :=
  match t.findMorphism (.root opName), t.findMorphism (.root unitName) with
  | none, _ | _, none => t
  | some op, some unitMor =>
    let carrier := op.codomain
    -- Flat name so renameGenerator can easily match: "μ_inv", "add_inv", etc.
    let invId   := { name := .root s!"{opName}_inv", index := 0, kind := .morphism }
    let invMor : Generator1 :=
      { id          := invId
        domain      := carrier
        codomain    := carrier
        description := s!"Inverse for {opName}: A → A" }
    let leftInv : Generator2 :=
      { id        := gid s!"left_inv_{opName}"
        leftPath  := .comp (.prod (.atom invId) (.id carrier)) (.atom op.id)
        rightPath := .atom unitMor.id
        description := s!"Left inverse: {opName}(ι(a), a) = unit" }
    let rightInv : Generator2 :=
      { id        := gid s!"right_inv_{opName}"
        leftPath  := .comp (.prod (.id carrier) (.atom invId)) (.atom op.id)
        rightPath := .atom unitMor.id
        description := s!"Right inverse: {opName}(a, ι(a)) = unit" }
    { t with
      morphisms := t.morphisms ++ [invMor]
      axioms    := t.axioms ++ [leftInv, rightInv] }

-- ============================================================
-- addUnit
-- ============================================================

/-- Add a unit element  e : 1 → A  for the operation  op : A × A → A.
    Adds left and right unit axioms:
      left_unit  :  op(e, a) = a
      right_unit :  op(a, e) = a
    Used to derive Monoid from a semigroup-like theory. -/
def addUnit (t : Theory) (opName : String) : Theory :=
  match t.findMorphism (.root opName) with
  | none => t
  | some op =>
    let carrier := op.codomain
    -- Flat name so renameGenerator can easily match: "μ_unit", "add_unit", etc.
    let unitId  := { name := .root s!"{opName}_unit", index := 0, kind := .morphism }
    let unitMor : Generator1 :=
      { id          := unitId
        domain      := .terminal
        codomain    := carrier
        description := s!"Unit for {opName}: 1 → A" }
    let leftUnit : Generator2 :=
      { id        := gid s!"left_unit_{opName}"
        leftPath  := .comp (.prod (.atom unitId) (.id carrier)) (.atom op.id)
        rightPath := .id carrier
        description := s!"{opName}(unit, a) = a" }
    let rightUnit : Generator2 :=
      { id        := gid s!"right_unit_{opName}"
        leftPath  := .comp (.prod (.id carrier) (.atom unitId)) (.atom op.id)
        rightPath := .id carrier
        description := s!"{opName}(a, unit) = a" }
    { t with
      morphisms := t.morphisms ++ [unitMor]
      axioms    := t.axioms ++ [leftUnit, rightUnit] }

-- ============================================================
-- addIdempotent
-- ============================================================

/-- Add idempotency  op(a, a) = a  for operation  op : A × A → A.
    Used to derive semilattices from commutative semigroups. -/
def addIdempotent (t : Theory) (opName : String) : Theory :=
  match t.findMorphism (.root opName) with
  | none => t
  | some op =>
    let carrier := op.codomain
    let idem : Generator2 :=
      { id        := gid s!"idem_{opName}"
        leftPath  := .comp (.prod (.id carrier) (.id carrier)) (.atom op.id)
        rightPath := .id carrier
        description := s!"Idempotency: {opName}(a, a) = a" }
    { t with axioms := t.axioms ++ [idem] }

-- ============================================================
-- addAbsorption
-- ============================================================

/-- Add the absorption laws between two binary operations:
      op1(a, op2(a, b)) = a     (a ∧ (a ∨ b) = a)
      op2(a, op1(a, b)) = a     (a ∨ (a ∧ b) = a)
    Used to derive a lattice from meet- and join-semilattices. -/
def addAbsorption (t : Theory) (op1Name : String) (op2Name : String) : Theory :=
  match t.findMorphism (.root op1Name), t.findMorphism (.root op2Name) with
  | none, _ | _, none => t
  | some op1, some op2 =>
    let carrier := op1.codomain
    let abs1 : Generator2 :=
      { id        := gid s!"absorb_{op1Name}_{op2Name}"
        leftPath  := .comp (.prod (.id carrier) (.atom op2.id)) (.atom op1.id)
        rightPath := .id carrier
        description := s!"{op1Name}(a, {op2Name}(a, b)) = a" }
    let abs2 : Generator2 :=
      { id        := gid s!"absorb_{op2Name}_{op1Name}"
        leftPath  := .comp (.prod (.id carrier) (.atom op1.id)) (.atom op2.id)
        rightPath := .id carrier
        description := s!"{op2Name}(a, {op1Name}(a, b)) = a" }
    { t with axioms := t.axioms ++ [abs1, abs2] }

-- ============================================================
-- addDistributivity
-- ============================================================

/-- Add left and right distributivity of  mulName  over  addName:
      left  : mul(a, add(b, c)) = add(mul(a,b), mul(a,c))
      right : mul(add(a,b), c)  = add(mul(a,c), mul(b,c))
    Used to derive Ring from additive + multiplicative structure. -/
def addDistributivity (t : Theory) (mulName : String) (addName : String) : Theory :=
  match t.findMorphism (.root mulName), t.findMorphism (.root addName) with
  | none, _ | _, none => t
  | some mulOp, some addOp =>
    let carrier := mulOp.codomain
    let leftD : Generator2 :=
      { id        := gid s!"left_distrib"
        leftPath  := .comp (.prod (.id carrier) (.atom addOp.id)) (.atom mulOp.id)
        rightPath := .comp (.prod (.atom mulOp.id) (.atom mulOp.id)) (.atom addOp.id)
        description := s!"Left distributivity: {mulName}(a, {addName}(b,c)) = {addName}({mulName}(a,b), {mulName}(a,c))" }
    let rightD : Generator2 :=
      { id        := gid s!"right_distrib"
        leftPath  := .comp (.prod (.atom addOp.id) (.id carrier)) (.atom mulOp.id)
        rightPath := .comp (.prod (.atom mulOp.id) (.atom mulOp.id)) (.atom addOp.id)
        description := s!"Right distributivity: {mulName}({addName}(a,b), c) = {addName}({mulName}(a,c), {mulName}(b,c))" }
    { t with axioms := t.axioms ++ [leftD, rightD] }

-- ============================================================
-- addAdjoint
-- ============================================================

/-- Add a right adjoint  adj : A × A → A  to the operation  op : A × A → A.
    The adjunction is:  op(a, b) ≤ c  ↔  a ≤ adj(b, c)
    encoded as two axioms:
      adj_counit : op(a, adj(a, c)) factors through c   (use the adjoint)
      adj_unit   : a ≤ adj(b, op(a, b))                 (introduce the adjoint)

    Classical instance:  addAdjoint Lattice "∧" "→"  gives Heyting implication
    since  a ∧ b ≤ c  ↔  a ≤ b → c. -/
def addAdjoint (t : Theory) (opName : String) (adjName : String) : Theory :=
  match t.findMorphism (.root opName) with
  | none => t
  | some op =>
    let carrier := op.codomain
    let adjId   := { name := .root adjName, index := 0, kind := .morphism }
    let adjMor : Generator1 :=
      { id          := adjId
        domain      := .prod carrier carrier
        codomain    := carrier
        description := s!"Right adjoint to {opName}: {adjName}(b, c) is the largest a with op(a,b) ≤ c" }
    -- Counit: op(a, adj(a, c)) ≤ c
    -- Encoded as: op ∘ (id × adj) = adj  (the adjunction identity in the Heyting sense)
    let counit : Generator2 :=
      { id        := gid s!"adj_counit_{opName}_{adjName}"
        leftPath  := .comp (.prod (.id carrier) (.atom adjId)) (.atom op.id)
        rightPath := .atom adjId
        description := s!"Adjunction counit: {opName}(a, {adjName}(a,c)) ≤ {adjName}(a,c)" }
    -- Unit: a ≤ adj(b, op(a, b))
    -- Encoded as: adj ∘ (id × op) = adj  (the unit identity)
    let unit : Generator2 :=
      { id        := gid s!"adj_unit_{opName}_{adjName}"
        leftPath  := .comp (.prod (.id carrier) (.atom op.id)) (.atom adjId)
        rightPath := .atom adjId
        description := s!"Adjunction unit: a ≤ {adjName}(b, {opName}(a,b))" }
    { t with
      morphisms := t.morphisms ++ [adjMor]
      axioms    := t.axioms ++ [counit, unit] }

-- ============================================================
-- renameGenerator
-- ============================================================

/-- Rename morphism IDs (and all references in axioms' paths) by a substitution
    list of  (oldName, newName)  string pairs.  Object sorts are unaffected.
    Used to adapt naming conventions before amalgamation:
      renameGenerator TheoryOfGroups [("μ", "add"), ("η", "zero"), ("ι.inv", "neg")]
    makes additive notation for use in ring construction. -/
def renameGenerator (t : Theory) (renames : List (String × String)) : Theory :=
  let nameMap : Name → Name := fun n =>
    match renames.find? (fun (old, _) => n == .root old) with
    | some (_, newName) => .root newName
    | none => n
  -- Also rename nested inverse names like "μ.inv"
  let nameMapFull : Name → Name := fun n =>
    match renames.find? (fun (old, _) => n == .root old) with
    | some (_, newName) => .root newName
    | none =>
      match renames.find? (fun (old, _) =>
        match n with | .nested (.root s) _ => s == old | _ => false) with
      | some (old, newName) =>
        match n with
        | .nested _ suffix => .nested (.root newName) suffix
        | _ => n
      | none => n
  let renameMor (m : Generator1) : Generator1 :=
    { m with
      id       := { m.id with name := nameMapFull m.id.name }
      domain   := m.domain.mapNames nameMapFull
      codomain := m.codomain.mapNames nameMapFull }
  let renameAx (ax : Generator2) : Generator2 :=
    { ax with
      leftPath  := ax.leftPath.mapNames nameMapFull
      rightPath := ax.rightPath.mapNames nameMapFull }
  { t with
    morphisms := t.morphisms.map renameMor
    axioms    := t.axioms.map renameAx }

-- ============================================================
-- addAnnihilator
-- ============================================================

/-- Add zero-annihilation axioms for `mulName` with absorbing element `zeroName`:
      left_annihilate  :  mul(zero, a) = zero
      right_annihilate :  mul(a, zero) = zero
    Used to complete the semiring axioms (0 · a = 0 and a · 0 = 0). -/
def addAnnihilator (t : Theory) (mulName : String) (zeroName : String) : Theory :=
  match t.findMorphism (.root mulName), t.findMorphism (.root zeroName) with
  | none, _ | _, none => t
  | some mulOp, some zeroMor =>
    let carrier := mulOp.codomain
    let leftAnn : Generator2 :=
      { id        := gid s!"left_annihilate_{mulName}"
        leftPath  := .comp (.prod (.atom zeroMor.id) (.id carrier)) (.atom mulOp.id)
        rightPath := .atom zeroMor.id
        description := s!"Left annihilation: {mulName}({zeroName}, a) = {zeroName}" }
    let rightAnn : Generator2 :=
      { id        := gid s!"right_annihilate_{mulName}"
        leftPath  := .comp (.prod (.id carrier) (.atom zeroMor.id)) (.atom mulOp.id)
        rightPath := .atom zeroMor.id
        description := s!"Right annihilation: {mulName}(a, {zeroName}) = {zeroName}" }
    { t with axioms := t.axioms ++ [leftAnn, rightAnn] }

-- ============================================================
-- addBracket
-- ============================================================

/-- Add a Lie bracket  [−,−] : A × A → A  to an abelian-group-like theory.
    Requires that the theory already has:
      addName  : A × A → A   (addition)
      negName  : A → A        (negation)
      swap     : A × A → A × A (from addCommutativity; looked up automatically)
    Adds:
      bracketName : A × A → A
    And three axioms:
      antisymm : [x,y] = neg([y,x])          (= neg ∘ (swap ∘ bracket))
      jacobi   : [x,[y,z]] = [[x,y],z] + [y,[x,z]]
      bilinear : [x, y+z] = [x,y] + [x,z]
    Used to derive LieAlgebra from AbelianGroup. -/
def addBracket (t : Theory) (addName negName bracketName : String) : Theory :=
  match t.findMorphism (.root addName), t.findMorphism (.root negName) with
  | none, _ | _, none => t
  | some addOp, some negOp =>
    let carrier   := addOp.codomain
    let bracketId := { name := .root bracketName, index := 0, kind := .morphism }
    let bracketMor : Generator1 :=
      { id := bracketId, domain := .prod carrier carrier, codomain := carrier
        description := s!"Lie bracket {bracketName}: A × A → A" }
    -- Find the swap morphism (added by addCommutativity)
    let swapId := (t.morphisms.find? (fun m => m.id.name == .root "swap")).map (·.id)
    -- Antisymmetry: [x,y] = neg([y,x])  i.e.  bracket = neg ∘ (swap ∘ bracket)
    let antiSymm : Generator2 :=
      { id        := gid s!"antisymm_{bracketName}"
        leftPath  := .atom bracketId
        rightPath := match swapId with
          | some sw => .comp (.comp (.atom sw) (.atom bracketId)) (.atom negOp.id)
          | none    => .comp (.atom bracketId) (.atom negOp.id)
        description := s!"Antisymmetry: {bracketName}(x,y) = neg({bracketName}(y,x))" }
    -- Jacobi: [x,[y,z]] = [[x,y],z] + [y,[x,z]]
    let jacobi : Generator2 :=
      { id        := gid s!"jacobi_{bracketName}"
        leftPath  := .comp (.prod (.id carrier) (.atom bracketId)) (.atom bracketId)
        rightPath :=
          .comp
            (.prod
              (.comp (.prod (.atom bracketId) (.id carrier)) (.atom bracketId))
              (.comp (.prod (.id carrier)    (.atom bracketId)) (.atom bracketId)))
            (.atom addOp.id)
        description := s!"Jacobi: {bracketName}(x,{bracketName}(y,z)) = {bracketName}({bracketName}(x,y),z) + {bracketName}(y,{bracketName}(x,z))" }
    -- Bilinearity: [x, y+z] = [x,y] + [x,z]
    let bilinear : Generator2 :=
      { id        := gid s!"bilinear_{bracketName}"
        leftPath  := .comp (.prod (.id carrier) (.atom addOp.id)) (.atom bracketId)
        rightPath := .comp (.prod (.atom bracketId) (.atom bracketId)) (.atom addOp.id)
        description := s!"Bilinearity: {bracketName}(x, y+z) = {bracketName}(x,y) + {bracketName}(x,z)" }
    { t with
      morphisms := t.morphisms ++ [bracketMor]
      axioms    := t.axioms ++ [antiSymm, jacobi, bilinear] }

-- ============================================================
-- addBialgebraAxioms
-- ============================================================

/-- Add bialgebra compatibility axioms to a theory that has both an algebra
    (mulName, unitName) and a coalgebra (comulName, counitName) on the same carrier.
    The bialgebra axioms say that comultiplication and counit are algebra morphisms:
      bialg_comul  : Δ(ab) ~ Δ(a)·Δ(b)    (Δ distributes over mul)
      bialg_counit : ε(ab) ~ ε(a)·ε(b)    (ε distributes over mul)
      bialg_unit   : Δ(1) ~ 1⊗1           (Δ preserves unit)
    Used as intermediate step in HopfAlgebra derivation. -/
def addBialgebraAxioms (t : Theory)
    (mulName unitName comulName counitName : String) : Theory :=
  match t.findMorphism (.root mulName),   t.findMorphism (.root unitName),
        t.findMorphism (.root comulName), t.findMorphism (.root counitName) with
  | some mulOp, some unitMor, some comulOp, some counitMor =>
    -- Δ(ab) ~ Δ(a)·Δ(b): mul then comul = comul both then mul
    let bialgComul : Generator2 :=
      { id        := gid "bialg_comul"
        leftPath  := .comp (.atom mulOp.id) (.atom comulOp.id)
        rightPath := .comp (.prod (.atom comulOp.id) (.atom comulOp.id)) (.atom mulOp.id)
        description := s!"Bialgebra: Δ({mulName}(a,b)) = {mulName}(Δ(a), Δ(b))" }
    -- ε(ab) ~ ε(a)·ε(b): mul then counit = counit both then mul
    let bialgCounit : Generator2 :=
      { id        := gid "bialg_counit"
        leftPath  := .comp (.atom mulOp.id) (.atom counitMor.id)
        rightPath := .comp (.prod (.atom counitMor.id) (.atom counitMor.id)) (.atom mulOp.id)
        description := s!"Bialgebra counit: ε({mulName}(a,b)) = {mulName}(ε(a), ε(b))" }
    -- Δ(1) ~ 1⊗1: unit then comul = unit paired with itself
    let bialgUnit : Generator2 :=
      { id        := gid "bialg_unit"
        leftPath  := .comp (.atom unitMor.id) (.atom comulOp.id)
        rightPath := .prod (.atom unitMor.id) (.atom unitMor.id)
        description := s!"Bialgebra unit: Δ({unitName}) = {unitName} ⊗ {unitName}" }
    { t with axioms := t.axioms ++ [bialgComul, bialgCounit, bialgUnit] }
  | _, _, _, _ => t

-- ============================================================
-- addAntipode
-- ============================================================

/-- Add an antipode  S : H → H  with the Hopf axioms:
      antipode_left  : mul(S(a), a) = unit(counit(a))   i.e. μ∘(S⊗id)∘Δ = η∘ε
      antipode_right : mul(a, S(a)) = unit(counit(a))   i.e. μ∘(id⊗S)∘Δ = η∘ε
    These say S is the inverse of the identity in the convolution algebra.
    Used to derive HopfAlgebra from a bialgebra. -/
def addAntipode (t : Theory)
    (mulName unitName comulName counitName : String) : Theory :=
  match t.findMorphism (.root mulName),   t.findMorphism (.root unitName),
        t.findMorphism (.root comulName), t.findMorphism (.root counitName) with
  | some mulOp, some unitMor, some comulOp, some counitMor =>
    let carrier    := mulOp.codomain
    let antipodeId := { name := .root "antipode", index := 0, kind := .morphism }
    let antipodeMor : Generator1 :=
      { id := antipodeId, domain := carrier, codomain := carrier
        description := "Antipode S : H → H" }
    -- μ ∘ (S ⊗ id) ∘ Δ = η ∘ ε
    let leftAntipode : Generator2 :=
      { id        := gid "antipode_left"
        leftPath  := .comp (.atom comulOp.id)
                      (.comp (.prod (.atom antipodeId) (.id carrier)) (.atom mulOp.id))
        rightPath := .comp (.atom counitMor.id) (.atom unitMor.id)
        description := "Left Hopf axiom: μ∘(S⊗id)∘Δ = η∘ε" }
    -- μ ∘ (id ⊗ S) ∘ Δ = η ∘ ε
    let rightAntipode : Generator2 :=
      { id        := gid "antipode_right"
        leftPath  := .comp (.atom comulOp.id)
                      (.comp (.prod (.id carrier) (.atom antipodeId)) (.atom mulOp.id))
        rightPath := .comp (.atom counitMor.id) (.atom unitMor.id)
        description := "Right Hopf axiom: μ∘(id⊗S)∘Δ = η∘ε" }
    { t with
      morphisms := t.morphisms ++ [antipodeMor]
      axioms    := t.axioms ++ [leftAntipode, rightAntipode] }
  | _, _, _, _ => t

-- ============================================================
-- addSymmetryAction
-- ============================================================

/-- Add a symmetric group action  sym_act : Op → Op  to an operad-like theory,
    together with an equivariance axiom:
      sym_equivariance : sym_act ∘ comp = comp ∘ (sym_act ⊗ sym_act)
    This turns a non-symmetric (plain) operad/multicategory into a symmetric one.
    Used to derive SymmetricOperad from Multicategory. -/
def addSymmetryAction (t : Theory) (compName : String) : Theory :=
  match t.findMorphism (.root compName) with
  | none => t
  | some compOp =>
    let carrier  := compOp.codomain
    let symActId := { name := .root "sym_act", index := 0, kind := .morphism }
    let symActMor : Generator1 :=
      { id := symActId, domain := carrier, codomain := carrier
        description := "Symmetric group action σ : Op → Op (permutes inputs)" }
    -- Equivariance: sym_act ∘ comp = comp ∘ (sym_act × sym_act)
    let equivariance : Generator2 :=
      { id        := gid "sym_equivariance"
        leftPath  := .comp (.atom compOp.id) (.atom symActId)
        rightPath := .comp (.prod (.atom symActId) (.atom symActId)) (.atom compOp.id)
        description := "Equivariance: σ ∘ ∘ = ∘ ∘ (σ × σ)" }
    { t with
      morphisms := t.morphisms ++ [symActMor]
      axioms    := t.axioms ++ [equivariance] }

end CatLab
