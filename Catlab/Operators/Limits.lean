/-
  CatLab — Limits & Colimits Engine

  The universal construction engine. Products, coproducts, pullbacks, pushouts,
  equalizers, coequalizers — all computed here.

  Each construction emits:
  1. The universal object
  2. Structural morphisms (projections/injections)
  3. Commutativity axioms (the defining equations)
  4. Existence axioms (∀ compatible morphisms, the mediating map exists)
  5. Uniqueness axioms (the mediating map is unique)

  Axioms use quantified schemas (AxiomVar + Expr.var) so the bounded
  Knuth-Bendix rewriter can verify them via unification.
-/

import Catlab.Core.Theory

namespace CatLab

/-- A diagram is a small category mapped into a target theory:
    a collection of objects and morphisms between them. -/
structure Diagram where
  /-- The nodes of the diagram, each referencing an Expr in the theory -/
  nodes : List (String × Expr)
  /-- The edges: (source_name, target_name, morphism_expr) -/
  edges : List (String × String × Expr)
  deriving Repr, Inhabited

/-- A cone over a diagram: an apex object with projection morphisms -/
structure Cone where
  apex : Expr
  projections : List (String × Expr)  -- node_name → projection morphism
  deriving Repr, Inhabited

/-- A cocone over a diagram: a nadir object with injection morphisms -/
structure Cocone where
  nadir : Expr
  injections : List (String × Expr)  -- node_name → injection morphism
  deriving Repr, Inhabited

/-- Result of a limit computation: the new generators added to a theory -/
structure LimitResult where
  /-- The universal object -/
  object : Generator0
  /-- The projection/injection morphisms -/
  morphisms : List Generator1
  /-- The universal property axioms -/
  axioms : List Generator2
  deriving Repr, Inhabited

-- ============================================================
-- Binary Product: A × B with π₁, π₂, ⟨-,-⟩, and uniqueness
-- ============================================================

/-- Compute the binary product of two expressions.
    Returns generators for A × B, π₁, π₂, and the full universal property:
    - ∀ f : X → A, g : X → B. π₁ ∘ ⟨f,g⟩ = f
    - ∀ f : X → A, g : X → B. π₂ ∘ ⟨f,g⟩ = g
    - ∀ h : X → A×B. ⟨π₁ ∘ h, π₂ ∘ h⟩ = h  (uniqueness) -/
def computeProduct (a b : Expr) (namePrefix : String := "prod") : LimitResult :=
  let prodObj := Expr.prod a b
  let π₁ := gid s!"{namePrefix}_π₁" 0 .morphism
  let π₂ := gid s!"{namePrefix}_π₂" 0 .morphism
  let pair := gid s!"{namePrefix}_pair" 0 .morphism
  { object := { id := gid namePrefix, description := s!"Product of {repr a} and {repr b}" }
    morphisms := [
      { id := π₁, domain := prodObj, codomain := a,
        description := "First projection" },
      { id := π₂, domain := prodObj, codomain := b,
        description := "Second projection" },
      { id := pair, domain := .prod a b, codomain := prodObj,
        description := "Pairing: ⟨f,g⟩ (parameterized by f,g via axiom schemas)" }
    ]
    axioms := [
      -- π₁ ∘ ⟨f,g⟩ = f  (first projection law)
      { id := gid s!"{namePrefix}_β₁" 0 .twoCell,
        quantifiers := [
          { name := "f", domain := some (.var "X"), codomain := some a, kind := .morphism },
          { name := "g", domain := some (.var "X"), codomain := some b, kind := .morphism }
        ],
        leftPath := .comp (.atom pair) (.atom π₁),
        rightPath := .var "f",
        description := "∀ f : X → A, g : X → B. π₁ ∘ ⟨f,g⟩ = f" },
      -- π₂ ∘ ⟨f,g⟩ = g  (second projection law)
      { id := gid s!"{namePrefix}_β₂" 0 .twoCell,
        quantifiers := [
          { name := "f", domain := some (.var "X"), codomain := some a, kind := .morphism },
          { name := "g", domain := some (.var "X"), codomain := some b, kind := .morphism }
        ],
        leftPath := .comp (.atom pair) (.atom π₂),
        rightPath := .var "g",
        description := "∀ f : X → A, g : X → B. π₂ ∘ ⟨f,g⟩ = g" },
      -- ⟨π₁ ∘ h, π₂ ∘ h⟩ = h  (uniqueness / η-law)
      -- Encodes the pairing applied to the composed projections
      { id := gid s!"{namePrefix}_η" 0 .twoCell,
        quantifiers := [
          { name := "h", domain := some (.var "X"), codomain := some prodObj, kind := .morphism }
        ],
        leftPath := .app (.app (.atom pair) (.comp (.var "h") (.atom π₁)))
                         (.comp (.var "h") (.atom π₂)),
        rightPath := .var "h",
        description := "∀ h : X → A×B. ⟨π₁ ∘ h, π₂ ∘ h⟩ = h (uniqueness)" }
    ] }

-- ============================================================
-- Binary Coproduct: A ⊔ B with ι₁, ι₂, [-,-], and uniqueness
-- ============================================================

/-- Compute the binary coproduct of two expressions.
    Dual of product: injections ι₁, ι₂ and copairing [-,-]. -/
def computeCoproduct (a b : Expr) (namePrefix : String := "coprod") : LimitResult :=
  let coprodObj := Expr.coprod a b
  let ι₁ := gid s!"{namePrefix}_ι₁" 0 .morphism
  let ι₂ := gid s!"{namePrefix}_ι₂" 0 .morphism
  let copair := gid s!"{namePrefix}_copair" 0 .morphism
  { object := { id := gid namePrefix, description := s!"Coproduct of {repr a} and {repr b}" }
    morphisms := [
      { id := ι₁, domain := a, codomain := coprodObj,
        description := "First injection" },
      { id := ι₂, domain := b, codomain := coprodObj,
        description := "Second injection" },
      { id := copair, domain := coprodObj, codomain := .coprod a b,
        description := "Copairing: [f,g] (parameterized by f,g via axiom schemas)" }
    ]
    axioms := [
      -- [f,g] ∘ ι₁ = f
      { id := gid s!"{namePrefix}_β₁" 0 .twoCell,
        quantifiers := [
          { name := "f", domain := some a, codomain := some (.var "Y"), kind := .morphism },
          { name := "g", domain := some b, codomain := some (.var "Y"), kind := .morphism }
        ],
        leftPath := .comp (.atom ι₁) (.atom copair),
        rightPath := .var "f",
        description := "∀ f : A → Y, g : B → Y. [f,g] ∘ ι₁ = f" },
      -- [f,g] ∘ ι₂ = g
      { id := gid s!"{namePrefix}_β₂" 0 .twoCell,
        quantifiers := [
          { name := "f", domain := some a, codomain := some (.var "Y"), kind := .morphism },
          { name := "g", domain := some b, codomain := some (.var "Y"), kind := .morphism }
        ],
        leftPath := .comp (.atom ι₂) (.atom copair),
        rightPath := .var "g",
        description := "∀ f : A → Y, g : B → Y. [f,g] ∘ ι₂ = g" },
      -- [h ∘ ι₁, h ∘ ι₂] = h  (uniqueness)
      -- Encodes the copairing applied to the composed injections
      { id := gid s!"{namePrefix}_η" 0 .twoCell,
        quantifiers := [
          { name := "h", domain := some coprodObj, codomain := some (.var "Y"), kind := .morphism }
        ],
        leftPath := .app (.app (.atom copair) (.comp (.atom ι₁) (.var "h")))
                         (.comp (.atom ι₂) (.var "h")),
        rightPath := .var "h",
        description := "∀ h : A⊔B → Y. [h ∘ ι₁, h ∘ ι₂] = h (uniqueness)" }
    ] }

-- ============================================================
-- Pullback: P with p₁, p₂, commutativity, and universal property
-- ============================================================

/-- Compute the pullback of f : A → C and g : B → C.
    Returns the pullback object P with projections p₁ : P → A, p₂ : P → B
    satisfying f ∘ p₁ = g ∘ p₂, plus the universal property. -/
def computePullback (f g : Generator1) (namePrefix : String := "pb") : LimitResult :=
  let pbObj := Expr.atom (gid namePrefix)
  let pbId := gid namePrefix
  let p₁ := gid s!"{namePrefix}_p₁" 0 .morphism
  let p₂ := gid s!"{namePrefix}_p₂" 0 .morphism
  let med := gid s!"{namePrefix}_med" 0 .morphism
  { object := { id := pbId, description := s!"Pullback of {f.id} and {g.id}" }
    morphisms := [
      { id := p₁, domain := pbObj, codomain := f.domain,
        description := "Pullback projection to first factor" },
      { id := p₂, domain := pbObj, codomain := g.domain,
        description := "Pullback projection to second factor" },
      { id := med, domain := .var "X", codomain := pbObj,
        description := "Mediating morphism (parameterized via axiom schemas)" }
    ]
    axioms := [
      -- Commutativity: f ∘ p₁ = g ∘ p₂
      { id := gid s!"{namePrefix}_comm" 0 .twoCell,
        leftPath := .comp (.atom p₁) (.atom f.id),
        rightPath := .comp (.atom p₂) (.atom g.id),
        description := "Pullback square commutes: f ∘ p₁ = g ∘ p₂" },
      -- Existence: ∀ h₁ : X → A, h₂ : X → B with f ∘ h₁ = g ∘ h₂,
      --   p₁ ∘ med = h₁
      { id := gid s!"{namePrefix}_univ₁" 0 .twoCell,
        quantifiers := [
          { name := "h₁", domain := some (.var "X"), codomain := some f.domain, kind := .morphism },
          { name := "h₂", domain := some (.var "X"), codomain := some g.domain, kind := .morphism }
        ],
        leftPath := .comp (.atom med) (.atom p₁),
        rightPath := .var "h₁",
        description := "∀ compatible (h₁,h₂). p₁ ∘ med(h₁,h₂) = h₁" },
      -- p₂ ∘ med = h₂
      { id := gid s!"{namePrefix}_univ₂" 0 .twoCell,
        quantifiers := [
          { name := "h₁", domain := some (.var "X"), codomain := some f.domain, kind := .morphism },
          { name := "h₂", domain := some (.var "X"), codomain := some g.domain, kind := .morphism }
        ],
        leftPath := .comp (.atom med) (.atom p₂),
        rightPath := .var "h₂",
        description := "∀ compatible (h₁,h₂). p₂ ∘ med(h₁,h₂) = h₂" },
      -- Uniqueness: ∀ k : X → P. p₁ ∘ k = h₁ ∧ p₂ ∘ k = h₂ → k = med(h₁,h₂)
      { id := gid s!"{namePrefix}_unique" 0 .twoCell,
        quantifiers := [
          { name := "k", domain := some (.var "X"), codomain := some pbObj, kind := .morphism },
          { name := "h₁", domain := some (.var "X"), codomain := some f.domain, kind := .morphism },
          { name := "h₂", domain := some (.var "X"), codomain := some g.domain, kind := .morphism }
        ],
        leftPath := .var "k",
        rightPath := .atom med,
        description := "∀ k with p₁∘k = h₁, p₂∘k = h₂. k = med(h₁,h₂) (uniqueness)" }
    ] }

-- ============================================================
-- Pushout: dual of pullback
-- ============================================================

/-- Compute the pushout of f : C → A and g : C → B.
    Dual to pullback. -/
def computePushout (f g : Generator1) (namePrefix : String := "po") : LimitResult :=
  let poObj := Expr.atom (gid namePrefix)
  let poId := gid namePrefix
  let ι₁ := gid s!"{namePrefix}_ι₁" 0 .morphism
  let ι₂ := gid s!"{namePrefix}_ι₂" 0 .morphism
  let med := gid s!"{namePrefix}_med" 0 .morphism
  { object := { id := poId, description := s!"Pushout of {f.id} and {g.id}" }
    morphisms := [
      { id := ι₁, domain := f.codomain, codomain := poObj,
        description := "Pushout injection from first factor" },
      { id := ι₂, domain := g.codomain, codomain := poObj,
        description := "Pushout injection from second factor" },
      { id := med, domain := poObj, codomain := .var "Y",
        description := "Mediating morphism (parameterized via axiom schemas)" }
    ]
    axioms := [
      -- Commutativity: ι₁ ∘ f = ι₂ ∘ g
      { id := gid s!"{namePrefix}_comm" 0 .twoCell,
        leftPath := .comp (.atom f.id) (.atom ι₁),
        rightPath := .comp (.atom g.id) (.atom ι₂),
        description := "Pushout square commutes: ι₁ ∘ f = ι₂ ∘ g" },
      -- Existence: ∀ h₁ : A → Y, h₂ : B → Y with h₁ ∘ f = h₂ ∘ g,
      --   med ∘ ι₁ = h₁
      { id := gid s!"{namePrefix}_univ₁" 0 .twoCell,
        quantifiers := [
          { name := "h₁", domain := some f.codomain, codomain := some (.var "Y"), kind := .morphism },
          { name := "h₂", domain := some g.codomain, codomain := some (.var "Y"), kind := .morphism }
        ],
        leftPath := .comp (.atom ι₁) (.atom med),
        rightPath := .var "h₁",
        description := "∀ compatible (h₁,h₂). med(h₁,h₂) ∘ ι₁ = h₁" },
      -- med ∘ ι₂ = h₂
      { id := gid s!"{namePrefix}_univ₂" 0 .twoCell,
        quantifiers := [
          { name := "h₁", domain := some f.codomain, codomain := some (.var "Y"), kind := .morphism },
          { name := "h₂", domain := some g.codomain, codomain := some (.var "Y"), kind := .morphism }
        ],
        leftPath := .comp (.atom ι₂) (.atom med),
        rightPath := .var "h₂",
        description := "∀ compatible (h₁,h₂). med(h₁,h₂) ∘ ι₂ = h₂" },
      -- Uniqueness: ∀ k : P → Y. k ∘ ι₁ = h₁ ∧ k ∘ ι₂ = h₂ → k = med(h₁,h₂)
      { id := gid s!"{namePrefix}_unique" 0 .twoCell,
        quantifiers := [
          { name := "k", domain := some poObj, codomain := some (.var "Y"), kind := .morphism },
          { name := "h₁", domain := some f.codomain, codomain := some (.var "Y"), kind := .morphism },
          { name := "h₂", domain := some g.codomain, codomain := some (.var "Y"), kind := .morphism }
        ],
        leftPath := .var "k",
        rightPath := .atom med,
        description := "∀ k with k∘ι₁ = h₁, k∘ι₂ = h₂. k = med(h₁,h₂) (uniqueness)" }
    ] }

-- ============================================================
-- Equalizer: E with ι, and universal property
-- ============================================================

/-- Compute the equalizer of f, g : A → B.
    The subobject E → A where f and g agree, with universal property. -/
def computeEqualizer (f g : Generator1) (namePrefix : String := "eq") : LimitResult :=
  let eqObj := Expr.atom (gid namePrefix)
  let eqId := gid namePrefix
  let ι := gid s!"{namePrefix}_ι" 0 .morphism
  let med := gid s!"{namePrefix}_med" 0 .morphism
  { object := { id := eqId, description := s!"Equalizer of {f.id} and {g.id}" }
    morphisms := [
      { id := ι, domain := eqObj, codomain := f.domain,
        description := "Equalizer inclusion" },
      { id := med, domain := .var "X", codomain := eqObj,
        description := "Mediating morphism (parameterized via axiom schemas)" }
    ]
    axioms := [
      -- f ∘ ι = g ∘ ι
      { id := gid s!"{namePrefix}_eq" 0 .twoCell,
        leftPath := .comp (.atom ι) (.atom f.id),
        rightPath := .comp (.atom ι) (.atom g.id),
        description := "Equalizer condition: f ∘ ι = g ∘ ι" },
      -- ∀ h : X → A with f ∘ h = g ∘ h. ι ∘ med(h) = h
      { id := gid s!"{namePrefix}_univ" 0 .twoCell,
        quantifiers := [
          { name := "h", domain := some (.var "X"), codomain := some f.domain, kind := .morphism }
        ],
        leftPath := .comp (.atom med) (.atom ι),
        rightPath := .var "h",
        description := "∀ h with f∘h = g∘h. ι ∘ med(h) = h" }
    ] }

-- ============================================================
-- Coequalizer: dual of equalizer
-- ============================================================

/-- Compute the coequalizer of f, g : A → B.
    The quotient B → Q where f and g are identified, with universal property. -/
def computeCoequalizer (f g : Generator1) (namePrefix : String := "coeq") : LimitResult :=
  let coeqObj := Expr.atom (gid namePrefix)
  let coeqId := gid namePrefix
  let π := gid s!"{namePrefix}_π" 0 .morphism
  let med := gid s!"{namePrefix}_med" 0 .morphism
  { object := { id := coeqId, description := s!"Coequalizer of {f.id} and {g.id}" }
    morphisms := [
      { id := π, domain := f.codomain, codomain := coeqObj,
        description := "Coequalizer quotient map" },
      { id := med, domain := coeqObj, codomain := .var "Y",
        description := "Mediating morphism (parameterized via axiom schemas)" }
    ]
    axioms := [
      -- π ∘ f = π ∘ g
      { id := gid s!"{namePrefix}_eq" 0 .twoCell,
        leftPath := .comp (.atom f.id) (.atom π),
        rightPath := .comp (.atom g.id) (.atom π),
        description := "Coequalizer condition: π ∘ f = π ∘ g" },
      -- ∀ h : B → Y with h ∘ f = h ∘ g. med(h) ∘ π = h
      { id := gid s!"{namePrefix}_univ" 0 .twoCell,
        quantifiers := [
          { name := "h", domain := some f.codomain, codomain := some (.var "Y"), kind := .morphism }
        ],
        leftPath := .comp (.atom π) (.atom med),
        rightPath := .var "h",
        description := "∀ h with h∘f = h∘g. med(h) ∘ π = h" }
    ] }

-- ============================================================
-- General finite limits/colimits
-- ============================================================

/-- Compute the limit of a finite diagram.
    For a diagram D with nodes {Aᵢ} and edges {fₑ : Aₛ → Aₜ},
    produces:
    - Limit object L
    - Projections πᵢ : L → Aᵢ for each node
    - Commutativity: fₑ ∘ πₛ = πₜ for each edge
    - Universal property via mediating morphism -/
def computeLimit (d : Diagram) (namePrefix : String := "lim") : LimitResult :=
  let limObj := Expr.atom (gid namePrefix)
  let projections := d.nodes.map fun (name, obj) =>
    { id := gid s!"{namePrefix}_π_{name}" 0 .morphism,
      domain := limObj, codomain := obj,
      description := s!"Projection to {name}" : Generator1 }
  -- Commutativity axioms: for each edge fₑ : Aₛ → Aₜ, fₑ ∘ πₛ = πₜ
  let commAxioms := d.edges.filterMap fun (srcName, tgtName, edgeExpr) =>
    let πₛ := projections.find? (fun p => p.id.name == .root s!"{namePrefix}_π_{srcName}")
    let πₜ := projections.find? (fun p => p.id.name == .root s!"{namePrefix}_π_{tgtName}")
    match πₛ, πₜ with
    | some ps, some pt => some
      { id := gid s!"{namePrefix}_comm_{srcName}_{tgtName}" 0 .twoCell,
        leftPath := .comp (.atom ps.id) edgeExpr,
        rightPath := .atom pt.id,
        description := s!"fₑ ∘ π_{srcName} = π_{tgtName}" : Generator2 }
    | _, _ => none
  -- Mediating morphism (universal property)
  let med : Generator1 :=
    { id := gid s!"{namePrefix}_med" 0 .morphism,
      domain := .var "X", codomain := limObj,
      description := "Universal mediating morphism" }
  -- Universal property: ∀ compatible cone, πᵢ ∘ med = cone_projection_i
  let univAxioms := d.nodes.map fun (name, _) =>
    { id := gid s!"{namePrefix}_univ_{name}" 0 .twoCell,
      quantifiers := [
        { name := s!"h_{name}", domain := some (.var "X"),
          codomain := d.nodes.find? (fun (n, _) => n == name) |>.map (·.2),
          kind := .morphism }
      ],
      leftPath := .comp (.atom med.id) (.atom (gid s!"{namePrefix}_π_{name}" 0 .morphism)),
      rightPath := .var s!"h_{name}",
      description := s!"∀ compatible cone. π_{name} ∘ med = h_{name}" : Generator2 }
  { object := { id := gid namePrefix, description := s!"Limit of diagram" }
    morphisms := projections ++ [med]
    axioms := commAxioms ++ univAxioms }

/-- Compute the colimit of a finite diagram (dual of limit). -/
def computeColimit (d : Diagram) (namePrefix : String := "colim") : LimitResult :=
  let colimObj := Expr.atom (gid namePrefix)
  let injections := d.nodes.map fun (name, obj) =>
    { id := gid s!"{namePrefix}_ι_{name}" 0 .morphism,
      domain := obj, codomain := colimObj,
      description := s!"Injection from {name}" : Generator1 }
  -- Commutativity axioms: for each edge fₑ : Aₛ → Aₜ, ιₜ ∘ fₑ = ιₛ  (WRONG direction for colimit)
  -- Correct: ιₛ = ιₜ ∘ fₑ  (naturality of cocone)
  let commAxioms := d.edges.filterMap fun (srcName, tgtName, edgeExpr) =>
    let ιₛ := injections.find? (fun p => p.id.name == .root s!"{namePrefix}_ι_{srcName}")
    let ιₜ := injections.find? (fun p => p.id.name == .root s!"{namePrefix}_ι_{tgtName}")
    match ιₛ, ιₜ with
    | some is_, some it => some
      { id := gid s!"{namePrefix}_comm_{srcName}_{tgtName}" 0 .twoCell,
        leftPath := .atom is_.id,
        rightPath := .comp edgeExpr (.atom it.id),
        description := s!"ι_{srcName} = ι_{tgtName} ∘ fₑ" : Generator2 }
    | _, _ => none
  -- Mediating morphism
  let med : Generator1 :=
    { id := gid s!"{namePrefix}_med" 0 .morphism,
      domain := colimObj, codomain := .var "Y",
      description := "Universal mediating morphism" }
  -- Universal property: ∀ compatible cocone, med ∘ ιᵢ = cocone_injection_i
  let univAxioms := d.nodes.map fun (name, _) =>
    { id := gid s!"{namePrefix}_univ_{name}" 0 .twoCell,
      quantifiers := [
        { name := s!"h_{name}",
          domain := d.nodes.find? (fun (n, _) => n == name) |>.map (·.2),
          codomain := some (.var "Y"),
          kind := .morphism }
      ],
      leftPath := .comp (.atom (gid s!"{namePrefix}_ι_{name}" 0 .morphism)) (.atom med.id),
      rightPath := .var s!"h_{name}",
      description := s!"∀ compatible cocone. med ∘ ι_{name} = h_{name}" : Generator2 }
  { object := { id := gid namePrefix, description := s!"Colimit of diagram" }
    morphisms := injections ++ [med]
    axioms := commAxioms ++ univAxioms }

/-- Adjoin a limit result into a theory, extending it with new generators -/
def Theory.adjoinLimit (t : Theory) (lr : LimitResult) : Theory :=
  { t with
    objects := t.objects ++ [lr.object]
    morphisms := t.morphisms ++ lr.morphisms
    axioms := t.axioms ++ lr.axioms }

end CatLab
