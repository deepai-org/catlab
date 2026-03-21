# Omega/Hyperion Evaluation for CatLab Verification Backend

**Purpose:** Evaluate whether Omega and/or Hyperion can serve as verification backends for CatLab's higher-categorical theories, replacing or supplementing the current Lean/Mathlib + Rzk (stubbed) architecture.

**Evaluator instructions:** For each test case below, implement it in Omega and/or Hyperion and report: (1) whether it type-checks/verifies, (2) the error diagnostics produced on failure, (3) wall-clock time, (4) any limitations hit.

---

## 1. Context: What CatLab Is

CatLab is a computer algebra system for categorical theories backed by Lean 4. An LLM proposes candidate theories in JSON; the CAS verifies them structurally (fast path, milliseconds) and semantically (deep path via Lean/Mathlib, seconds). The system has:

- **25 doctrines** (Category, MonoidalCategory, Abelian, Topos, HoTT, CubicalTypeTheory, etc.)
- **68+ operators** (opposite, functor_category, grothendieck, stabilize, etc.)
- **21 expression constructors** (atom, comp, prod, tensor, sigma, pi, fiber, limit, colimit, etc.)

The wire format is `TheoryJson`:

```json
{
  "name": "Monoid",
  "doctrine": "LawvereTheory",
  "objects": [{ "name": "M" }],
  "morphisms": [
    { "name": "mu", "domain": {"prod": ["M", "M"]}, "codomain": "M" },
    { "name": "eta", "domain": "terminal", "codomain": "M" }
  ],
  "axioms": [
    {
      "name": "assoc",
      "lhs": {"comp": [{"prod": [{"atom":"mu"}, {"id":"M"}]}, {"atom":"mu"}]},
      "rhs": {"comp": [{"prod": [{"id":"M"}, {"atom":"mu"}]}, {"atom":"mu"}]}
    }
  ]
}
```

This format maps directly to CatLab's Lean-side `Expr` type:

```
Expr ::= atom(id) | id(obj) | comp(f, g) | prod(a, b) | coprod(a, b)
       | hom(a, b) | tensor(a, b) | unit | terminal | initial
       | sigma(var, base, family) | pi(var, base, family)
       | fiber(mor, pt) | proj(i, src) | inj(i, tgt) | var(name)
       | app(functor, arg) | limit(diagram) | colimit(diagram)
       | natComponent(nat, obj)
```

---

## 2. What We Currently Verify (and How)

### 2.1 Fast Path (Lean-side structural checker)

**Engine:** Bounded term rewriting (max 200 steps, leftmost-outermost).

**What it checks:**
- Position-normalized morphism shape matching (names are irrelevant; §0 = first object, §1 = second)
- Axiom satisfaction via bounded bidirectional normalization
- Permutation search over object orderings (≤4 objects: all N!)

**Failure modes it produces:**

```
MissingSignature { domainShape: "(§0,§0)", codomainShape: "§0", sourceName: "mu" }
AxiomViolation { sourceAxiom: "assoc", lhsReduced: "comp([f,g])", rhsReduced: "h", depthUsed: 5, status: "Failed" }
AxiomViolation { status: "Timeout at depth 200" }  -- circular rewriting
```

**Known limitation:** This is pure term rewriting. It cannot discover non-trivial equalities, prove coherence conditions, or handle higher-dimensional structure.

### 2.2 Deep Path (Lean/Mathlib elaboration)

**Engine:** Lean 4 kernel + `aesop_cat` tactic.

**What it checks:**
- Full type-checking of morphism domain/codomain declarations against Mathlib typeclasses
- Axiom proof obligations via aesop_cat (with sorry fallback)
- Operator-specialized elaboration for functor categories, Grothendieck, comma categories

**Three-state result:**
- `success` — fully typed, all axioms proven
- `semantic_error` — type mismatch (e.g., invalid composition)
- `unverified_axiom` — well-typed but aesop_cat couldn't prove it (falls back to sorry)

**Known limitation:** Only works for truncation level ≤ 2 (ordinary 1-categories). Higher-categorical theories hit a stub that returns "Rzk-based semantic verification pending."

### 2.3 The Gap: 5 Higher-Categorical Doctrines Are Unverified

These doctrines currently pass structural checks only — no semantic verification:

| Doctrine | What it models | Key axioms needing verification |
|----------|---------------|--------------------------------|
| `MartinLofTypeTheory` | HoTT / Categories with Families | J-β, univalence (ua is section of transport) |
| `CubicalTypeTheory` | Cubical TT with interval, Kan ops | hcomp endpoint reduction, coercion |
| `CohesiveHomotopyTypeTheory` | Cohesive HoTT (∫ ⊣ ♭ ⊣ ♯) | Adjunction triangle identities, modal laws |
| `InfinityNCategory` | (∞,n)-categories with cells | Globularity, interchange law, invertibility of higher cells |
| `PresentableInfinityCategory` | ∞-topoi (Lurie) | Descent axiom, object classifier |

---

## 3. Test Cases for Omega

These test the claim that CatLab's TheoryJson maps naturally to Omega's data model.

### Test 3.1: Basic Algebraic Theory (Monoid)

**Goal:** Verify that Omega can represent and verify the theory of monoids.

```
Sort: M
Constructors: mu : M × M → M, eta : 1 → M
Rewrite rules:
  assoc: mu(mu(x,y), z) => mu(x, mu(y,z))  -- or as equation
  left_unit: mu(eta, x) => x
  right_unit: mu(x, eta) => x
```

**Required output on success:** Confirmation that all rewrite rules are confluent/terminating, or that the equations hold.

**Required output on intentional failure:** Given a "bad monoid" with `mu : M → M` (wrong arity), does Omega reject it? What error?

### Test 3.2: Algebraic Theory with Position-Normalized Matching

**Goal:** Test whether Omega can handle CatLab's position-normalized matching.

Given target theory (Group) with morphisms:
```
mu : M × M → M   (position §0 × §0 → §0)
eta : 1 → M       (position terminal → §0)
inv : M → M        (position §0 → §0)
```

And a candidate with different names but identical shapes:
```
op : X × X → X
unit : 1 → X
neg : X → X
```

**Question:** Can Omega determine structural equivalence modulo name permutation? Does it have a built-in notion of "shape matching" or would we need to encode it?

### Test 3.3: Ring Theory with Cross-Operation Axioms

**Goal:** Verify distributivity across two operations sharing the same carrier.

```
Sorts: R
Constructors: add : R×R → R, mul : R×R → R, zero : 1→R, one : 1→R, neg : R→R
Axioms (as equations):
  left_distrib:  mul(x, add(y,z)) = add(mul(x,y), mul(x,z))
  right_distrib: mul(add(x,y), z) = add(mul(x,z), mul(y,z))
  add_assoc, mul_assoc, add_comm, left_unit, right_unit, left_inv, right_inv
```

**Critical test:** CatLab's fast path has a known failure mode where two morphisms with the same type (`add : R×R→R` and `mul : R×R→R`) are position-normalized to each other, silently breaking axioms. Does Omega suffer from this? How does it distinguish same-typed operations?

### Test 3.4: Category Theory (The Meta-Level)

**Goal:** Represent the theory of categories itself (not work inside a fixed category).

```
Sorts: Ob, Mor
Constructors:
  src : Mor → Ob
  tgt : Mor → Ob
  id  : Ob → Mor
  comp : Mor × Mor → Mor  (partial: requires tgt(f) = src(g))
Axioms:
  src_id: src(id(x)) = x
  tgt_id: tgt(id(x)) = x
  comp_assoc: comp(comp(f,g), h) = comp(f, comp(g,h))
  left_unit: comp(id(src(f)), f) = f
  right_unit: comp(f, id(tgt(f))) = f
```

**Critical test:** Composition is *partial* — `comp(f,g)` only makes sense when `tgt(f) = src(g)`. Can Omega's judgment/rule system enforce this partiality? Or does everything have to be total?

### Test 3.5: Timeout/Divergence Detection

**Goal:** Test Omega's behavior on circular rewriting.

```
Axioms:
  rule1: f(x) => g(x)
  rule2: g(x) => f(x)
```

**Question:** Does Omega detect the cycle? Does it timeout gracefully? What diagnostic does it produce? CatLab needs bounded normalization (max 200 steps) with a clean "Timeout at depth N" result.

### Test 3.6: Metatheorem-Driven Verification

**Goal:** Test whether Omega's metatheorem mechanism can replace `aesop_cat`.

Given a category with morphisms f, g, h and the associativity axiom, can Omega:
1. Accept `comp(comp(f,g),h) = comp(f,comp(g,h))` as a rewrite rule
2. Automatically verify that `comp(comp(comp(a,b),c),d) = comp(a,comp(b,comp(c,d)))` follows (by repeated application)
3. Report which rules were used in the derivation

This is what `aesop_cat` does for us in Lean. We need an equivalent in Omega.

---

## 4. Test Cases for Hyperion

These test higher-categorical verification — the gap that Lean cannot fill.

### Test 4.1: HoTT — Identity Types and J Elimination

**Goal:** Verify CatLab's `TheoryOfHoTT` (the actual theory from `Catlab/Library/HoTT.lean`).

The theory has 3 sorts (Ctx, Ty, Tm) and 16 morphisms including:
```
Id_ty : Ty × (Tm × Tm) → Ty      -- identity type Id_A(x,y)
refl  : Tm → Tm                    -- reflexivity proof
J_elim : Tm × Tm → Tm              -- path induction eliminator
lam   : Tm → Tm                    -- lambda abstraction
app   : Tm × Tm → Tm               -- application
ua    : Tm → Tm                    -- univalence map
```

Key axioms to verify:
```
J_beta:     J(C, d, refl(x)) = d               -- J computation rule
pi_beta:    app(lam(t), a) = t[a/x]            -- beta reduction
pi_eta:     lam(app(f, var)) = f                -- eta expansion
ua_section: J(ua(e)) = e                        -- univalence is a section
```

**Critical question:** Can Hyperion verify the J-β rule (path induction computes on refl)? This requires dependent elimination — not just equational reasoning but type-directed computation.

**Suggested Hyperion encoding:**
```
[Category CwFWithUnivalence
  [Object Ctx]
  [Object Ty]
  [Object Tm]
  [PathType :refl refl :concat concat :inv inv :ap ap]
  [Evaluator app]
  [Exponential lam :object Tm]
]

[Substrate HomotopyEngine
  @engine interaction-graph
  @equality topological-hash  -- or equality-saturation?
]

[Universe HoTTWorld :category CwFWithUnivalence :substrate HomotopyEngine]
```

**Question:** Does PathType auto-injection give us J, transport, and ap for free? Or do we need to define them manually?

### Test 4.2: (∞,2)-Category — Interchange Law Discovery

**Goal:** Reproduce the Eckmann-Hilton argument from the Hyperion docs using CatLab's actual `TheoryOfInfinityTwoCategory`.

The theory has 3 sorts (Cell0, Cell1, Cell2) with:
- Horizontal composition `comp0 : C1 × C1 → C1`
- Vertical composition `comp1v : C2 × C2 → C2`
- Horizontal 2-cell composition `comp1h : C2 × C2 → C2`
- 2-cell inverses `inv2 : C2 → C2`

The interchange axiom is:
```
(α ∙ β) ∘ (γ ∙ δ) = (α ∘ γ) ∙ (β ∘ δ)
```

**Test A (Verification):** Given the interchange axiom, vertical/horizontal unit laws, and associativity, verify that these are consistent.

**Test B (Discovery — the Eckmann-Hilton punchline):** On an equality-saturation substrate, can Hyperion discover that when comp1v and comp1h share the same unit (degenerate 2-cells), vertical composition is commutative? This is the content of the Eckmann-Hilton theorem. CatLab's fast path cannot discover this — it would require the user to state commutativity explicitly.

**Test C (Substrate comparison):** Run the same theory on `rewrite-equivalence` vs `equality-saturation`. Confirm that the e-graph substrate discovers commutativity but the directed substrate cannot.

### Test 4.3: Cubical Type Theory — Kan Composition

**Goal:** Verify the computational content of cubical type theory.

CatLab's cubical theory (from `CubicalTypeTheory.lean`) includes:
```
Sorts: Ctx, Ty, Tm, I (interval)
Key operations:
  i0, i1 : 1 → I                    -- interval endpoints
  meet, join : I × I → I             -- connections
  path_ty : Ty × I → Ty              -- path type P(i)
  path_abs : Tm → Tm                 -- path abstraction <i> t
  path_app : Tm × I → Tm             -- path application p(i)
  hcomp : Tm × Tm → Tm               -- homogeneous Kan composition
  coe : Tm × I × I → Tm              -- coercion along a line of types

Key axioms:
  path_beta: path_app(path_abs(t), i) = t      -- <i>t applied to i = t
  path_eta:  path_abs(path_app(p, i)) = p       -- extensionality
  hcomp_base: path_app(hcomp(u, a0), i0) = a0   -- hcomp at base = base
  coe_refl: coe(a, i, i) = a                     -- coercion along constant = id
  connection_meet: meet(i0, j) = i0              -- ∧ absorbs 0
  connection_join: join(i1, j) = i1              -- ∨ absorbs 1
```

**Critical question:** Can Hyperion handle the *partial* nature of hcomp? Kan composition is defined only when the partial element agrees on overlaps. This is a constraint on the *tope* (shape), not just on terms.

**Suggested Hyperion encoding:**
```
[Category CubicalCwF
  [Object Ctx]
  [Object Ty]
  [Object Tm]
  [Object Interval]
  [PathType :refl path_abs :concat hcomp :ap coe]
]
```

**Question:** Does Hyperion's PathType capture interval-indexed types natively, or would we need a custom substrate with tope logic?

### Test 4.4: Cohesive HoTT — Modal Adjunction Triple

**Goal:** Verify the adjoint triple ∫ ⊣ ♭ ⊣ ♯ from CatLab's `CohesiveHoTT.lean`.

```
Modal operators on Ty:
  shape : Ty → Ty    -- ∫ (shape modality, "discrete types")
  flat  : Ty → Ty    -- ♭ (flat modality, "codiscrete types")
  sharp : Ty → Ty    -- ♯ (sharp modality, "coreduced types")

Unit/counit:
  shape_unit : Tm → Tm   -- η_∫ : A → ∫A
  flat_counit : Tm → Tm  -- ε_♭ : ♭A → A
  sharp_unit : Tm → Tm   -- η_♯ : A → ♯A

Adjunction axioms:
  shape_flat_adj:  comp(shape_unit, flat_counit) = id    -- ∫ ⊣ ♭ triangle
  flat_sharp_adj:  comp(flat_counit, sharp_unit) = id    -- ♭ ⊣ ♯ triangle

Monad/comonad laws:
  shape_monad_unit: comp(shape_unit, shape_unit) = shape_unit  -- μ_∫ ∘ η_∫ = id
  flat_comonad:     comp(flat_counit, flat_counit) = flat_counit
```

**Question:** Can Hyperion verify the adjunction triangle identities? These are non-trivial — they require showing that composite natural transformations equal identities, which involves naturality squares.

### Test 4.5: Cross-Substrate Transport

**Goal:** Test the claim that theorems discovered on an e-graph substrate can be transported to a directed substrate.

**Setup:**
1. Define the (∞,2)-category theory on an equality-saturation substrate
2. Let it discover Eckmann-Hilton commutativity
3. Transport the discovered equation to a directed-rewriting substrate
4. Verify that the directed substrate can *check* (but not independently discover) the equation

**Question:** What does the transport API look like? Is it a `[Functor]`? Does it preserve proof terms or just normal forms? Can we serialize the transported result back to CatLab's `TheoryJson` format?

---

## 5. Integration Requirements

For either system to work as a CatLab backend, we need:

### 5.1 Programmatic API

CatLab's TypeScript orchestrator needs to:
1. Generate source files from TheoryJson (we write the translator)
2. Invoke the checker via CLI or library call
3. Parse structured error output
4. Map errors back to TheoryJson AST nodes

**Question:** What is the CLI invocation? What is the error output format? Is there a JSON mode?

For Lean, we use: `lean --json <file>` → NDJSON diagnostics on stdout with `{severity, pos, endPos, data}`.

For Rzk, we use: `rzk typecheck <file>` → unstructured text on stderr with `line N: Error occurred when checking #define X`.

**What we need from Omega/Hyperion:**
```json
{"file": "test.omega", "line": 15, "severity": "error", "node": "axiom:assoc",
 "message": "Rewrite rule diverges: f(x) => g(x) => f(x) cycle detected",
 "expected": "comp(mu, mu)", "actual": "stuck term"}
```

### 5.2 Verification Result Schema

CatLab's deep verifier expects results in this shape:

```typescript
type ElaborationStatus =
  | "success"           // All types checked, all axioms verified
  | "semantic_error"    // Type mismatch, arity error, sort error
  | "unverified_axiom"  // Well-typed but couldn't prove an axiom

interface SourceMappedError {
  astNodeId: string;     // e.g., "morphism:mu", "axiom:assoc"
  leanLine: number;      // line in generated source
  message: string;       // human-readable error
  severity: "fatal" | "warning";
}
```

**Question:** Can Omega/Hyperion produce errors mapped to specific declarations (not just line numbers)?

### 5.3 Performance Budget

- Fast path (structural): < 100ms
- Deep path (semantic): < 60 seconds (with 120s hard timeout)
- The LLM feedback loop runs 5 rounds max; each round = 1 fast + 1 deep verification
- Total wall clock per solve: < 5 minutes

**Question:** What are Omega/Hyperion's typical verification times for theories with 5-20 morphisms and 5-15 axioms?

### 5.4 Installation and Deployment

CatLab runs on macOS and Linux. The current Lean dependency is ~2GB (Mathlib oleans).

**Question:** What are the binary sizes? Dependencies? Can we ship a static binary?

---

## 6. Specific Comparison Points

### 6.1 vs. Lean/Mathlib (current backend for 1-categories)

| Capability | Lean/Mathlib | Omega | Hyperion |
|-----------|-------------|-------|----------|
| Library of formalized category theory | ~1M lines (Mathlib) | ? | ? |
| MonoidalCategory typeclass | Yes | Must define | Must define |
| Functor/NatTrans | Yes | Must define | PathType may help |
| aesop_cat (auto-prover) | Yes | Tactics/metatheorems? | Equality saturation? |
| Type-checking morphism compositions | Native | Judgment rules | Category + Substrate |
| Error attribution to AST nodes | Yes (source maps) | ? | ? |

**We do NOT expect Omega/Hyperion to replace Lean for 1-categories.** The question is whether they can handle what Lean cannot.

### 6.2 vs. Rzk (current stub for higher categories)

| Capability | Rzk | Omega | Hyperion |
|-----------|-----|-------|----------|
| Simplicial type theory | Native | Must define | PathType? |
| Directed intervals (2, Δ¹) | Native | Must define | Must define |
| Extension types | Native | Must define | Must define |
| Tope logic (shapes) | Native | ? | Substrate config? |
| Error output format | Unstructured text | ? | ? |
| ∞-groupoid structure | Automatic | Must define | PathType auto-inject |
| Cubical features | No | Must define | Must define |
| Equality saturation | No | No? | Yes (e-graph substrate) |

### 6.3 The Key Question

**Can Hyperion's equality-saturation substrate discover coherence conditions that neither Lean's aesop_cat nor Rzk's directed type-checker can find?**

This is the make-or-break. CatLab's biggest verification gap is:
1. aesop_cat fails on non-trivial coherence (result: `unverified_axiom` with sorry)
2. Rzk can check directed composition but cannot discover equivalences
3. We need something that can *find* proofs in higher-dimensional settings

If Hyperion's e-graph substrate can discover the Eckmann-Hilton theorem from five independent axioms (as claimed in the docs), that would be transformative for CatLab.

---

## 7. Deliverables

After running these tests, please provide:

1. **Source files** for each test case (in Omega/Hyperion syntax)
2. **Raw output** from the checker (stdout + stderr)
3. **Timing data** (wall-clock per test)
4. **Error quality assessment**: Are errors specific enough to map back to TheoryJson nodes?
5. **Gap report**: Which test cases cannot be implemented? Why?
6. **Integration sketch**: What would a `omega-elaborator.ts` / `hyperion-elaborator.ts` look like? How much translation code is needed from TheoryJson → source format?
7. **Recommendation**: For each of CatLab's 25 doctrines, which backend (Lean / Omega / Hyperion / Rzk) is the best fit?

---

## Appendix A: Full TheoryJson for Test Cases

### A.1: TheoryOfHoTT (from Catlab/Library/HoTT.lean)

```json
{
  "name": "HomotopyTypeTheory",
  "doctrine": "MartinLofTypeTheory",
  "objects": [
    {"name": "Ctx", "description": "Contexts"},
    {"name": "Ty", "description": "Types (dependent on a context)"},
    {"name": "Tm", "description": "Terms (dependent on a type)"}
  ],
  "morphisms": [
    {"name": "empty_ctx", "domain": "terminal", "codomain": "Ctx"},
    {"name": "ctx_ext", "domain": {"prod": ["Ctx", "Ty"]}, "codomain": "Ctx"},
    {"name": "wk", "domain": {"prod": ["Ctx", "Ty"]}, "codomain": "Ctx"},
    {"name": "ty_ctx", "domain": "Ty", "codomain": "Ctx"},
    {"name": "tm_ty", "domain": "Tm", "codomain": "Ty"},
    {"name": "var", "domain": {"prod": ["Ctx", "Ty"]}, "codomain": "Tm"},
    {"name": "ty_subst", "domain": {"prod": ["Ty", "Ctx"]}, "codomain": "Ty"},
    {"name": "tm_subst", "domain": {"prod": ["Tm", "Ctx"]}, "codomain": "Tm"},
    {"name": "Id_ty", "domain": {"prod": ["Ty", {"prod": ["Tm", "Tm"]}]}, "codomain": "Ty"},
    {"name": "refl", "domain": "Tm", "codomain": "Tm"},
    {"name": "J_elim", "domain": {"prod": ["Tm", "Tm"]}, "codomain": "Tm"},
    {"name": "Pi_ty", "domain": {"prod": ["Ty", "Ty"]}, "codomain": "Ty"},
    {"name": "lam", "domain": "Tm", "codomain": "Tm"},
    {"name": "app", "domain": {"prod": ["Tm", "Tm"]}, "codomain": "Tm"},
    {"name": "U", "domain": "Ctx", "codomain": "Ty"},
    {"name": "El", "domain": "Tm", "codomain": "Ty"},
    {"name": "ua", "domain": "Tm", "codomain": "Tm"}
  ],
  "axioms": [
    {"name": "subst_ctx", "lhs": {"comp": [{"atom":"ty_subst"}, {"atom":"ty_ctx"}]}, "rhs": {"id": "Ctx"}},
    {"name": "subst_ty", "lhs": {"comp": [{"atom":"tm_subst"}, {"atom":"tm_ty"}]}, "rhs": {"comp": [{"prod": [{"atom":"tm_ty"}, {"id":"Ctx"}]}, {"atom":"ty_subst"}]}},
    {"name": "refl_ty", "lhs": {"comp": [{"atom":"refl"}, {"atom":"tm_ty"}]}, "rhs": {"comp": [{"atom":"Id_ty"}, {"atom":"ty_ctx"}]}},
    {"name": "J_beta", "lhs": {"comp": [{"prod": [{"atom":"refl"}, {"id":"Tm"}]}, {"atom":"J_elim"}]}, "rhs": {"id": "Tm"}},
    {"name": "pi_beta", "lhs": {"comp": [{"prod": [{"atom":"lam"}, {"id":"Tm"}]}, {"atom":"app"}]}, "rhs": {"id": "Tm"}},
    {"name": "pi_eta", "lhs": {"comp": [{"atom":"app"}, {"atom":"lam"}]}, "rhs": {"id": "Tm"}},
    {"name": "ua_section", "lhs": {"comp": [{"prod": [{"atom":"ua"}, {"id":"Tm"}]}, {"atom":"J_elim"}]}, "rhs": {"id": "Tm"}}
  ]
}
```

### A.2: TheoryOfInfinityTwoCategory (from Catlab/Library/InfinityNCategory.lean)

```json
{
  "name": "Infinity2Category",
  "doctrine": "InfinityNCategory",
  "objects": [
    {"name": "Cell0", "description": "0-cells (objects)"},
    {"name": "Cell1", "description": "1-cells (morphisms)"},
    {"name": "Cell2", "description": "2-cells (homotopies)"}
  ],
  "morphisms": [
    {"name": "s0", "domain": "Cell1", "codomain": "Cell0"},
    {"name": "t0", "domain": "Cell1", "codomain": "Cell0"},
    {"name": "s1", "domain": "Cell2", "codomain": "Cell1"},
    {"name": "t1", "domain": "Cell2", "codomain": "Cell1"},
    {"name": "id0", "domain": "Cell0", "codomain": "Cell1"},
    {"name": "id1", "domain": "Cell1", "codomain": "Cell2"},
    {"name": "comp0", "domain": {"prod": ["Cell1", "Cell1"]}, "codomain": "Cell1"},
    {"name": "comp1v", "domain": {"prod": ["Cell2", "Cell2"]}, "codomain": "Cell2"},
    {"name": "comp1h", "domain": {"prod": ["Cell2", "Cell2"]}, "codomain": "Cell2"},
    {"name": "inv2", "domain": "Cell2", "codomain": "Cell2"}
  ],
  "axioms": [
    {"name": "glob_s", "lhs": {"comp": [{"atom":"s1"}, {"atom":"s0"}]}, "rhs": {"comp": [{"atom":"t1"}, {"atom":"s0"}]}},
    {"name": "glob_t", "lhs": {"comp": [{"atom":"s1"}, {"atom":"t0"}]}, "rhs": {"comp": [{"atom":"t1"}, {"atom":"t0"}]}},
    {"name": "id0_s", "lhs": {"comp": [{"atom":"id0"}, {"atom":"s0"}]}, "rhs": {"id": "Cell0"}},
    {"name": "id0_t", "lhs": {"comp": [{"atom":"id0"}, {"atom":"t0"}]}, "rhs": {"id": "Cell0"}},
    {"name": "id1_s", "lhs": {"comp": [{"atom":"id1"}, {"atom":"s1"}]}, "rhs": {"id": "Cell1"}},
    {"name": "id1_t", "lhs": {"comp": [{"atom":"id1"}, {"atom":"t1"}]}, "rhs": {"id": "Cell1"}},
    {"name": "left_unit0", "lhs": {"comp": [{"prod": [{"atom":"id0"}, {"id":"Cell1"}]}, {"atom":"comp0"}]}, "rhs": {"id": "Cell1"}},
    {"name": "right_unit0", "lhs": {"comp": [{"prod": [{"id":"Cell1"}, {"atom":"id0"}]}, {"atom":"comp0"}]}, "rhs": {"id": "Cell1"}},
    {"name": "assoc0", "lhs": {"comp": [{"prod": [{"atom":"comp0"}, {"id":"Cell1"}]}, {"atom":"comp0"}]}, "rhs": {"comp": [{"prod": [{"id":"Cell1"}, {"atom":"comp0"}]}, {"atom":"comp0"}]}},
    {"name": "vert_unit", "lhs": {"comp": [{"prod": [{"atom":"id1"}, {"id":"Cell2"}]}, {"atom":"comp1v"}]}, "rhs": {"id": "Cell2"}},
    {"name": "vert_assoc", "lhs": {"comp": [{"prod": [{"atom":"comp1v"}, {"id":"Cell2"}]}, {"atom":"comp1v"}]}, "rhs": {"comp": [{"prod": [{"id":"Cell2"}, {"atom":"comp1v"}]}, {"atom":"comp1v"}]}},
    {"name": "inv2_right", "lhs": {"comp": [{"prod": [{"id":"Cell2"}, {"atom":"inv2"}]}, {"atom":"comp1v"}]}, "rhs": {"comp": [{"atom":"s1"}, {"atom":"id1"}]}},
    {"name": "interchange", "lhs": {"comp": [{"prod": [{"atom":"comp1h"}, {"atom":"comp1h"}]}, {"atom":"comp1v"}]}, "rhs": {"comp": [{"prod": [{"atom":"comp1v"}, {"atom":"comp1v"}]}, {"atom":"comp1h"}]}}
  ]
}
```

---

## Appendix B: Current Architecture Diagram

```
                    ┌─────────────────────┐
                    │   LLM (Claude)      │
                    │  Proposes TheoryJson │
                    └──────┬──────────────┘
                           │
                    ┌──────▼──────────────┐
                    │  TypeScript          │
                    │  Orchestrator        │
                    │  (solver.ts)         │
                    └──────┬──────────────┘
                           │
              ┌────────────┼────────────────┐
              ▼            ▼                ▼
    ┌─────────────┐ ┌────────────┐  ┌──────────────┐
    │ Fast Path   │ │ Deep Path  │  │ Higher Path  │
    │ (Lean REPL) │ │ (Lean      │  │ (STUB:       │
    │ Structural  │ │  /Mathlib)  │  │  returns     │
    │ rewriting   │ │ Type-check │  │  "pending")  │
    │ <100ms      │ │ <60s       │  │              │
    └─────────────┘ └────────────┘  └──────────────┘
    20 doctrines    20 doctrines     5 doctrines
    All operators   All operators    NO verification
```

**Proposed with Omega/Hyperion:**

```
              ┌────────────┼────────────────┐
              ▼            ▼                ▼
    ┌─────────────┐ ┌────────────┐  ┌──────────────┐
    │ Fast Path   │ │ Deep Path  │  │ Higher Path  │
    │ (Lean REPL) │ │ (Lean      │  │ Omega or     │
    │ OR Omega    │ │  /Mathlib)  │  │ Hyperion     │
    │ (algebraic  │ │ (1-cats)   │  │ (∞-cats,     │
    │  theories)  │ │            │  │  HoTT,       │
    │             │ │            │  │  coherence)   │
    └─────────────┘ └────────────┘  └──────────────┘
```
