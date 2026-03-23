# CatLab

A **computer algebra system for categorical theories**, implemented in Lean 4.

Where a classical CAS operates on polynomials and numbers, CatLab operates on *theories* — categorical presentations of mathematical structures. Every operator is deterministic and composable. Every result is a first-class `Theory` value that can be inspected, further transformed, or verified.

---

## The Algebra of Theories

CatLab is organized around a four-tier architecture:

**Tier 1 — Primitives & Symmetries**
The foundation: `Theory`, `TheoryMorphism`, `InitialTheory` (⊥), `TerminalTheory` (⊤), `Opposite`, `Mirror`.

**Tier 2 — Combinators (The Colimit/Limit Engine)**
The algebraic operations on theories:
- `pushout f g` — amalgamated sum T₁ ⊔_{T₀} T₂ (the fundamental combinator)
- `theoryPullback f g` — fibered product T₁ ×_{T₃} T₂ (the dual: "diff" / "intersection")
- `tensorTheories` — Freyd/Kronecker product for commuting structures
- `theoryCoproduct` — disjoint union, derived as `pushout` over ⊥
- `theoryProduct'` — product, derived as `pullback` over ⊤
- `quotientCategory` — derived as `pushout` along an inclusion

**Tier 3 — Categorical Constructors**
Derived semantics with structural content: `FunctorCategory` (three functor-objects F/G/H, naturality squares for α and β, vertical composition, left/right unit laws), `Comma` (comma morphisms, commutativity squares), `Grothendieck` (projection functors, naturality axioms, identity morphisms, identity laws), `Limits`/`Colimits` (full universal properties: existence + uniqueness axioms, proper η-laws encoding `⟨π₁ ∘ h, π₂ ∘ h⟩`), `Slice`, `Model`, `Decategorify` (isoClasses with axiom translation, K₀ with additivity, Euler characteristic with additivity).

**Tier 4 — Advanced Applications**
Specialized constructions: `Dialectica`, `TriposToTopos`, `Realizability`, `MacNeille`, `Skolem`, `Truncate` (higher-categorical truncation), `TheoryFamily` (dependent theories / fibered theory families), and 50+ others.

### Theory Morphisms

`TheoryMorphism` is a first-class type — explicit, inspectable maps between theories:

```lean
-- Identity and composition
TheoryMorphism.id t
TheoryMorphism.comp f g

-- Smart inclusion: maps generators by matching names
TheoryMorphism.inclusion Monoid Group

-- Pushout: amalgamate two theories over a shared base
pushout (inclusion Monoid Group) (inclusion Monoid Ring)
-- → a theory with both Group and Ring structure, Monoid generators identified
```

### Pullback (Fibered Product)

The dual of pushout. Where pushout merges two theories over a shared base (amalgamated sum), pullback extracts the maximal shared sub-structure:

```lean
-- Pullback: the largest theory mapping into both T₁ and T₂ compatibly over T₃
theoryPullback (inclusion base T₁) (inclusion base T₂)

-- Product as pullback over ⊤ (terminal theory)
theoryProduct' T₁ T₂  -- = pullback (terminalMorphism T₁) (terminalMorphism T₂)

-- PullbackCone: apex + projection morphisms π₁, π₂
pullbackCone f g  -- returns { apex, leftProj : P → T₁, rightProj : P → T₂ }
```

Algorithm: pair objects where `f(x) = g(y)` in T₃, pair morphisms where images match and domains/codomains are paired, pair axioms where translated equations agree.

### Dependent Theories (TheoryFamily)

A `TheoryFamily` parameterizes theories over a base — instead of hardcoding hundreds of variants, you define a single family and instantiate it:

```lean
-- Extract Module as a family over Ring
let family := extractFamily TheoryOfRings (TheoryOfModules "R") "Module"

-- Instantiate with ℤ: smul becomes ℤ × M → M instead of R × M → M
let intMod := family.instantiate "ℤ" model
-- intMod.name = "Module(ℤ)"
```

Key types:
- **`SyntacticModel`** — a lightweight assignment of concrete Exprs to a theory's generators
- **`TheoryFamily`** — `{ base : Theory, fiberOf : SyntacticModel → Theory }`
- **`extractFamily`** — given a base B and total theory T extending B, automatically separates base from fiber using domain/codomain analysis
- **`flatten`** / **`instantiate`** — substitute a model into the fiber, producing a standalone Theory
- **`totalTheory`** — merge base + generic fiber into one Theory

### Doctrine Inference

CatLab automatically infers the minimum doctrine from a theory's AST structure, so the LLM doesn't need to get doctrine labels right:

```lean
-- Bottom-up constraint collection from Expr constructors:
--   prod/terminal → CartesianCategory
--   tensor       → MonoidalCategory
--   hom          → CartesianClosed
--   coprod       → FinitelyCocomplete
--   sigma/pi     → MartinLofTypeTheory

-- Auto-upgrade: if the LLM says "Category" but uses prod/coprod,
-- the doctrine is automatically upgraded to CartesianCategory
let upgraded := theory.autoUpgradeDoctrine
```

The doctrine lattice (`Doctrine.join`) handles special cases like Cartesian + Monoidal = Cartesian, FinitelyComplete + FinitelyCocomplete = Abelian.

---

## Inverse Problems & The LLM Loop

CatLab includes a unified framework for **inverse problems**: finding an unknown theory `X` such that some forward operator applied to `X` produces a target theory `T`.

```
find X such that forwardOperator(X) ≅ Target
```

| Problem | Unknown X | Forward operator | Target |
|---|---|---|---|
| Categorification | higher theory C | `decategorify` | algebraic theory (e.g. ℕ-rig → FinSet) |
| Morita context | bimodule M | `moritaCheck` | (T₁, T₂) equivalence |
| Internalization | morphism f | `f.preservesTyping` | valid embedding |
| Pushout complement | theory X | `pushout f X` | amalgamated theory |

### Architecture

```
Proposer (LLM or search)
  → produces List Theory candidates

CAS Verifier (deterministic)
  → applies forwardOp to each candidate
  → computes VerificationResult (structured diff)

LLM reads diff, refines proposal
  → next round
```

The key insight: **verification is always cheaper than discovery**. The CAS owns verification permanently; the LLM or a search procedure owns proposal generation.

### The Structured Diff

`VerificationResult` is designed to be the primary input to the LLM's next proposal:

```lean
structure VerificationResult where
  verified          : Bool
  status            : VerificationStatus   -- Success | Failed reason | Timeout depth
  missingSignatures : List MorphismSignature  -- morphisms required by target, absent in produced
  unmappedObjects   : List Name               -- objects the LLM hallucinated
  axiomViolations   : List AxiomViolation     -- axioms that don't hold, with partial reductions + rewrite traces
```

Three traps addressed explicitly:

- **Rich timeout diagnostics.** When Knuth-Bendix times out, the LLM receives partial normal forms, rewrite traces (last 10 axiom names that fired), and cycle detection (rules firing 3+ times indicate looping). This gives the LLM actionable gradient signal instead of a blind "Timeout at depth N".

- **Verification is bounded, not decidable.** CatLab checks *strict presentation isomorphism* — same generator counts, matching domain/codomain shapes (position-normalized), and axioms that reduce to the same normal form under bounded term rewriting. This is not categorical equivalence: two presentations of the same mathematical structure (related by Tietze transformations) will be rejected if their generator counts or expression shapes differ. Checking full categorical equivalence is undecidable in general (it reduces to the Word Problem). `VerificationStatus.Timeout depth` reports "I tried N rewriting steps and couldn't prove this" rather than falsely reporting failure — an unavoidable consequence of the bounded Word Problem. The LLM is expected to match the target's presentation structure, not discover arbitrary equivalent presentations.

- **Comp-reversing operators.** Operators like `opposite` and `mirror` reverse the direction of composition. For involutions, CatLab uses a **contravariant verification strategy**: instead of diffing `op(X)` against `T`, it diffs `X` against `op(T)`. This is a heuristic that keeps the rewriter's axiom orientation aligned with the candidate's composition direction, improving convergence of the bounded Knuth-Bendix procedure in practice. It does not solve the underlying Word Problem — if the rewrite system diverges in one orientation, it may also diverge in the other. The benefit is empirical: it avoids a common class of non-termination where the rewriter expands `comp(comp(comp(...)))` chains indefinitely due to misaligned orientation.

- **The alias problem.** If the target requires an object named `State` and the LLM proposes `System`, a name-based diff wastes an API call on a trivial rename. CatLab diffs by **structural signatures**: position-normalized Expr shapes invariant under generator renaming. "Missing morphism `§0 → §1 ⊗ §0`" rather than "Missing morphism `η`."

### The Categorification Example

Categorification as implemented here is strictly algebraic: given a 1-categorical theory `T`, find a higher theory `C` whose `decategorify` recovers `T`'s presentation. This is *not* the deep topological categorification of knot invariants (Khovanov homology categorifies the Jones polynomial via chain complexes assigned to link diagrams, which is far beyond what a finite presentation engine can express). Instead, CatLab handles the algebraic case well:

```lean
-- Categorify ℕ-as-a-rig: find C such that decategorify(C) ≅ CommutativeMonoid
-- Answer: the theory of finite sets (FinSet), where
--   objects (finite sets) → generators of CommutativeMonoid
--   bijections between sets → equations (|A×B| = |A|·|B|, |A⊔B| = |A|+|B|)

evaluateAll (target := TheoryOfCommutativeMonoid)
            (forward := fun c => some (decategorify c .isoClasses))
            (candidates := [proposal1, proposal2, proposal3])

-- Proposal 1: failed to compile (missing counit)
-- Proposal 2: compiled, wrong structure (axiom violation)
-- Proposal 3: verified ✓
```

---

## Three-Tier Verification

CatLab uses three complementary verification backends, routed automatically by doctrine. All share the same `TheoryJson` wire format — the solver loop and LLM don't need to know which backend is running.

```
TheoryJson ──┬── Omega     (algebraic doctrines)       ~1ms
             ├── Lean/Mathlib (1-categorical doctrines) ~seconds
             └── Hyperion  (higher-categorical doctrines) ~5ms
```

### Omega — Equational Verification

[Omega](https://github.com/omega-logic/omega) is a logic-agnostic proof kernel where the type theory itself is user-defined as sorts, constructors, judgments, and rewrite rules. CatLab translates `TheoryJson` into `.omega` source and pipes it via `echo '<source>' | omega check --json --stdin`.

**Doctrines routed to Omega:** LawvereTheory, AlgebraicTheory, CartesianClosed, FiniteProduct, MonoidalCategory.

**Features used:**
- **AC attributes** — `(attribute op :ac)` for commutative operations. Hash-consing canonicalization makes `op(a,b)` and `op(b,a)` definitionally equal, eliminating entire classes of commutativity proofs for rings, lattices, etc.
- **`auto` tactic** — bounded depth-first search through rules. Proofs use `(try (eq-refl) (auto 10))` so multi-step equational reasoning succeeds where normalization alone fails.
- **Lemmas (cut rule)** — proven conclusions are registered as derived rules, enabling incremental theory building for complex verifications.
- **`@node` annotations** — AST node ID passthrough (`axiom:assoc`, `morphism:mu`) for error attribution back to `TheoryJson`.

**Why Omega over CatLab's built-in rewriter:** Omega matches on constructor names, not types, so same-typed operations (e.g., `add` and `mul` in a ring, both `R × R → R`) are never confused. Normalization is bounded (configurable fuel) with clean error messages on exhaustion, not hangs.

### Lean/Mathlib — Deep Categorical Verification

The existing deep path: translates `TheoryJson` into `.lean` source with Mathlib imports, runs the Lean compiler, and maps diagnostics back to AST node IDs. Used for doctrines with deep Mathlib library coverage (Category, Abelian, Topos, etc.).

### Hyperion — Higher-Categorical Coherence Discovery

[Hyperion](https://github.com/omega-logic/hyperion) is a meta-framework that compiles mathematical structures onto computational substrates. Its key capability is **equality saturation via e-graphs**: given a set of axioms, Hyperion can autonomously discover non-obvious equalities that directed search (Lean's `aesop_cat`, type-checking) cannot find.

**Doctrines routed to Hyperion:** MartinLofTypeTheory, InfinityNCategory, PresentableInfinityCategory, CubicalTypeTheory, CohesiveHomotopyTypeTheory, 2Category, Double, Bicategory.

**Features used:**
- **Equality saturation** — the e-graph substrate discovers theorems, not just verifies them. From 5 independent axioms (interchange + unit laws), Hyperion autonomously discovers the Eckmann-Hilton theorem: that vertical composition is commutative. Neither Lean's `aesop_cat` nor directed type-checking can find this.
- **`PathType` auto-injection** — declaring `[PathType :refl R :concat C :inv I :ap A]` auto-injects 4-5 rewrite rules (unit laws, associativity, inverse, functoriality), covering HoTT's ground-level path algebra.
- **`JType` auto-injection** — adds J-beta and transport-refl rules for Martin-Lof type theory.
- **`PartialElement` auto-injection** — adds hcomp/coe rules for cubical type theory.
- **`ModalOperator`** — for cohesive HoTT's shape/flat/sharp adjoint triple.
- **Substrate comparison** — the same theory on different substrates has different provability. CatLab uses this for "try harder" semantics: start with directed rewriting, escalate to e-graph. `assert-neq` on the directed substrate confirms which equalities genuinely require e-graph discovery.
- **`Functor :verify`** — verifies that doctrine morphisms preserve equational structure.
- **`eval-simplify`** — extracts canonical forms from the e-graph, giving CatLab simplified representatives.

**Why Hyperion matters:** CatLab has 5 higher-categorical doctrines that were previously stubs — no verification backend could handle them. Hyperion fills this gap. The Eckmann-Hilton result is the concrete proof: directed search provably cannot derive commutativity from interchange + unit laws, but e-graph saturation discovers it in 0.23s. This is the difference between "we can verify what you already know" and "we can discover what you didn't know."

### Implementation

All Omega and Hyperion interaction is centralized in `ts/src/external-elaborators.ts`:
- `routeToExternal(theory)` — determines backend by doctrine
- `theoryToOmega(theory)` / `theoryToHyperion(theory)` — source generation
- `elaborateExternal(theory, opts)` — CLI invocation via stdin, JSON response parsing
- Automatic integration into `elaborate()` in `lean-elaborator.ts`

---

## Library

33 registered library theories covering algebra, topology, logic, and higher category theory (plus `InfinityCategory`, defined but not yet registered in the REPL):

**Algebra:** Monoid, Group, AbelianGroup, Ring, CommutativeRing, Semiring, Module, HopfAlgebra, LieAlgebra, DifferentialGradedAlgebra

**Order/Logic:** Poset, Lattice, BooleanAlgebra, HeytingAlgebra, LinearLogic, GeometricLogic

**Category Theory:** Category, SymmetricMonoidalCategory, EnrichedCategory, AbelianCategory, TriangulatedCategory, ModelCategory, Derivator, Locale

**Higher Structures (strictified presentations):** ElementaryTopos, InfinityTopos, HoTT, CohesiveHoTT, CubicalTypeTheory, InfinityCategory, InfinityTwoCategory, Multicategory, SymmetricOperad, CategoriesWithAttributes

> **Higher-categorical theories.** The library entries for HoTT, CohesiveHoTT, CubicalTypeTheory, and InfinityTopos are *strictified 1-categorical presentations* of the type theory's syntactic signature. However, the core AST now supports genuine HoTT constructs: `path` types (identity types), `univ n` (Russell-style universe hierarchy), dependent types (`pi`, `sigma`), path induction (`pathJ`), and Higher Inductive Types via `HITDecl` (with point and path constructors). Operators like `homotopyPushout`, `homotopyCoproduct`, and `homotopySuspension` compute homotopy colimits as HITs — not strict 1-categorical colimits. Propositional/set truncation, equivalence types (`Equiv A B`), the univalence axiom (`ua`/`idToEquiv`), and the subobject classifier Ω are defined as Theory-level macros composing these primitives.
>
> **Truncation support.** Higher theories carry a `truncationLevel` in their `DoctrineContext` (e.g., `some 2` for (∞,2)-Category). The `truncate n` operator explicitly reduces a higher theory to level n by keeping k-cells for k ≤ n and filtering morphisms/axioms that reference removed cells. This makes the relationship between higher and lower theories computationally explicit.

---

## Testing Philosophy & Results

CatLab treats testing as an algebra problem: if theories form an algebra with operators as its combinators, the test suite should verify that this algebra is *closed* — every operator applied to every theory produces a well-formed result. This goes beyond unit testing individual operators; it tests the **combinatorial surface** of operators × theories × compositions.

### Validation: The Structural Type-Checker

`validate : Theory → List ValidationError` is the core invariant enforcer. It checks five properties:

1. **No duplicate names** — every generator (object, morphism, axiom) has a unique name
2. **Morphism references** — every atom in a morphism's domain/codomain refers to a declared generator
3. **Axiom references** — every atom in an axiom's left/right path refers to a declared generator
4. **Doctrine constraints** — e.g. Lawvere theories must have at least one sort
5. **Composition boundaries** — for every `comp f g`, the codomain of `f` matches the domain of `g`

Every theory produced by every operator must pass all five checks. This is enforced at build time — a validation failure is a build failure.

### Test Matrix

| Test Suite | What It Tests | Scale | Result |
|---|---|---|---|
| **Library validation** | All 33 library theories pass `validate` | 33 | **33/33** |
| **Unary operators × theories** | 15 operators × 33 theories | 495 | **495/495** |
| **Binary operators × theory pairs** | product, coproduct, tensor × 6×6 pairs | 108 | **108/108** |
| **Involution: opposite²** | `opposite(opposite(t))` structurally isomorphic to original (name-map verified) | 33 | **33/33** |
| **Involution: mirror²** | `mirror(mirror(t))` structurally isomorphic to original (shape-equivalent) | 33 | **33/33** |
| **Involution validation** | `opposite²(t)` and `mirror²(t)` pass `validate` | 66 | **66/66** |
| **Composition chains** | 10 two-deep operator compositions × 3 theories | 30 | **30/30** |
| **Idempotency** | `op(op(t))` has no duplicate names (karoubi, morita, stabilize, exact, family) | 5 | **5/5** |
| **Monotonicity** | Enriching operators (karoubi, morita, exact, syntactic) don't lose generators | 132 | **132/132** |
| **Axiom preservation** | Operators that include `t.axioms` don't drop them | 165 | **165/165** |
| **Non-emptiness** | No operator produces a theory with 0 objects and 0 morphisms | 495 | **495/495** |
| **Fuzz: all ops × random theories** | 15 operators × 20 random theories (xorshift32 PRNG) | 300 | **300/300** |
| **Fuzz: operator chains** | Depth 2-3 chains of lightweight ops × 20 random theories | 20 | **20/20** |
| **Fuzz: binary × random pairs** | product/coproduct/tensor × 15 random theory pairs | 45 | **45/45** |
| **Fuzz: mixed chains** | Unary + binary depth 2-3 × 15 random theories | 15 | **15/15** |
| **Fuzz: degenerate inputs** | Empty/point/arrow/loop × all unary + binary ops | 108 | **108/108** |
| **Category A** | Unary operator smoke tests + shape invariants × 33 theories | ~1000 | all pass |
| **Category B** | Binary operator smoke tests × theory pairs | ~200 | all pass |
| **Category C** | Operators with complex inputs (monads, functors, localizations) | ~100 | all pass |
| **Category D** | Tier 2 combinators × 33×33 pairs; algebraic laws (pushout over ⊥ = coproduct) | ~1200 | all pass |
| **Properties** | Mathematical laws: mirror involution, tensor commutativity, Morita reflexivity | ~50 | all pass |
| **Negative validation** | Malformed theories rejected: duplicate names, undeclared refs, doctrine violations, boundary mismatches | 22 | **22/22** |
| **TS verifier unit tests** | All 18 Verifier classes: preflight, verify, formatFeedback, validatePayload | 54 | **54/54** |
| **TS solver unit tests** | GenericSolver state machine: success, refinement, exhaustion, error classification, retries | 9 | **9/9** |
| **TS client unit tests** | NDJSON protocol: concurrency, timeouts, malformed input, process exit, post-kill | 8 | **8/8** |
| **JSON roundtrip** | `toJson(fromJson(toJson(t)))` is stable for all 33 theories + operator outputs | ~40 | all pass |
| **Doctrine roundtrip** | `doctrineFromStr(doctrineToStr(d)) == d` for all 28 doctrine variants | 28 | **28/28** |
| **Expr JSON roundtrip** | All Expr constructors survive `exprToJson` → `exprFromJson` → `exprToJson` | 14 | **14/14** |
| **TheoryMorphism laws** | Identity, composition, self-inclusion, signatureMatch reflexivity | ~70 | all pass |
| **TS integration** | Wire protocol: TheoryJson shapes, ExprJson types, VerificationResult format, concurrent requests, error responses | 10 | **10/10** |
| **Functoriality (structural)** | opposite/mirror structural involutions verified via name-map and shape-equivalence; mirror swaps product↔coproduct at expression level; commutativity of binary ops | ~60 | all pass |
| **Limits/Colimits** | Product/coproduct/pullback/pushout/equalizer/coequalizer/general limit/colimit: morphism counts, axiom counts (including uniqueness), quantifier presence, η-law encoding, domain/codomain correctness, duality | 36 | **36/36** |
| **Coherence** | Naturality axiom presence in functor categories, monoidal coherence (pentagon/triangle/hexagon), isomorphism axioms, quantifier usage | 16 | **16/16** |
| **Higher-categorical** | Truncation metadata, strictified flags, truncation validity, cell count reduction, doctrine preservation, isHigherCategorical classification | 27 | **27/27** |
| **TheoryFamily** | SyntacticModel substitution, generic fiber, flatten, extractFamily (Module/Ring), totalTheory, ℤ-Module instantiation | 20 | **20/20** |
| **Mutation testing** | 7 mutant operators (broken opposite, mirror, drop axioms/morphisms, duplicate names) all caught by existing checks | ~40 | all pass |

**Total: ~5,314 assertions, 0 failures.**

### What the Tests Catch

The test suite is designed to catch specific classes of bugs that arise in categorical construction code:

- **Undeclared references.** An operator creates morphisms whose domain/codomain mention objects it forgot to include in the output. (The most common bug — found in 10+ operators.)
- **Composition boundary mismatches.** An axiom states `f ∘ g = h` but the codomain of `f` doesn't match the domain of `g`. Catches incorrect use of `.comp` when the intended operation is internal composition.
- **Duplicate names under iteration.** Applying `karoubi(karoubi(t))` — the second application re-derives generators that already exist from the first. Caught by the idempotency test.
- **Generator loss.** An operator that should enrich a theory (add structure) accidentally drops original objects, morphisms, or axioms. Caught by monotonicity and axiom preservation tests.
- **Interaction bugs.** `center(opposite(t))` might be valid even though `center(t)` and `opposite(t)` are individually valid — the composition can expose assumptions about expression shapes. Caught by composition chain tests.
- **Structural involution failures.** Involution tests go beyond count preservation: `opposite²(t)` is verified structurally isomorphic to `t` via explicit name mappings (`Theory.structuralMatch`), and `mirror²(t)` via shape-equivalence (name-erased multiset comparison of morphism/axiom shapes). This catches bugs where counts match but expression structure diverges.
- **Missing universal properties.** Limit/colimit operators are tested for complete universal property structure: correct morphism counts (projections + mediating), quantified axiom schemas with proper variable domains, and duality between limits and colimits.
- **Coherence violations.** The coherence checker verifies that functor categories have naturality axioms, monoidal categories satisfy pentagon/triangle/hexagon identities, and isomorphism axioms come in inverse pairs.
- **Compound domain handling.** Binary operators (product, tensor) must correctly handle morphisms with compound domains like `M × M`. Product uses `Expr.prod` to preserve compound structure (atoms resolve recursively). Tensor filters interchange axioms to endomorphisms of the base object. Both tag component generators with `inl`/`inr` to avoid name collisions when combining theories that share names.
- **Random theory robustness.** A deterministic fuzzer (xorshift32 PRNG) synthesizes random well-formed theories and feeds them through single operators, depth 2-3 chains, binary combinations, and mixed unary+binary chains. Catches edge cases that curated library theories don't expose: degenerate inputs (empty/single-object), unusual morphism topologies, and deeply nested compound expressions.
- **Negative validation.** Adversarial theories with duplicate names, dangling references, doctrine violations, and boundary mismatches must be *rejected* by `validate`. Tests verify that error types are correct and that operators propagate (not mask) input errors.
- **TypeScript unit tests.** The TS orchestrator is tested independently of the Lean CAS using mock clients: all 18 Verifier classes (preflight schemas, CAS result pass-through, error handling, custom feedback/validation), the GenericSolver state machine (success paths, exhaustion, error classification, retries, progress events), and the NDJSON client (concurrent requests, timeouts, malformed input, process lifecycle).

### Mathematical Completeness

The following operators encode their full mathematical content (not just generator shapes):

- **Limits/Colimits.** Products and coproducts have properly encoded η-laws (`⟨π₁ ∘ h, π₂ ∘ h⟩ = h` via `Expr.app`, not a bare atom). Pullbacks and pushouts include uniqueness axioms alongside existence, giving full universal properties.
- **FunctorCategory.** Three functor-objects (F, G, H) with explicit natural transformations α : F ⟹ G and β : G ⟹ H, naturality squares for both, vertical composition law, identity law, and left/right unit laws.
- **Grothendieck.** Identity morphisms for total objects and identity law axioms ensuring the projection functor preserves identities.
- **ElementaryTopos.** Exponential β/η-rules (quantified over morphisms), product β-laws, characteristic map source axiom. The subobject classifier's classifying square is axiomatized.
- **Yoneda.** Representable presheaves carry functoriality axioms (`id* = id`, `(g ∘ f)* = f* ∘ g*`). The presheaf category doctrine is honestly reported as `Category` rather than overclaiming `GrothendieckTopos`.
- **Kan extensions.** Both left and right Kan extensions have dinaturality axioms (coend/end conditions). Left Kan no longer references undeclared generators.
- **Decategorify.** The `isoClasses` strategy translates object-referencing axioms through the `[X]` renaming rather than dropping them. The `grothendieckGroup` strategy emits additivity axioms `[A ⊔ B] = [A] + [B]` when coproduct structure is present. The `eulerCharacteristic` strategy has `χ(A ⊕ B) = χ(A) + χ(B)`.
- **Morita.** Equivalence checking uses structural isomorphism of Cauchy completions (not just signature comparison). Presheaf equivalence data includes unit/counit axioms.
- **Alpha-equivalence.** Bijective mapping tracking — the checker records and enforces consistency of the name bijection, preventing false positives from unmapped atoms.
- **Theory isomorphism.** Permutation search for theories with ≤ 6 objects; degree-based heuristic for larger theories. Replaces the previous identity-only check.
- **`preservesTyping`.** Actually verifies that mapped morphisms have the expected domain/codomain in the target theory.

---

## Running the Solver

The TypeScript orchestrator in `ts/` drives the LLM ↔ CAS feedback loop. The solver is fully generic — it treats the LLM's output as an opaque payload and delegates all verification, feedback formatting, and schema definition to pluggable **Verifiers**.

### Setup

```bash
cd ts
npm install && npm run build

# Create .env with your Anthropic API key
echo "ANTHROPIC_API_KEY=sk-ant-..." > .env

# Build the Lean REPL (first time only)
cd .. && lake build catlab-repl && cd ts
```

### Running Tests

**Lean tests** (runs all `#eval` test blocks during build):

```bash
lake build
```

**TypeScript unit tests** (no Lean or API key needed):

```bash
cd ts
npx tsx test/verifiers.test.ts   # 54 verifier tests
npx tsx test/solver.test.ts      # 9 solver tests (needs @anthropic-ai/sdk installed)
npx tsx test/client.test.ts      # 8 NDJSON client tests
npm run test:unit                # all unit tests
```

**TypeScript integration tests** (requires Lean REPL built):

```bash
lake build catlab-repl           # build REPL first
cd ts && npx tsx test/integration.test.ts
```

> **Note:** The solver test for `AuthenticationError` propagation imports `@anthropic-ai/sdk` at the module level. No API key is needed — only the SDK package must be installed (`npm install`). The `.env` file with `ANTHROPIC_API_KEY` is only required for actually running the solver against Claude.

### Problem Types (18 total)

| Problem | Status | Command | What it solves |
|---------|--------|---------|----------------|
| **Inverse** | ✅ | `catlab-solve <theory> <op>` | find X s.t. op(X) ≅ target |
| **Fixed-point** | ✅ | `--problem fixed-point --target <T> --op <op>` | find X s.t. op(X) ≅ X |
| **Pushout complement** | ✅ | `--problem pushout-complement --base <T> --target <T>` | find X s.t. pushout(base, X) ≅ target |
| **Pullback complement** | ✅ | `--problem pullback-complement --base <T> --target <T>` | find X s.t. pullback(base, X) ≅ target |
| **Extension** | ✅ | `--problem extension --base <T> --property <P>` | find X extending base with property P |
| **Interpolation** | ✅ | `--problem interpolation --base <T> --target <T>` | find X with base ↪ X → target |
| **Simplification** | ✅ | `--problem simplify --target <T>` | find minimal X ≅ target |
| **Model finding** | ✅ | `--problem model-finding --target <T>` | generate concrete instance of a theory |
| **Synthesis** | ✅ | `--problem synthesis --base <T> --source <A> --target <B>` | find morphism composition A → B |
| **Quotient** | ✅ | `--problem quotient --base <T> --property <P>` | find minimal quotient satisfying P |
| **Relaxation** | ✅ | `--problem relax --target <T> --property <P>` | find X closest to target satisfying P |
| **Sub-object** | ✅ | `--problem subobject --target <T> --property <P>` | find sub-theory satisfying P |
| **Decomposition** | ✅ | `--problem decompose --target <T>` | find components s.t. ⨁ Xᵢ ≅ target |
| **Catalyst** | ✅ | `--problem catalyst --source <A> --target <B>` | find C s.t. A⊗C → B⊗C |
| **Compose** | ✅ | `--problem compose --constraints "<spec>"` | find X satisfying ALL constraints |
| **Multi-objective** | ✅ | `--problem multi --objectives "<T>:<op>,..."` | find X satisfying multiple inverse constraints |
| **Factorization** | ✅ | `--problem factorization --target <T>` | find (X,Y) s.t. X⊗Y ≅ target |
| **Optimization** | ✅ | `--problem optimization --target <T> --op <op> --property <P>` | minimize cost subject to op(X)≅target |

### Composition

The **compose** problem type combines any of the above constraints into a single search. The LLM must find one theory satisfying all constraints simultaneously. Constraints are specified as `type:arg1:arg2` separated by `+`:

```
type:arg1:arg2+type:arg1:arg2+...
```

Available constraint types and their arguments:

| Constraint | Format | Example |
|------------|--------|---------|
| `inverse` | `inverse:<target>:<op>` | `inverse:Monoid:opposite` |
| `fixed-point` | `fixed-point:<target>:<op>` | `fixed-point:Monoid:opposite` |
| `pushout-complement` | `pushout-complement:<base>:<target>` | `pushout-complement:Monoid:Group` |
| `pullback-complement` | `pullback-complement:<base>:<target>` | `pullback-complement:Monoid:Group` |
| `extension` | `extension:<base>:<property>` | `extension:Monoid:has_inverses` |
| `interpolation` | `interpolation:<base>:<target>` | `interpolation:Monoid:Group` |
| `simplify` | `simplify:<target>` | `simplify:Monoid` |
| `subobject` | `subobject:<target>:<property>` | `subobject:Group:has_inverses` |
| `quotient` | `quotient:<base>:<property>` | `quotient:Group:commutative` |
| `relax` | `relax:<target>:<property>` | `relax:Monoid:has_inverses` |
| `catalyst` | `catalyst:<source>:<target>` | `catalyst:Monoid:Group` |
| `decompose` | `decompose:<target>` | `decompose:Ring` |

Verification runs all constraints independently and reports per-constraint pass/fail. The distance metric sums across constraints, giving the LLM gradient-like feedback for iterative refinement.

### Tested Examples

The examples below solve in 1–3 rounds for *small, well-known algebraic theories* where the LLM can pattern-match from training data (e.g., "the opposite of a Monoid is a comonoid"). These are presentation-level problems: the LLM must produce a theory JSON whose generators and axioms structurally match the target after applying the forward operator. For problems requiring genuine mathematical discovery (non-trivial Morita equivalences, novel categorical localizations, deep tensor factorizations), expect significantly more rounds, frequent `Timeout` feedback from the bounded rewriter, or outright failure. The bounded verification means correct candidates with complex axiom interactions may receive false-negative feedback if the rewriter exceeds its depth limit.

```bash
export $(cat .env | xargs)

# ── Inverse: find X such that op(X) ≅ target ──────────────
catlab-solve Monoid opposite        # round 1 ✅
catlab-solve Group opposite         # round 1 ✅
catlab-solve AbelianGroup opposite  # round 1 ✅
catlab-solve Category opposite      # round 1 ✅
catlab-solve Ring opposite          # round 2 ✅
catlab-solve Monoid mirror          # round 2 ✅

# ── Fixed-point: find X such that op(X) ≅ X ───────────────
catlab-solve --problem fixed-point --target Monoid --op opposite        # round 1 ✅
catlab-solve --problem fixed-point --target AbelianGroup --op opposite  # round 1 ✅

# ── Extension / Pushout / Pullback / Interpolation ─────────
catlab-solve --problem extension --base Monoid --property has_inverses  # round 1 ✅
catlab-solve --problem pushout-complement --base Monoid --target Group  # round 1 ✅
catlab-solve --problem pullback-complement --base Monoid --target Group # round 1 ✅
catlab-solve --problem interpolation --base Monoid --target Group       # round 1 ✅

# ── Simplification / Model / Synthesis ─────────────────────
catlab-solve --problem simplify --target Monoid                         # round 2 ✅
catlab-solve --problem model-finding --target Monoid                    # round 1 ✅
catlab-solve --problem synthesis --base Group --source M --target M     # round 1 ✅

# ── HoTT / ∞-Topos ────────────────────────────────────────
# Full command line (from ts/ directory):
#   export $(cat .env | xargs) && node dist/index.js --problem model-finding \
#     --target "HoTT" --rounds 3 --lean /path/to/catlab --timeout 60000
catlab-solve --problem model-finding --target HoTT                          # round 1 ✅
catlab-solve --problem model-finding --target InfinityTopos                  # round 1 ✅
catlab-solve --problem model-finding --target CohesiveHoTT                  # round 2 ✅
catlab-solve --problem model-finding --target CubicalTypeTheory              # round 2 ✅
catlab-solve HoTT identity                                                   # round 2 ✅
catlab-solve HoTT opposite                                                   # round 3 ✅

# ── Quotient / Relaxation / Sub-object / Decomposition ─────
catlab-solve --problem quotient --base Group --property commutative     # round 1 ✅
catlab-solve --problem relax --target Monoid --property has_inverses    # round 1 ✅
catlab-solve --problem subobject --target Group --property has_identity # round 1 ✅
catlab-solve --problem decompose --target Monoid                        # round 1 ✅

# ── Catalyst: find C such that source⊗C → target⊗C ────────
catlab-solve --problem catalyst --source Monoid --target Monoid         # round 1 ✅
# Note: cross-theory catalysts (e.g. Monoid→Group) are hard — expect 5+ rounds

# ── Multi-objective: find X satisfying multiple inverse constraints ──
catlab-solve --problem multi \
  --objectives "Monoid:opposite,Monoid:identity"                        # round 2 ✅

# ── Factorization: find (X,Y) such that X⊗Y ≅ target ────
catlab-solve --problem factorization --target Monoid                    # round 1 ✅

# ── Optimization: minimize cost subject to constraint ─────
catlab-solve --problem optimization --target Monoid --op opposite \
  --property "minimize generators"                                      # round 1 ✅

# ── Composition: find X satisfying multiple constraints ────
catlab-solve --problem compose \
  --constraints "inverse:Monoid:opposite+fixed-point:Monoid:opposite"   # round 2 ✅
catlab-solve --problem compose \
  --constraints "extension:Monoid:has_inverses+quotient:Group:commutative"

# ── Options ────────────────────────────────────────────────
catlab-solve Monoid opposite --rounds 5 --style "keep it simple"
catlab-solve list  # list all 33 available theories
```

Output goes to stderr (progress logs) and stdout (final JSON result).

### Final Boss Tests (HoTT / Higher-Categorical)

These test the full three-tier verification pipeline including the Hyperion e-graph backend for HIT (Higher Inductive Type) theories where bounded KnuthBendix rewriting times out.

```bash
# Boss 1: The Topological Inverse — find X such that Σ(X) ≅ S¹
# Answer: X = S⁰. Hyperion e-graph verifies the HIT structural equivalence.
catlab-solve --problem inverse --target S1 --op homotopy_suspension          # round 1 ✅

# Boss 2: The Logic Quotient — quotient HoTT to satisfy isProp
# The LLM must realize "quotienting into a proposition" means propositional truncation.
catlab-solve --problem quotient --base HoTT --property isProp                # round 1 ✅

# Boss 3: Univalence Catalyst — synthesize a morphism Equiv(A,B) → Path(U₀,A,B)
# Tests understanding of universe levels and the univalence axiom (ua).
catlab-solve --problem synthesis --base Univalence \
  --source 'Equiv A B' --target 'path (univ 0) A B'                         # round 1 ✅

# Boss 4: E-Graph Coherence Stress Test — fixed-point of S¹ under homotopy coproduct
# A stress test: S¹ ⊔ₕ S¹ (figure-eight) ≠ S¹. Tests graceful failure/creative solutions.
catlab-solve --problem fixed-point --target S1 --op homotopy_coproduct       # round 1 ✅
```

### Secret Boss Tests (Advanced HoTT)

These test deeper mathematical reasoning: duality, higher-dimensional paths, contractibility, and the Eckmann-Hilton argument.

```bash
# Boss 5: The Homotopy Pullback (Dual Trap) — model the fiber product Σ(a:A).Σ(b:B).path(C,f(a),g(b))
# Tests that the LLM does NOT reach for HITs when limits (Σ + path types) suffice.
catlab-solve --problem model-finding --target HomotopyPullback                   # round 1 ✅

# Boss 6: Set Truncation — quotient a type to satisfy isSet (0-truncation)
# The LLM must output a 2-dimensional path constructor: squash on paths, not points.
catlab-solve --problem quotient --base TypeA --property isSet                    # round 3 ✅

# Boss 7: Based Path Space Contractibility — simplify Σ(x:A).path(A,a,x) to Unit
# The LLM must recognize the "based path space is contractible" theorem.
catlab-solve --problem simplify --target BasedPathSpace                          # round 1 ✅

# Boss 8: Eckmann-Hilton — extend Ω²(X,x) with commutative composition
# The LLM sets up 2-loops; the CAS verifies the interchange law.
catlab-solve --problem extension --base LoopSpaceSquared \
  --property "commutative composition"                                           # round 2 ✅
```

### Ascension Boss Tests (Topology & Dependent Types)

These test cross-domain reasoning (algebra ↔ topology), 2-dimensional HIT geometry, universal properties of mapping spaces, and dependent-type manipulation.

```bash
# Boss 9: The Torus T² — synthesize a 2-dimensional HIT with surface constructor
# The LLM must produce base, loop1, loop2, and a 2-cell surf : loop1·loop2 = loop2·loop1.
catlab-solve --problem model-finding --target Torus \
  --target-file theories/torus.json                                              # round 1 ✅

# Boss 10: The Fundamental Group — find X such that Ω(X) ≅ ℤ
# The space whose loop space is the integers is the circle S¹. Classic π₁(S¹) ≅ ℤ.
catlab-solve --problem inverse --target Integers \
  --target-file theories/integers.json --op loop_space                           # round 1 ✅

# Boss 11: Universal Property of S¹ — simplify (S¹ → X) to the free loop space
# The LLM should reduce Map(S¹, X) to Σ(x:X).path(X,x,x).
catlab-solve --problem simplify --target FunctionSpaceS1 \
  --target-file theories/function-space-s1.json                                  # round 1 ✅

# Boss 12: Function Extensionality from Univalence — extend Univalence with FunExt
# The LLM must correctly encode happly with dependent types (Π, path, app, bvar).
catlab-solve --problem extension --base Univalence --property funext             # round 1 ✅
```

### Transcendence Boss Tests (Fibrations, Coherence & Paradox)

These test synthetic fibrations, higher-dimensional coherence, delooping, and universe consistency boundaries.

```bash
# Boss 13: The Hopf Fibration — synthesize S² → U₀ with fiber S¹
# The LLM must compose HITs (S², S¹), universes, and univalence into a typed fibration map.
catlab-solve --problem model-finding --target HopfFibration \
  --target-file theories/hopf-fibration.json                                     # round 1 ✅

# Boss 14: Mac Lane Pentagon — extend a monoidal type with the pentagon coherence axiom
# The LLM must wire up 5 associator applications into the exact commuting 3-cell boundary.
catlab-solve --problem extension --base MonoidalWithAssociator \
  --base-file theories/monoidal-with-associator.json \
  --property "Mac Lane Pentagon Identity"                                        # round 1 ✅

# Boss 15: Classifying Space BG — model a groupoid HIT with loop constructors per group element
# The LLM must embed strict group structure into the path-algebra of a HIT.
catlab-solve --problem model-finding --target ClassifyingSpaceBG \
  --target-file theories/classifying-space.json                                  # round 1 ✅

# Boss 16: Girard Paradox — model "a type containing all types, including itself"
# The LLM produces U : U. The universe consistency checker now rejects this
# with "Universe inconsistency: U is isomorphic to univ 0 but contains a self-referential code."
catlab-solve --problem model-finding --target TypeOfAllTypes \
  --target-file theories/type-of-all-types.json                                  # round 1 ✅ → ❌ (rejected by validator)
```

> **Note on Boss 16:** The universe consistency checker (`Catlab/Core/Validate.lean`) now catches Girard's paradox. When the LLM produces `U : U` (a type isomorphic to `univ 0` that contains a code for itself), the validator detects the self-referential universe membership and rejects it. This runs as part of `evaluate_model` — no `--deep` flag needed.

### Universe Consistency Checking

The validator (`Catlab/Core/Validate.lean`) enforces three soundness checks for HoTT theories (MLTT, Cubical, Cohesive):

1. **Universe stratification** — `univ n` lives at level `n+1`. If an object `U ≅ univ n` contains a self-referential code (`self : 1 → U` with `decode(self) = U`), this requires `level(U) > level(U)`, which is a contradiction (Girard's paradox).

2. **Strict positivity for HITs** — A HIT constructor must not reference the type being defined in a negative (left-of-arrow) position. For example, `bad : (Bad → Nat) → Bad` allows encoding a Y-combinator and deriving `⊥`.

3. **Predicativity for Π-types** — `Π(x : univ n). B` must live at level `≥ n+1`, not below. Violations allow impredicative encodings of large types in small universes.

These checks are integrated into `evaluate_model` and run automatically on all MLTT/Cubical/Cohesive candidates before structural matching.

### User-Defined Theories

You can define custom theories from JSON files without modifying the Lean source:

```bash
# Register a theory from a file and use it as a target
catlab-solve --problem model-finding --target MyTheory --target-file my_theory.json

# Also available: --base-file and --source-file
catlab-solve --problem extension --base MyBase --base-file base.json --property "has_inverses"
```

The Lean REPL supports a `define_theory` command that registers theories at runtime, making them available to all subsequent commands in the same session.

---

## Structure

```
Core/
  Expr.lean           — categorical AST (Expr, Name, GeneratorId)
  Doctrine.lean       — doctrine hierarchy (Category → Topos → ...)
  Theory.lean         — Theory, GeneratorMap, first-class functors
  Equality.lean       — TheoryMorphism with id, comp, inclusion; bijective alpha-equivalence; permutation-based isomorphism checking
  Coherence.lean      — naturality checking, monoidal coherence, isomorphism axioms
  Primitives.lean     — initialTheory (⊥), terminalTheory (⊤)
  Validate.lean       — well-formedness checking, categorical typechecker
  InverseProblem.lean — VerificationResult, computeStructuralDiff, solveInverse
  KnuthBendix.lean    — Knuth-Bendix completion, unification for axiom verification
  PrettyPrint.lean    — pretty-printing for theories and expressions
  Pipeline.lean       — operator pipeline execution

Operators/            — 70 categorical construction operators (incl. Truncate, Pullback, TheoryFamily)
Library/              — 33 registered theory instances (+ InfinityCategory, InfinityTwoCategory)
Repl/                 — REPL server (Protocol.lean, Server.lean)
Tests/                — test suite (Categories A–D, Validate, Fuzz, Properties, Negative,
                        Functorial, Mutation, Limits, Coherence, Higher, Roundtrip, TheoryFamily)

studio/               — CatLab Studio web UI
ts/                   — TypeScript orchestrator (LLM ↔ CAS solver)
```

---

## CatLab Studio

`studio/` contains a web UI for interacting with CatLab via an LLM-driven chat agent backed by the CAS. It provides real-time streaming of solver events via SSE, structured theory visualization, and a periodic table layout of all library theories grouped by domain.
