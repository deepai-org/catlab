# CatLab Architecture

CatLab is a computer algebra system for categorical theories. Where a classical CAS operates on polynomials and numbers, CatLab operates on **theories** — categorical presentations of mathematical structures (objects, morphisms, axioms). The system is split across two languages with a clean boundary: Lean owns the mathematics, TypeScript owns the LLM orchestration.

---

## The Two Halves

### Lean (19,973 lines) — The CAS

Everything that touches mathematical content lives in Lean. The Lean side is a self-contained, deterministic algebra of theories. It has no awareness of LLMs, HTTP, or orchestration.

### TypeScript (10,678 lines) — The Orchestrator

Everything that touches LLMs, external verification backends (Omega, Hyperion), and the solver feedback loop lives in TypeScript. It has no theory algebra of its own — when it needs a pushout, morphism, or validation, it asks Lean.

### The Boundary: NDJSON over stdio

The two halves communicate through a single pipe. The Lean REPL (`lake exe catlab-repl`) reads newline-delimited JSON commands on stdin and writes responses on stdout. The TypeScript `CatlabClient` spawns this process and manages request/response correlation via request IDs.

```
TypeScript                          Lean
┌──────────────┐    NDJSON/stdio    ┌──────────────┐
│  CatlabClient │ ◄──────────────► │  catlab-repl  │
│  (client.ts)  │                   │  (Server.lean)│
└──────────────┘                   └──────────────┘
```

Commands include: `list_theories`, `summary`, `apply_operator`, `compute_pushout`, `compute_pushout_cocone`, `compute_morphism`, `evaluate_inverse`, `evaluate_extension`, and 14 other `evaluate_*` variants for different problem types.

---

## Lean: The CAS Internals

### Core (11 files, 3,064 lines)

The foundational type system and algorithms.

- **`Expr.lean`** — The AST. A `Name` is an S-expression-like tree (atoms, `inl`/`inr` tags for disjoint unions). An `Expr` is built from atoms, composition, products, tensors, hom-objects, coproducts, identities, and terminal/initial constants.

- **`Theory.lean`** — A `Theory` is a list of `Generator0` (objects/sorts), `Generator1` (morphisms with domain/codomain as `Expr`), and `Axiom` (pairs of `Expr` paths asserted equal), plus a `Doctrine` tag.

- **`Equality.lean`** — `TheoryMorphism`: explicit, inspectable maps between theories. Supports `id`, `comp`, and `inclusion` (matches generators by name). Also contains bijective alpha-equivalence and permutation-based isomorphism checking.

- **`Doctrine.lean`** — The doctrine hierarchy: `Category`, `CartesianCategory`, `MonoidalCategory`, `Topos`, `PresentableInfinityCategory`, `MartinLofTypeTheory`, etc. Each doctrine carries metadata (truncation level, strictification flag).

- **`KnuthBendix.lean`** — Bounded Knuth-Bendix completion. Decides equality of `Expr` terms via normal-form matching with a configurable depth limit. Reports `Timeout` rather than looping — an unavoidable consequence of the bounded Word Problem.

- **`InverseProblem.lean`** — The verification engine. Given a candidate theory and a forward operator, applies the operator and computes a `VerificationResult`: structured diff with missing signatures, unmapped objects, and axiom violations (with partial reductions). This is the primary feedback signal to the LLM.

- **`Validate.lean`** — Well-formedness checking: no duplicate names, all morphism domain/codomain atoms resolve, all axiom path atoms resolve, doctrine constraints satisfied, composition boundaries match.

- **`Coherence.lean`** — Checks naturality squares, monoidal coherence (pentagon, triangle, hexagon), and well-formed axiom schemas.

- **`Primitives.lean`** — The initial theory ⊥ (empty) and terminal theory ⊤ (single object, identity only), plus canonical morphisms from/to them.

### Library (30 files, 2,838 lines)

Pre-built mathematical theory signatures. Each file defines a `Theory` value with the appropriate objects, morphisms, axioms, and doctrine.

**Algebra:** Monoid, Group, AbelianGroup, Ring, CommutativeRing, Semiring, Module, HopfAlgebra, LieAlgebra, DGA

**Order & Logic:** Poset, Lattice, BooleanAlgebra, LinearLogic, GeometricLogic

**Category Theory:** Category, SymmetricMonoidalCategory, EnrichedCategory, AbelianCategory, TriangulatedCategory, ModelCategory, Derivator, Locale

**Higher Structures:** ElementaryTopos, InfinityTopos, HoTT, CohesiveHoTT, CubicalTypeTheory, (∞,n)-Category, Operad, CategoriesWithAttributes

Each theory is registered in the REPL and available by name (e.g., `"Monoid"`, `"Group"`, `"ElementaryTopos"`).

### Operators (68 files, 7,953 lines)

The combinator algebra. Each operator is a function `Theory → Theory` (or `Theory^n → Theory`) implementing a categorical construction. They are organized in tiers:

**Tier 1 — Primitives:** `Opposite` (flip morphisms), `Mirror` (flip axiom paths), `Free` (no additional relations).

**Tier 2 — Colimit Engine:** `Pushout` (the fundamental combinator — amalgamated sum T₁ ⊔_{T₀} T₂ via Union-Find), `Coproduct` (derived as pushout over ⊥), `Quotient` (derived as pushout along an inclusion), `Product`, `Tensor`.

**Tier 3 — Categorical Constructors:** `FunctorCategory`, `Comma`, `Grothendieck`, `Limits`/`Colimits` (with full universal properties), `Slice`, `Arrow`, `Kan`, `Yoneda`, `Nerve`.

**Tier 4 — Advanced:** `TriposToTopos`, `Realizability`, `PER`, `Assembly` (realizability topos pipeline), `Dialectica`, `Chu`, `MacNeille`, `DrinfeldCenter`, `DayConvolution`, `ExactCompletion`, `Stabilize`, `Derived`, `Bousfield`, `EilenbergMoore`, `Kleisli`, `Skolem`, `Truncate`, and ~30 others.

Notable: `Pushout.lean` also defines `PushoutCocone` — returns the apex theory plus the two cocone leg morphisms with correct name mappings (accounting for `inl`/`inr` tagging and Union-Find collapse). The `Registry.lean` file enumerates all 68 operators with their parameter types and applicability metadata.

### REPL (2 files, 1,334 lines)

- **`Protocol.lean`** — JSON serialization for `Theory`, `Expr`, `TheoryMorphism`, `VerificationResult`, and all request/response types.
- **`Server.lean`** — The NDJSON command dispatcher. Reads commands, looks up theories/operators in the registry, executes, and returns JSON responses.

### Tests (17 files, 3,662 lines)

Comprehensive: smoke tests (every operator × every library theory), shape invariants, involution correctness, idempotency, monotonicity, axiom preservation, composition chains, property-based fuzzing (xorshift32 PRNG), mutation testing, negative validation, limits/colimits, coherence checking, higher-categorical metadata, JSON roundtrips, and TheoryMorphism algebraic laws. ~5,314 assertions total.

---

## TypeScript: The Orchestrator Internals

### The Solver Loop (`solver.ts`, 346 lines)

A verifier-agnostic state machine:

```
GENERATING → VERIFYING → (SUCCESS | feedback → GENERATING | EXHAUSTED)
```

The `GenericSolver` takes a `Verifier` and an `LLMClient`, runs up to N rounds (default 5), and returns a `SolverResult` with history. It knows nothing about theory structure — the Verifier defines the answer schema, sends payloads to the CAS, and formats feedback.

### Verifiers (`verifiers.ts`, 1,430 lines)

18 concrete `Verifier` implementations, one per problem type (inverse, pushout-complement, extension, fixed-point, multi-objective, factorization, interpolation, simplification, model-finding, subobject, synthesis, quotient, decomposition, relaxation, catalyst, optimization, pullback-complement, compose). Each verifier:

1. **`preflight()`** — Fetches context from the CAS (target theory summary, base theory, etc.) and returns a `ProblemSpec` with the LLM prompt, answer schema, and hints.
2. **`verify()`** — Sends the LLM's payload to the CAS via the appropriate `evaluate_*` command, returns a `VerificationResult`.
3. **`formatFeedback()`** — Turns the result into LLM-readable text (missing signatures, axiom violations, distance metrics).

### LLM Client (`llm.ts`, 617 lines)

Wrapper around the Anthropic SDK. Uses forced `tool_choice` so the LLM always returns structured JSON (a `TheoryJson` or problem-specific schema). Supports adaptive thinking budgets and cached system prompts.

### CAS Client (`client.ts`, 132 lines)

Spawns `lake exe catlab-repl`, sends NDJSON requests, correlates responses by ID, handles timeouts per-request.

### Elaborators — The Three Verification Tiers

CatLab routes theories to three verification backends based on doctrine:

**1. Lean/Mathlib (`lean-elaborator.ts`, 856 lines + `operator-elaborators.ts`, 848 lines)**

Translates `TheoryJson` → `.lean` source with Mathlib imports (`CategoryTheory.Category.Basic`, etc.), runs the Lean compiler, and maps diagnostics back to AST node IDs. Used for doctrines with deep Mathlib coverage (Category, Abelian, Topos). The `operator-elaborators.ts` file handles operator-specific code generation (e.g., realizability theories get PCA typeclasses, Setoid quotients, and assembly structures).

**2. Omega (`external-elaborators.ts` → `theoryToOmega()`)**

For equational/algebraic doctrines (LawvereTheory, AlgebraicTheory, CartesianClosed, FiniteProduct, MonoidalCategory). Translates `TheoryJson` to `.omega` S-expression source with AC attributes, auto tactics, and lemma registration. Invoked via `omega check --json --stdin`. ~1ms verification.

**3. Hyperion (`external-elaborators.ts` → `theoryToHyperion()`)**

For higher-categorical doctrines (MartinLofTypeTheory, ∞-categories, cubical, cohesive HoTT). Translates to `.hyp` source with:
- `[PathType]` auto-injection (refl, concat, inv, ap rules)
- `[JType]` for MLTT, `[PartialElement]` for cubical
- `[ModalOperator]` for cohesive modalities (ʃ, ♭, ♯)
- Equality saturation via e-graphs (discovers theorems, not just verifies)
- `[extract-proof]` to recover path witnesses (critical for HoTT — multiple distinct paths between same endpoints)
- `[Functor :verify]`, `[NatTrans :verify]`, `[Adjunction :verify]`

~5ms verification. The key capability: e-graph saturation can discover non-obvious equalities (e.g., Eckmann-Hilton from interchange + unit laws) that directed search cannot find.

### Geometric Morphism Elaboration (`external-elaborators.ts`)

`morphismToHyperion()` and `adjunctionToHyperion()` translate `TheoryMorphismJson` (received from the Lean REPL) into Hyperion functor/adjunction syntax. This is the tier-translation bridge for ∞-topos verification:

- Lean computes the theory morphism (pushout cocone leg, inclusion, identity)
- TypeScript translates it into Hyperion's `[Functor]` / `[Adjunction]` blocks
- For PathType doctrines, functors get `:preserve-paths true`
- Hyperion verifies functoriality, path preservation, and adjunction triangle identities

### Deep Verifier (`deep-verifier.ts`, 167 lines)

Two-tier wrapper: runs any verifier's fast structural check first, then optionally escalates to Lean/Mathlib type-checking for deep verification.

### Chat Agent (`chat.ts`, 746 lines)

LLM-driven conversational interface to the CAS. Interprets natural language and invokes tools (list theories, apply operators, solve problems).

### Studio Server (`server.ts`, 259 lines)

HTTP API + web UI. Proxies CAS calls for the browser-based periodic table / theory explorer.

### CLI (`index.ts`, 390 lines)

`catlab-solve` command supporting all 18 problem types with argparse-style flags.

---

## Data Flow: End-to-End

A typical inverse problem (`catlab-solve Monoid opposite`):

```
1. CLI parses args → creates InverseVerifier("Monoid", "opposite")

2. Verifier.preflight()
   → CatlabClient sends {command: "summary", theory: "Monoid"}
   → Lean returns theory structure
   → Verifier builds ProblemSpec with prompt + answer schema

3. Solver sends ProblemSpec to LLM
   → LLM returns TheoryJson candidate via tool_use

4. Verifier.verify()
   → CatlabClient sends {command: "evaluate_inverse", target: "Monoid",
      forward_op: "opposite", candidate: <TheoryJson>}
   → Lean applies opposite(candidate), diffs against Monoid
   → Returns VerificationResult (missing sigs, axiom violations, distance)

5. If verified: return success
   If not: Verifier.formatFeedback() → LLM reads diff → step 3
```

For deep verification, the elaborator pipeline adds a second check:

```
TheoryJson → routeToExternal() → "omega" | "hyperion" | null
  → theoryToOmega() or theoryToHyperion() → CLI invocation → parse results
  → OR theoryToLean() → lean compiler → parse diagnostics
```

---

## Key Design Principles

1. **Lean owns all theory algebra.** No pushouts, morphisms, truncations, or validation in TypeScript. When TypeScript removed ~522 lines of redundant theory algebra, zero functionality was lost — it was all already in Lean.

2. **TypeScript owns all tier translation.** Converting a `TheoryJson` to `.lean` / `.omega` / `.hyp` source is a syntactic translation, not theory algebra. This stays in TypeScript because it's the orchestrator's job to choose and invoke the right backend.

3. **The verifier is the API.** The solver loop is completely verifier-agnostic. Adding a new problem type means implementing one `Verifier` interface (preflight, verify, formatFeedback) — no changes to the solver, LLM client, or CAS.

4. **Verification is always cheaper than discovery.** The CAS verifies deterministically; the LLM proposes. The structured diff (`VerificationResult`) is designed to be the primary input to the LLM's next attempt — position-normalized signatures, partial reductions, distance metrics.

5. **Three backends, one wire format.** Omega, Lean/Mathlib, and Hyperion all consume the same `TheoryJson`. The solver loop and LLM don't know which backend ran. Routing is by doctrine, fully automatic.
