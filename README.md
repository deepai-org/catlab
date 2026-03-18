# CatLab

A **computer algebra system for categorical theories**, implemented in Lean 4.

Where a classical CAS operates on polynomials and numbers, CatLab operates on *theories* — categorical presentations of mathematical structures. Every operator is deterministic and composable. Every result is a first-class `Theory` value that can be inspected, further transformed, or verified.

---

## The Algebra of Theories

CatLab is organized around a four-tier architecture:

**Tier 1 — Primitives & Symmetries**
The foundation: `Theory`, `TheoryMorphism`, `InitialTheory` (⊥), `TerminalTheory` (⊤), `Opposite`, `Mirror`.

**Tier 2 — Combinators (The Colimit Engine)**
The algebraic operations on theories:
- `pushout f g` — amalgamated sum T₁ ⊔_{T₀} T₂ (the fundamental combinator)
- `tensorTheories` — Freyd/Kronecker product for commuting structures
- `theoryCoproduct` — disjoint union, derived as `pushout` over ⊥
- `quotientCategory` — derived as `pushout` along an inclusion

**Tier 3 — Categorical Constructors**
Derived semantics: `FunctorCategory`, `Model`, `Limits`/`Colimits`, `Comma`, `Slice`, `Grothendieck`, `Decategorify`.

**Tier 4 — Advanced Applications**
Specialized constructions: `Dialectica`, `TriposToTopos`, `Realizability`, `MacNeille`, `Skolem`, and 50+ others.

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

---

## Inverse Problems & The LLM Loop

CatLab includes a unified framework for **inverse problems**: finding an unknown theory `X` such that some forward operator applied to `X` produces a target theory `T`.

```
find X such that forwardOperator(X) ≅ Target
```

| Problem | Unknown X | Forward operator | Target |
|---|---|---|---|
| Categorification | higher theory C | `decategorify` | Jones polynomial theory |
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
  axiomViolations   : List AxiomViolation     -- axioms that don't hold, with partial reductions
```

Three traps addressed explicitly:

- **Verification is not O(N).** Checking theory isomorphism is Graph Isomorphism; checking if an axiom holds is the Word Problem (undecidable). `VerificationStatus.Timeout depth` reports "I tried N rewriting steps and couldn't prove this" rather than falsely reporting failure.

- **Comp-reversing operators.** Operators like `opposite` and `mirror` reverse the direction of composition. Naively comparing `op(candidate)` against `target` puts axioms in the wrong orientation for rewriting, causing infinite expansion. CatLab detects comp-reversing operators and uses a **contravariant verification strategy**: instead of diffing `op(X)` against `T`, it diffs `X` against `op(T)`, keeping composition direction aligned.

- **The alias problem.** If the target requires an object named `State` and the LLM proposes `System`, a name-based diff wastes an API call on a trivial rename. CatLab diffs by **structural signatures**: position-normalized Expr shapes invariant under generator renaming. "Missing morphism `§0 → §1 ⊗ §0`" rather than "Missing morphism `η`."

### The Khovanov Homology Example

```lean
-- CAS recognizes categorification is an inverse problem
-- LLM proposes three candidate 2D categorical theories
-- CAS verifies each by decategorifying back to 1D

evaluateAll (target := TheoryOfJonesPolynomial)
            (forward := fun c => some (decategorify c .isoClasses))
            (candidates := [proposal1, proposal2, proposal3])

-- Proposal 1: failed to compile (missing counit)
-- Proposal 2: compiled, wrong polynomial (axiom violation)
-- Proposal 3: verified → Khovanov Homology
```

---

## Library

34 library theories covering algebra, topology, logic, and higher category theory:

**Algebra:** Monoid, Group, AbelianGroup, Ring, CommutativeRing, Semiring, Module, HopfAlgebra, LieAlgebra, DifferentialGradedAlgebra

**Order/Logic:** Poset, Lattice, BooleanAlgebra, HeytingAlgebra, LinearLogic, GeometricLogic

**Category Theory:** Category, SymmetricMonoidalCategory, EnrichedCategory, AbelianCategory, TriangulatedCategory, ModelCategory, Derivator, Locale

**Higher Structures:** ElementaryTopos, InfinityTopos, HoTT, CohesiveHoTT, CubicalTypeTheory, InfinityTwoCategory, Multicategory, SymmetricOperad, CategoriesWithAttributes

---

## Test Matrix

CatLab has an exhaustive test suite organized by operator category:

- **Category A** — pure `Theory → Theory` operators × all 34 library theories
- **Category B** — binary operators × all 34 library theories (same-theory and cross-theory pairs)
- **Category C** — operators with complex input types (monads, functors, localizations)
- **Category D** — Tier 2 combinators × all 34×34 = 1,156 theory pairs; algebraic law verification (self-pushout collapses to T, pushout over ⊥ = coproduct)
- **InverseProblem** — mock LLM loop with hand-crafted candidates; structural diff correctness; `solveInverse` + `decategorify` integration across all 34 theories

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

### Problem Types

| Problem | Command | What it solves |
|---------|---------|----------------|
| **Inverse** | `catlab-solve Monoid opposite` | find X s.t. op(X) ≅ target |
| **Fixed-point** | `catlab-solve --problem fixed-point --target Monoid --op opposite` | find X s.t. op(X) ≅ X |
| **Pushout complement** | `catlab-solve --problem pushout-complement --base Monoid --target Ring` | find X s.t. pushout(base, X) ≅ target |
| **Extension** | `catlab-solve --problem extension --base Monoid --property has_inverses` | find X extending base with property P |
| **Multi-objective** | `catlab-solve --problem multi --objectives "Monoid:opposite,Monoid:mirror"` | find X satisfying multiple constraints |
| **Factorization** | `catlab-solve --problem factorization --target Ring` | find (X,Y) s.t. X⊗Y ≅ target |
| **Interpolation** | `catlab-solve --problem interpolation --base Monoid --target Ring` | find X with base ↪ X → target |
| **Optimization** | `catlab-solve --problem optimization --target Ring --op opposite --property cost` | minimize cost subject to op(X)≅target |

### Examples

```bash
export $(cat .env | xargs)

# Easy: find X such that opposite(X) ≅ Monoid → solves in ~6s
catlab-solve Monoid opposite

# Fixed-point: find X such that opposite(X) ≅ X → solves in ~4s
catlab-solve --problem fixed-point --target Monoid --op opposite

# With options
catlab-solve Monoid opposite --rounds 5 --style "keep it simple"

# List available theories
catlab-solve list
```

Output goes to stderr (progress logs) and stdout (final JSON result).

---

## Structure

```
Core/
  Expr.lean           — categorical AST (Expr, Name, GeneratorId)
  Doctrine.lean       — doctrine hierarchy (Category → Topos → ...)
  Theory.lean         — Theory, GeneratorMap, first-class functors
  Equality.lean       — TheoryMorphism with id, comp, inclusion
  Primitives.lean     — initialTheory (⊥), terminalTheory (⊤)
  Validate.lean       — well-formedness checking, categorical typechecker
  InverseProblem.lean — VerificationResult, computeStructuralDiff, solveInverse
  Pipeline.lean       — operator pipeline execution

Operators/            — 60+ categorical construction operators
Library/              — 34 named theory instances
Tests/                — test suite (Categories A–D, InverseProblem)
```
