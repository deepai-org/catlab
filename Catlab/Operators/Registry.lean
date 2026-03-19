/-
  CatLab -- Operator Registry

  Single source of truth for all operator metadata.
  The frontend fetches this via the `list_operators` REPL command
  so that theories and operators are never hardcoded in multiple places.
-/

import Lean

namespace CatLab

open Lean (Json JsonNumber)

-- ============================================================
-- Parameter kinds: what extra data an operator needs beyond a Theory
-- ============================================================

inductive ParamKind where
  | theory          -- a second Theory
  | expr            -- an Expr (e.g. dualizer, slice object)
  | monadData       -- MonadData
  | topology        -- GrothendieckTopology
  | pca             -- PCA (partial combinatory algebra)
  | congruence      -- Congruence relation
  | generatorIds    -- List GeneratorId (morphisms to localize, etc.)
  | theoryFunctor   -- TheoryFunctor
  | predicate       -- GeneratorId → Bool (for subcategory)
  | ultrafilter     -- UltrafilterSpec
  | fibration       -- FibrationData
  | enrichment      -- LaxMonoidalFunctor + EnrichedCategory
  | oreData         -- OreData (for fractions)
  | weakEquiv       -- WeakEquivalences
  | homologyTheory  -- HomologyTheory
  deriving Repr, BEq

def ParamKind.toString : ParamKind → String
  | .theory         => "theory"
  | .expr           => "expr"
  | .monadData      => "monad_data"
  | .topology       => "topology"
  | .pca            => "pca"
  | .congruence     => "congruence"
  | .generatorIds   => "generator_ids"
  | .theoryFunctor  => "theory_functor"
  | .predicate      => "predicate"
  | .ultrafilter    => "ultrafilter"
  | .fibration      => "fibration"
  | .enrichment     => "enrichment"
  | .oreData        => "ore_data"
  | .weakEquiv      => "weak_equivalences"
  | .homologyTheory => "homology_theory"

instance : ToString ParamKind := ⟨ParamKind.toString⟩

-- ============================================================
-- Parameter spec: describes one required input
-- ============================================================

structure ParamSpec where
  name : String
  kind : ParamKind
  description : String
  optional : Bool := false
  deriving Repr

-- ============================================================
-- Operator metadata
-- ============================================================

structure OperatorMeta where
  name : String            -- wire name (e.g. "opposite", "sheafify")
  displayName : String     -- UI name (e.g. "Opposite", "Sheafification")
  symbol : String          -- short symbol for periodic table (e.g. "Op", "Shf")
  group : String           -- grouping (e.g. "duality", "completion", "constructor")
  description : String     -- one-line mathematical description
  params : List ParamSpec  -- empty = unary Theory → Theory
  arity : Nat := 1         -- 1 = unary, 2 = binary
  compReversing : Bool := false
  deriving Repr

-- ============================================================
-- Serialization
-- ============================================================

def paramSpecToJson (p : ParamSpec) : Json :=
  Json.mkObj [
    ("name", .str p.name),
    ("kind", .str p.kind.toString),
    ("description", .str p.description),
    ("optional", .bool p.optional)]

def operatorMetaToJson (o : OperatorMeta) : Json :=
  Json.mkObj [
    ("name", .str o.name),
    ("displayName", .str o.displayName),
    ("symbol", .str o.symbol),
    ("group", .str o.group),
    ("description", .str o.description),
    ("params", .arr (o.params.map paramSpecToJson).toArray),
    ("arity", .num { mantissa := Int.ofNat o.arity, exponent := 0 }),
    ("compReversing", .bool o.compReversing)]

-- ============================================================
-- Theory metadata (for list_theories with detail)
-- ============================================================

structure TheoryMeta where
  name : String
  symbol : String
  group : String
  description : String
  deriving Repr

def theoryMetaToJson (t : TheoryMeta) : Json :=
  Json.mkObj [
    ("name", .str t.name),
    ("symbol", .str t.symbol),
    ("group", .str t.group),
    ("description", .str t.description)]

-- ============================================================
-- Group metadata
-- ============================================================

structure GroupMeta where
  key : String
  label : String
  deriving Repr

def groupMetaToJson (g : GroupMeta) : Json :=
  Json.mkObj [("key", .str g.key), ("label", .str g.label)]

def theoryGroups : List GroupMeta := [
  { key := "algebra",     label := "The Builders — Algebra" },
  { key := "logic",       label := "The Deciders — Logic & Order" },
  { key := "category",    label := "The Universes — Categories" },
  { key := "topos",       label := "The Generalized Spaces — Topoi" },
  { key := "higher",      label := "The Ascenders — Higher Structures" },
  { key := "foundations",  label := "Foundations" }
]

def operatorGroups : List GroupMeta := [
  { key := "duality",     label := "The Dualities — Structural Reflection" },
  { key := "glue",        label := "The Glue — Combining" },
  { key := "transformer", label := "The Transformers — Change Dimension" },
  { key := "constructor", label := "The Constructors — Build New From Old" },
  { key := "completion",  label := "The Completions — Add Missing Structure" },
  { key := "enrichment",  label := "The Enrichments — Logic & Structure" }
]

-- ============================================================
-- THE REGISTRY: single source of truth
-- ============================================================

def theoryMetas : List TheoryMeta := [
  -- Algebra
  { name := "Monoid", symbol := "Mon", group := "algebra",
    description := "A system where items can be combined associatively, with a neutral element that does nothing." },
  { name := "Group", symbol := "Grp", group := "algebra",
    description := "A Monoid where every combination can be reversed. Every element has an inverse." },
  { name := "AbelianGroup", symbol := "Ab", group := "algebra",
    description := "A Group where the operation is commutative: a·b = b·a." },
  { name := "Ring", symbol := "Rng", group := "algebra",
    description := "Two operations—addition (a Group) and multiplication (a Monoid)—linked by distributivity." },
  { name := "CommutativeRing", symbol := "CRn", group := "algebra",
    description := "A Ring where multiplication commutes: a·b = b·a." },
  { name := "Semiring", symbol := "SRn", group := "algebra",
    description := "Like a Ring, but addition only needs to be a commutative Monoid—no negation required." },
  { name := "Module", symbol := "Mod", group := "algebra",
    description := "A generalization of vector spaces: scalars from a Ring acting on an abelian Group." },
  { name := "LieAlgebra", symbol := "Lie", group := "algebra",
    description := "An algebra with a bracket operation satisfying the Jacobi identity. Models infinitesimal symmetry." },
  { name := "HopfAlgebra", symbol := "Hpf", group := "algebra",
    description := "Simultaneously an algebra and a coalgebra, with a compatible antipode map." },
  { name := "DGA", symbol := "DGA", group := "algebra",
    description := "A graded algebra with a differential (boundary operator) that squares to zero." },

  -- Logic & Order
  { name := "Poset", symbol := "Pos", group := "logic",
    description := "A set with a partial order: some pairs are comparable, some are not." },
  { name := "Lattice", symbol := "Lat", group := "logic",
    description := "A Poset where every pair has a join (least upper bound) and a meet (greatest lower bound)." },
  { name := "BooleanAlgebra", symbol := "BA", group := "logic",
    description := "A Lattice with complements, modeling classical propositional logic." },
  { name := "HeytingAlgebra", symbol := "HA", group := "logic",
    description := "A Lattice with implication, modeling intuitionistic propositional logic." },
  { name := "GeometricLogic", symbol := "Geo", group := "logic",
    description := "Logic preserved by geometric morphisms—allows infinite disjunctions but only finite conjunctions." },
  { name := "LinearLogic", symbol := "Lin", group := "logic",
    description := "Resource-sensitive logic: hypotheses are consumed when used. Models computation and concurrency." },
  { name := "Locale", symbol := "Loc", group := "logic",
    description := "A pointless topology: a frame of open sets without requiring underlying points." },

  -- Categories
  { name := "Category", symbol := "Cat", group := "category",
    description := "Objects and morphisms with associative composition and identity arrows. The foundation of it all." },
  { name := "SymmetricMonoidal", symbol := "SMC", group := "category",
    description := "A Category with a tensor product that is associative, unital, and symmetric up to isomorphism." },
  { name := "AbelianCategory", symbol := "Abel", group := "category",
    description := "An additive Category where every morphism has a kernel and cokernel. Home of homological algebra." },
  { name := "TriangulatedCategory", symbol := "Tri", group := "category",
    description := "A Category with a shift functor and distinguished triangles. Models derived categories." },
  { name := "ModelCategory", symbol := "Mdl", group := "category",
    description := "A Category with three classes of maps (weak equivalences, fibrations, cofibrations) for homotopy theory." },
  { name := "EnrichedCategory", symbol := "Enr", group := "category",
    description := "A Category where hom-sets are replaced by objects of another monoidal category." },
  { name := "Derivator", symbol := "Der", group := "category",
    description := "An enhancement of triangulated categories that remembers homotopy (co)limits." },

  -- Topoi & Spaces
  { name := "ElementaryTopos", symbol := "ETop", group := "topos",
    description := "A Category with finite limits and power objects. An alternative foundation for mathematics." },
  { name := "InfinityTopos", symbol := "∞Top", group := "topos",
    description := "The ∞-categorical version of a topos. The arena for derived algebraic geometry." },
  { name := "CohesiveHoTT", symbol := "Coh", group := "topos",
    description := "Homotopy Type Theory extended with modalities for cohesion, modeling smooth and continuous spaces." },

  -- Higher Structures
  { name := "Infinity2Category", symbol := "∞2Cat", group := "higher",
    description := "A 2-dimensional ∞-category: morphisms between morphisms at all levels." },
  { name := "Multicategory", symbol := "MCat", group := "higher",
    description := "Like a Category but morphisms can have multiple inputs. Generalizes operads." },
  { name := "SymmetricOperad", symbol := "Opd", group := "higher",
    description := "Encodes operations with multiple inputs and one output, with composition rules and symmetry." },
  { name := "HoTT", symbol := "HoTT", group := "higher",
    description := "Homotopy Type Theory: types are spaces, equalities are paths, higher equalities are homotopies." },
  { name := "CubicalTypeTheory", symbol := "Cub", group := "higher",
    description := "A computational interpretation of HoTT using cubes instead of simplices." },

  -- Foundations
  { name := "CategoriesWithAttributes", symbol := "CwA", group := "foundations",
    description := "A category-theoretic framework for dependent type theories. The semantics of type theory." }
]

def operatorMetas : List OperatorMeta := [
  -- ── Duality (unary, structural reflection) ────────────────────────────────
  { name := "opposite", displayName := "Opposite", symbol := "Op", group := "duality",
    description := "Reverse all arrows. What was domain becomes codomain.",
    params := [], compReversing := true },
  { name := "mirror", displayName := "Dual", symbol := "Dual", group := "duality",
    description := "Categorical duality: vector space duals, Stone duality, Pontryagin duality.",
    params := [], compReversing := true },
  { name := "core", displayName := "Core", symbol := "Core", group := "duality",
    description := "Keep only the isomorphisms—throw away non-invertible morphisms.",
    params := [] },

  -- ── Glue (binary, combining) ──────────────────────────────────────────────
  { name := "pushout", displayName := "Pushout", symbol := "Push", group := "glue",
    description := "Glue two theories along a shared base. The categorical union.",
    params := [{ name := "second_theory", kind := .theory, description := "Second theory to glue" },
               { name := "base", kind := .theory, description := "Shared base theory" }],
    arity := 2 },
  { name := "pullback", displayName := "Pullback", symbol := "Pull", group := "glue",
    description := "The fiber product: intersect two theories over a shared base.",
    params := [{ name := "second_theory", kind := .theory, description := "Second theory" },
               { name := "base", kind := .theory, description := "Shared base theory" }],
    arity := 2 },
  { name := "product", displayName := "Product", symbol := "Prod", group := "glue",
    description := "Pair up two theories: objects are pairs, morphisms act componentwise.",
    params := [{ name := "second_theory", kind := .theory, description := "Second theory", optional := true }],
    arity := 2 },
  { name := "coproduct", displayName := "Coproduct", symbol := "Coprod", group := "glue",
    description := "Disjoint union of two theories: everything stays separate.",
    params := [{ name := "second_theory", kind := .theory, description := "Second theory", optional := true }],
    arity := 2 },
  { name := "collage", displayName := "Collage", symbol := "Coll", group := "glue",
    description := "Place two categories side by side, connected by a profunctor.",
    params := [{ name := "second_theory", kind := .theory, description := "Second category" }],
    arity := 2 },
  { name := "comma", displayName := "Comma", symbol := "Com", group := "glue",
    description := "Objects are arrows between two functors—the universal comma construction.",
    params := [{ name := "second_theory", kind := .theory, description := "Second category" }],
    arity := 2 },
  { name := "span", displayName := "Span", symbol := "Spn", group := "glue",
    description := "Build the category of spans (roofs) over the theory.",
    params := [] },
  { name := "day_convolution", displayName := "DayConvolution", symbol := "Day", group := "glue",
    description := "Lift the monoidal structure of a category to its presheaf category.",
    params := [{ name := "monoidal_structure", kind := .monadData, description := "Monoidal structure to lift" }] },

  -- ── Transformers (change dimension/structure) ─────────────────────────────
  { name := "decategorify_iso", displayName := "Decategorify", symbol := "Decat", group := "transformer",
    description := "Drop one categorical level: identify isomorphic objects.",
    params := [] },
  { name := "grothendieck", displayName := "Grothendieck", symbol := "Groth", group := "transformer",
    description := "Flatten an indexed family of categories into a single fibered category.",
    params := [{ name := "indexed_category", kind := .fibration, description := "Indexed category to flatten" }] },
  { name := "nerve", displayName := "Nerve", symbol := "Nrv", group := "transformer",
    description := "Turn a category into a simplicial set—its combinatorial skeleton.",
    params := [] },
  { name := "stabilize", displayName := "Stabilize", symbol := "Stab", group := "transformer",
    description := "Pass to the stable category: force the suspension functor to be an equivalence.",
    params := [] },
  { name := "derived", displayName := "Derived", symbol := "Der", group := "transformer",
    description := "Localize at quasi-isomorphisms to get the derived category.",
    params := [] },
  { name := "chain_complex", displayName := "Linearize", symbol := "Lnz", group := "transformer",
    description := "Linearize: turn a category into its chain complex category.",
    params := [] },
  { name := "bousfield", displayName := "Bousfield", symbol := "Bous", group := "transformer",
    description := "Localize a model category at a chosen homology theory.",
    params := [{ name := "local_morphisms", kind := .generatorIds, description := "Morphisms to localize at" }] },
  { name := "factorization", displayName := "Factorization", symbol := "Fact", group := "transformer",
    description := "Decompose morphisms into a composition of two special classes.",
    params := [] },
  { name := "drinfeld_center", displayName := "DrinfeldCenter", symbol := "DrnC", group := "transformer",
    description := "The braided monoidal center: objects that commute with everything.",
    params := [] },
  { name := "center", displayName := "Center", symbol := "Cen", group := "transformer",
    description := "Extract the center—elements that commute with all others.",
    params := [] },

  -- ── Constructors (build new from old) ─────────────────────────────────────
  { name := "free", displayName := "Free", symbol := "Free", group := "constructor",
    description := "Freely generate structure from generators. No extra equations.",
    params := [] },
  { name := "kleisli", displayName := "Kleisli", symbol := "Kl", group := "constructor",
    description := "Build the Kleisli category from a monad: morphisms are effectful computations.",
    params := [{ name := "monad", kind := .monadData, description := "The monad (functor + unit + multiplication)" }] },
  { name := "eilenberg_moore", displayName := "EilenbergMoore", symbol := "EM", group := "constructor",
    description := "Build the Eilenberg-Moore category: algebras over a monad.",
    params := [{ name := "monad", kind := .monadData, description := "The monad" }] },
  { name := "monad", displayName := "Monad", symbol := "Mnd", group := "constructor",
    description := "Extract or construct the monad associated to an adjunction.",
    params := [{ name := "adjunction", kind := .theoryFunctor, description := "The adjunction to extract monad from" }] },
  { name := "functor_category", displayName := "FunctorCategory", symbol := "Fun", group := "constructor",
    description := "The category of functors between two categories, with natural transformations.",
    params := [{ name := "target", kind := .theory, description := "Target category", optional := true }],
    arity := 2 },
  { name := "adjunction", displayName := "Adjunction", symbol := "Adj", group := "constructor",
    description := "Find or construct a pair of adjoint functors between theories.",
    params := [{ name := "second_theory", kind := .theory, description := "Second category" }],
    arity := 2 },
  { name := "kan", displayName := "Kan", symbol := "Kan", group := "constructor",
    description := "Compute left or right Kan extensions along a functor.",
    params := [{ name := "along", kind := .theoryFunctor, description := "Functor to extend along" },
               { name := "functor", kind := .theoryFunctor, description := "Functor to extend" }] },
  { name := "yoneda", displayName := "Yoneda", symbol := "Yon", group := "constructor",
    description := "Embed a category into its presheaf category via the Yoneda embedding.",
    params := [] },
  { name := "slice", displayName := "Slice", symbol := "Sl", group := "constructor",
    description := "The slice (over) category: objects are morphisms into a fixed target.",
    params := [{ name := "over", kind := .expr, description := "Object to slice over", optional := true }] },
  { name := "arrow_category", displayName := "Arrow", symbol := "Arr", group := "constructor",
    description := "The arrow category: objects are morphisms, morphisms are commutative squares.",
    params := [] },
  { name := "twisted_arrow", displayName := "TwistedArrow", symbol := "TwA", group := "constructor",
    description := "Like Arrow, but with domain and codomain swapped on one side.",
    params := [] },
  { name := "internal_cat", displayName := "Internal", symbol := "Int", group := "constructor",
    description := "Internalize a structure: define it inside another category.",
    params := [] },
  { name := "family", displayName := "Family", symbol := "Fam", group := "constructor",
    description := "Build the category of set-indexed families of objects.",
    params := [] },
  { name := "matrix", displayName := "Matrix", symbol := "Mat", group := "constructor",
    description := "Build the matrix category: morphisms are matrices of hom-set elements.",
    params := [] },
  { name := "lawvere", displayName := "Lawvere", symbol := "Law", group := "constructor",
    description := "Construct the Lawvere theory—the categorical encoding of an algebraic theory.",
    params := [] },
  { name := "syntactic", displayName := "Syntactic", symbol := "Syn", group := "constructor",
    description := "Build the syntactic category from a logical theory.",
    params := [] },
  { name := "operad_envelope", displayName := "OperadEnvelope", symbol := "OpE", group := "constructor",
    description := "The monoidal envelope of an operad—turning multi-input into tensor.",
    params := [] },
  { name := "freyd", displayName := "Freyd", symbol := "Frd", group := "constructor",
    description := "The Freyd category for modeling effectful computation.",
    params := [] },
  { name := "int", displayName := "TracedCompletion", symbol := "TrC", group := "constructor",
    description := "The Joyal–Street–Verity Int construction: formally adjoin inverses to make a compact closed category.",
    params := [] },
  { name := "chu", displayName := "Chu", symbol := "Chu", group := "constructor",
    description := "The Chu construction: a *-autonomous category from a closed monoidal one.",
    params := [{ name := "dualizer", kind := .expr, description := "The dualizing object" }] },

  -- ── Completions (add missing structure) ───────────────────────────────────
  { name := "ex_completion", displayName := "ExactCompletion", symbol := "ExCp", group := "completion",
    description := "Freely add finite colimits to make the category exact.",
    params := [] },
  { name := "karoubi", displayName := "Karoubi", symbol := "Kar", group := "completion",
    description := "Idempotent completion: formally split all idempotent morphisms.",
    params := [] },
  { name := "sheafify", displayName := "Sheafify", symbol := "Shf", group := "completion",
    description := "Turn presheaves into sheaves by forcing the gluing axiom.",
    params := [{ name := "topology", kind := .topology, description := "Grothendieck topology (covering families)" }] },
  { name := "localize", displayName := "Localize", symbol := "Loc", group := "completion",
    description := "Formally invert a chosen class of morphisms.",
    params := [{ name := "weak_equivalences", kind := .weakEquiv, description := "Morphisms to invert" }] },
  { name := "booleanize", displayName := "DoubleNegation", symbol := "DblN", group := "completion",
    description := "Force the logic to be Boolean via the double negation translation.",
    params := [] },
  { name := "macneille", displayName := "MacNeille", symbol := "MacN", group := "completion",
    description := "The MacNeille completion: embed a poset into a complete lattice.",
    params := [] },
  { name := "ind_completion", displayName := "Ind", symbol := "Ind", group := "completion",
    description := "Ind-completion: adjoin formal filtered colimits.",
    params := [] },
  { name := "pro_completion", displayName := "Pro", symbol := "Pro", group := "completion",
    description := "Pro-completion: adjoin formal cofiltered limits.",
    params := [] },
  { name := "limits", displayName := "Limits", symbol := "Lim", group := "completion",
    description := "Freely adjoin all limits to the category.",
    params := [] },
  { name := "fractions", displayName := "Fractions", symbol := "Frac", group := "completion",
    description := "Calculus of fractions: a structured way to localize a category.",
    params := [{ name := "ore_data", kind := .oreData, description := "Ore condition data" }] },
  { name := "quotient", displayName := "Quotient", symbol := "Quot", group := "completion",
    description := "Form the quotient by a congruence relation on morphisms.",
    params := [{ name := "congruence", kind := .congruence, description := "Congruence relation to quotient by" }] },
  { name := "subcategory", displayName := "Subcategory", symbol := "Sub", group := "completion",
    description := "Restrict to a chosen sub-collection of objects and morphisms.",
    params := [{ name := "predicate", kind := .predicate, description := "Which objects to keep" }] },
  { name := "ultrapower", displayName := "Ultrapower", symbol := "Ultr", group := "completion",
    description := "Build the ultrapower—ultraproduct along a single structure.",
    params := [{ name := "ultrafilter", kind := .ultrafilter, description := "Ultrafilter specification" }] },

  -- ── Enrichment & Logic ────────────────────────────────────────────────────
  { name := "change_of_base", displayName := "ChangeOfBase", symbol := "ChBs", group := "enrichment",
    description := "Re-enrich a category over a different monoidal base.",
    params := [{ name := "functor", kind := .enrichment, description := "Lax monoidal functor to new base" }] },
  { name := "cleavage", displayName := "Cleavage", symbol := "Clvg", group := "enrichment",
    description := "Choose a cleavage for a fibration—pick canonical lifts of morphisms.",
    params := [{ name := "fibration", kind := .fibration, description := "Fibration data" }] },
  { name := "dialectica", displayName := "Dialectica", symbol := "Dial", group := "enrichment",
    description := "Gödel's Dialectica interpretation: transform proofs into witnessing data.",
    params := [{ name := "omega", kind := .expr, description := "Dualizing object ω" }] },
  { name := "realizability", displayName := "Realizability", symbol := "Real", group := "enrichment",
    description := "Build a realizability topos: truth is witnessable computation.",
    params := [{ name := "pca", kind := .pca, description := "Partial combinatory algebra" }] },
  { name := "assembly", displayName := "Assembly", symbol := "Asm", group := "enrichment",
    description := "The category of assemblies—sets with realizability structure.",
    params := [{ name := "pca", kind := .pca, description := "Partial combinatory algebra" }] },
  { name := "per", displayName := "PER", symbol := "PER", group := "enrichment",
    description := "Partial equivalence relations: a model of types as quotients of computable functions.",
    params := [{ name := "pca", kind := .pca, description := "Partial combinatory algebra" }] },
  { name := "tripos_to_topos", displayName := "TriposToTopos", symbol := "T2T", group := "enrichment",
    description := "Turn a tripos (categorical model of logic) into a topos.",
    params := [{ name := "tripos", kind := .fibration, description := "Tripos structure" }] },
  { name := "morita", displayName := "Morita", symbol := "Mor", group := "enrichment",
    description := "Pass to the Morita equivalence class—theories with the same models.",
    params := [] },
  { name := "artin_gluing", displayName := "ArtinGluing", symbol := "AGlu", group := "enrichment",
    description := "Glue two toposes along a geometric morphism—Artin's gluing construction.",
    params := [{ name := "topos", kind := .theory, description := "Topos to glue along" }],
    arity := 2 },
  { name := "isbell", displayName := "Isbell", symbol := "Isb", group := "enrichment",
    description := "Isbell duality: adjunction between presheaves and copresheaves.",
    params := [] },
  { name := "skolem", displayName := "Skolem", symbol := "Sk", group := "enrichment",
    description := "Skolemization: replace existential quantifiers with witness functions.",
    params := [{ name := "existentials", kind := .generatorIds, description := "Existential axioms to skolemize" }] },
  { name := "cwf", displayName := "CwF", symbol := "CwF", group := "enrichment",
    description := "Category with Families—the categorical semantics of dependent type theory.",
    params := [{ name := "cwf_data", kind := .fibration, description := "CwF structure data" }] },
  { name := "ends_coends", displayName := "EndsCoends", symbol := "E/C", group := "enrichment",
    description := "Compute ends and coends—the categorical trace and cotrace.",
    params := [{ name := "profunctor", kind := .theoryFunctor, description := "Profunctor to compute end/coend of" }] }
]

/-- Check whether an operator can be applied with just a Theory (no extra params needed). -/
def OperatorMeta.isUnary (o : OperatorMeta) : Bool :=
  o.params.all (·.optional) || o.params.isEmpty

end CatLab
