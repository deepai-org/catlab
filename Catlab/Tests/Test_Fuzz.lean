/-
  CatLab — Generative Property-Based Testing (Fuzzer)

  Synthesizes random, syntactically valid theories and feeds them through
  random operator chains to stress-test the combinator algebra.
-/

import Catlab.Tests.TestCore
import Catlab.Core.Validate
import Catlab.Operators.Opposite
import Catlab.Operators.Mirror
import Catlab.Operators.Decategorify
import Catlab.Operators.Karoubi
import Catlab.Operators.Arrow
import Catlab.Operators.Span
import Catlab.Operators.Family
import Catlab.Operators.Nerve
import Catlab.Operators.ExactCompletion
import Catlab.Operators.Morita
import Catlab.Operators.Internal
import Catlab.Operators.Center
import Catlab.Operators.Syntactic
import Catlab.Operators.Stabilize
import Catlab.Operators.Isbell
import Catlab.Operators.Product
import Catlab.Operators.Coproduct
import Catlab.Operators.DayConvolution
import Catlab.Operators.Comma

namespace CatLab.Tests.Fuzz

open CatLab CatLab.Arrow

-- ============================================================
-- Deterministic PRNG (xorshift32)
-- ============================================================

structure RNG where
  state : UInt32

def RNG.next (r : RNG) : RNG × Nat :=
  let s := r.state
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 17)
  let s := s ^^^ (s <<< 5)
  ({ state := s }, s.toNat)

def RNG.natMod (r : RNG) (n : Nat) : RNG × Nat :=
  if n == 0 then (r, 0)
  else let (r', v) := r.next; (r', v % n)

def RNG.natRange (r : RNG) (lo hi : Nat) : RNG × Nat :=
  let (r', v) := r.natMod (hi - lo + 1)
  (r', lo + v)

-- ============================================================
-- Random theory generator (small theories: 1-3 objects, 0-4 morphisms)
-- ============================================================

def randomTheory (seed : RNG) (name : String) : RNG × Theory := Id.run do
  let mut r := seed
  let (r', numObj) := r.natRange 1 3
  r := r'
  let objects : List Generator0 := (List.range numObj).map fun i =>
    { id := gid s!"O{i}", description := s!"Object {i}" }

  let (r', numMor) := r.natRange 0 4
  r := r'
  let mut morphisms : List Generator1 := []
  for i in List.range numMor do
    let (r', di) := r.natMod numObj; r := r'
    let (r', ci) := r.natMod numObj; r := r'
    let dom := Expr.atom (gid s!"O{di}")
    let cod := Expr.atom (gid s!"O{ci}")
    let m : Generator1 := { id := gid s!"f{i}" (k := .morphism), domain := dom, codomain := cod }
    morphisms := morphisms ++ [m]

  -- 0-2 axioms between parallel morphisms
  let (r', numAx) := r.natRange 0 2; r := r'
  let mut axioms : List Generator2 := []
  for i in List.range numAx do
    if morphisms.length < 2 then break
    let (r', idx1) := r.natMod morphisms.length; r := r'
    let m1 := morphisms[idx1]!
    let parallel := morphisms.filter fun m =>
      m.domain.toName == m1.domain.toName && m.codomain.toName == m1.codomain.toName
    if parallel.length >= 2 then
      let (r', idx2) := r.natMod parallel.length; r := r'
      let m2 := parallel[idx2]!
      let ax : Generator2 := { id := gid s!"ax{i}" (k := .twoCell), leftPath := .atom m1.id, rightPath := .atom m2.id }
      axioms := axioms ++ [ax]

  (r, { name := name, doctrine := { doctrine := .Category }
        objects := objects, morphisms := morphisms, axioms := axioms })

-- ============================================================
-- Operator pools
-- ============================================================

-- All 15 unary operators
private def allUnaryOps : List (String × (Theory → Theory)) :=
  [ ("opposite",   opposite),   ("mirror",     mirror)
  , ("decat",      fun t => decategorify t .isoClasses)
  , ("karoubi",    karoubiEnvelope), ("arrow", arrowCategory)
  , ("span",       spanCategory),    ("family", familyCategory)
  , ("nerve",      nerve),           ("exact",  exCompletion)
  , ("morita",     moritaEnvelope),  ("internal", internalCategoryCategory)
  , ("center",     center),          ("syntactic", syntacticCategory)
  , ("stabilize",  stabilize),       ("isbell", isbellAdjunction)
  ]

-- Lightweight ops safe for chaining (don't blow up theory size)
private def lightOps : List (String × (Theory → Theory)) :=
  [ ("opposite",   opposite),   ("mirror",     mirror)
  , ("decat",      fun t => decategorify t .isoClasses)
  , ("karoubi",    karoubiEnvelope), ("arrow", arrowCategory)
  , ("family",     familyCategory),  ("nerve", nerve)
  , ("center",     center)
  ]

private def binaryOps : List (String × (Theory → Theory → Theory)) :=
  [ ("product",    productCategory)
  , ("coproduct",  coproductCategory)
  , ("tensor",     tensorTheories)
  ]

-- ============================================================
-- 1. Every operator × 20 random theories
-- ============================================================

#eval do
  IO.println "\n=== fuzz: all operators × random theories ==="
  let mut rng : RNG := { state := 42 }
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for i in List.range 20 do
    let (r, t) := randomTheory rng s!"fuzz_{i}"
    rng := r
    if !(CatLab.validate t).isEmpty then continue
    for (opName, op) in allUnaryOps do
      total := total + 1
      let errors := CatLab.validate (op t)
      if !errors.isEmpty then
        failures := failures + 1
        if failures <= 5 then
          IO.println s!"[FAIL] {opName}(fuzz_{i}): {errors.length} errors"
          for e in errors.take 2 do IO.println s!"  - {e}"
  IO.println s!"Fuzzed {total} single-op: {total - failures} pass, {failures} fail"
  if failures > 0 then
    throw (IO.userError s!"{failures} single-op fuzz failures")

-- ============================================================
-- 2. Operator chains (depth 2-3) × 20 random theories (light ops only)
-- ============================================================

#eval do
  IO.println "\n=== fuzz: operator chains depth 2-3 ==="
  let mut rng : RNG := { state := 137 }
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for i in List.range 20 do
    let (r, t) := randomTheory rng s!"chain_{i}"
    rng := r
    if !(CatLab.validate t).isEmpty then continue
    let (r, depth) := r.natRange 2 3; rng := r
    let mut current := t
    let mut chainNames : List String := []
    for _ in List.range depth do
      let (r, opIdx) := rng.natMod lightOps.length; rng := r
      let (opName, op) := lightOps[opIdx]!
      chainNames := chainNames ++ [opName]
      current := op current
    total := total + 1
    let errors := CatLab.validate current
    if !errors.isEmpty then
      failures := failures + 1
      if failures <= 5 then
        IO.println s!"[FAIL] ({String.intercalate " ∘ " chainNames.reverse})(chain_{i}): {errors.length} errors"
        for e in errors.take 2 do IO.println s!"  - {e}"
  IO.println s!"Fuzzed {total} chains: {total - failures} pass, {failures} fail"
  if failures > 0 then
    throw (IO.userError s!"{failures} chain fuzz failures")

-- ============================================================
-- 3. Binary operators × 15 random theory pairs
-- ============================================================

#eval do
  IO.println "\n=== fuzz: binary operators × random pairs ==="
  let mut rng : RNG := { state := 271 }
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for i in List.range 15 do
    let (r, t1) := randomTheory rng s!"binL_{i}"
    let (r, t2) := randomTheory r s!"binR_{i}"
    rng := r
    if !(CatLab.validate t1).isEmpty || !(CatLab.validate t2).isEmpty then continue
    for (opName, op) in binaryOps do
      total := total + 1
      let errors := CatLab.validate (op t1 t2)
      if !errors.isEmpty then
        failures := failures + 1
        if failures <= 5 then
          IO.println s!"[FAIL] {opName}(binL_{i}, binR_{i}): {errors.length} errors"
          for e in errors.take 2 do IO.println s!"  - {e}"
  IO.println s!"Fuzzed {total} binary: {total - failures} pass, {failures} fail"
  if failures > 0 then
    throw (IO.userError s!"{failures} binary fuzz failures")

-- ============================================================
-- 4. Mixed chains: unary + binary, depth 2-3
-- ============================================================

#eval do
  IO.println "\n=== fuzz: mixed chains unary+binary ==="
  let mut rng : RNG := { state := 314 }
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for i in List.range 15 do
    let (r, t) := randomTheory rng s!"mix_{i}"
    rng := r
    if !(CatLab.validate t).isEmpty then continue
    let (r, depth) := r.natRange 2 3; rng := r
    let mut current := t
    let mut chainDesc : List String := []
    for step in List.range depth do
      let (r, coin) := rng.natMod 10; rng := r
      if coin < 7 then
        let (r, opIdx) := rng.natMod lightOps.length; rng := r
        let (opName, op) := lightOps[opIdx]!
        current := op current
        chainDesc := chainDesc ++ [opName]
      else
        let (r, t2) := randomTheory r s!"mix_{i}_aux_{step}"; rng := r
        if !(CatLab.validate t2).isEmpty then continue
        let (r, opIdx) := rng.natMod binaryOps.length; rng := r
        let (opName, op) := binaryOps[opIdx]!
        current := op current t2
        chainDesc := chainDesc ++ [s!"{opName}(_, aux)"]
    total := total + 1
    let errors := CatLab.validate current
    if !errors.isEmpty then
      failures := failures + 1
      if failures <= 5 then
        IO.println s!"[FAIL] mixed_{i} [{String.intercalate " → " chainDesc}]: {errors.length} errors"
        for e in errors.take 2 do IO.println s!"  - {e}"
  IO.println s!"Fuzzed {total} mixed: {total - failures} pass, {failures} fail"
  if failures > 0 then
    throw (IO.userError s!"{failures} mixed chain fuzz failures")

-- ============================================================
-- 5. Degenerate inputs: empty, point, arrow, loop × all operators
-- ============================================================

private def emptyTheory : Theory :=
  { name := "Empty", doctrine := { doctrine := .Category }
    objects := [], morphisms := [], axioms := [] }

private def pointTheory : Theory :=
  { name := "Pt", doctrine := { doctrine := .Category }
    objects := [{ id := gid "X" }], morphisms := [], axioms := [] }

private def arrowTheory' : Theory :=
  let f : Generator1 :=
    { id := gid "f" (k := .morphism), domain := .atom (gid "A"), codomain := .atom (gid "B") }
  { name := "Arr", doctrine := { doctrine := .Category }
    objects := [{ id := gid "A" }, { id := gid "B" }]
    morphisms := [f], axioms := [] }

private def loopTheory : Theory :=
  let e : Generator1 :=
    { id := gid "e" (k := .morphism), domain := .atom (gid "X"), codomain := .atom (gid "X") }
  let idem : Generator2 :=
    { id := gid "idem" (k := .twoCell)
      leftPath := .comp (.atom e.id) (.atom e.id)
      rightPath := .atom e.id }
  { name := "Loop", doctrine := { doctrine := .Category }
    objects := [{ id := gid "X" }], morphisms := [e], axioms := [idem] }

#eval do
  IO.println "\n=== fuzz: degenerate inputs ==="
  let degenerates := [("Empty", emptyTheory), ("Pt", pointTheory),
                      ("Arr", arrowTheory'), ("Loop", loopTheory)]
  let mut failures : Nat := 0
  let mut total : Nat := 0
  for (tName, t) in degenerates do
    for (opName, op) in allUnaryOps do
      total := total + 1
      let errors := CatLab.validate (op t)
      if !errors.isEmpty then
        failures := failures + 1
        if failures <= 10 then
          IO.println s!"[FAIL] {opName}({tName}): {errors.length} errors"
          for e in errors.take 2 do IO.println s!"  - {e}"
    for (tName2, t2) in degenerates do
      for (opName, op) in binaryOps do
        total := total + 1
        let errors := CatLab.validate (op t t2)
        if !errors.isEmpty then
          failures := failures + 1
          if failures <= 10 then
            IO.println s!"[FAIL] {opName}({tName},{tName2}): {errors.length} errors"
            for e in errors.take 2 do IO.println s!"  - {e}"
  IO.println s!"Tested {total} degenerate: {total - failures} pass, {failures} fail"
  if failures > 0 then
    throw (IO.userError s!"{failures} degenerate input failures")

end CatLab.Tests.Fuzz
