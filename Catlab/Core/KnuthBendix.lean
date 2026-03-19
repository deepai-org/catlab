/-
  CatLab -- Knuth-Bendix Completion

  Given a set of equations over CatLab Expr, computes a confluent terminating
  rewrite system (if one exists). Once complete, normalization becomes a
  decision procedure: two terms are equal iff they have the same normal form.

  Supports both ground terms (atoms, comp, id, etc.) and variable terms (.var).
  When axioms contain variables, proper unification (MGU) is used for matching
  and critical pair computation, not just syntactic equality.

  Algorithm:
  1. Orient initial equations using LPO (lexicographic path ordering)
  2. Compute critical pairs via unification of rule LHS overlaps
  3. Normalize critical pairs using current rules (via pattern matching)
  4. Orient new equations, add to rule set
  5. Inter-reduce: simplify RHS's; push reduced LHS's back as equations
  6. Repeat until no new critical pairs (convergence) or limit hit

  Reference: Baader & Nipkow, "Term Rewriting and All That", Chapter 7
-/

import Catlab.Core.Theory
import Catlab.Core.Equality

namespace CatLab.KnuthBendix

open CatLab

-- ============================================================
-- Substitutions and Unification
-- ============================================================

/-- A substitution maps variable names to expressions. -/
abbrev Substitution := List (String × Expr)

/-- Apply a substitution to an expression. -/
partial def applySubst (σ : Substitution) (e : Expr) : Expr :=
  match e with
  | .var n => match σ.find? (·.1 == n) with
    | some (_, v) => v  -- single substitution step (no transitive chase)
    | none => e
  | .atom _ | .unit | .terminal | .initial => e
  | .id obj => .id (applySubst σ obj)
  | .comp f g => .comp (applySubst σ f) (applySubst σ g)
  | .prod a b => .prod (applySubst σ a) (applySubst σ b)
  | .coprod a b => .coprod (applySubst σ a) (applySubst σ b)
  | .tensor a b => .tensor (applySubst σ a) (applySubst σ b)
  | .hom a b => .hom (applySubst σ a) (applySubst σ b)
  | .fiber a b => .fiber (applySubst σ a) (applySubst σ b)
  | .app f x => .app (applySubst σ f) (applySubst σ x)
  | .natComponent n x => .natComponent (applySubst σ n) (applySubst σ x)
  | .sigma v b f => .sigma v (applySubst σ b) (applySubst σ f)
  | .pi v b f => .pi v (applySubst σ b) (applySubst σ f)
  | .proj i s => .proj i (applySubst σ s)
  | .inj i s => .inj i (applySubst σ s)
  | .limit d => .limit (applySubst σ d)
  | .colimit d => .colimit (applySubst σ d)

/-- Check if a variable occurs in an expression (occurs check). -/
private partial def occursIn (varName : String) (e : Expr) : Bool :=
  match e with
  | .var n => n == varName
  | .atom _ | .unit | .terminal | .initial => false
  | .id obj => occursIn varName obj
  | .comp f g | .prod f g | .coprod f g | .tensor f g
  | .hom f g | .fiber f g | .app f g | .natComponent f g =>
    occursIn varName f || occursIn varName g
  | .sigma _ b f | .pi _ b f => occursIn varName b || occursIn varName f
  | .proj _ s | .inj _ s | .limit s | .colimit s => occursIn varName s

/-- Compose two substitutions: apply σ2 after σ1. -/
private def composeSubst (σ1 σ2 : Substitution) : Substitution :=
  let updated := σ1.map fun (n, e) => (n, applySubst σ2 e)
  let newBindings := σ2.filter fun (n, _) => !σ1.any (·.1 == n)
  updated ++ newBindings

/-- Most General Unifier (MGU) via Robinson's algorithm.
    Returns the MGU substitution if terms are unifiable, none otherwise. -/
partial def unify (s t : Expr) (σ : Substitution := []) : Option Substitution :=
  let s' := applySubst σ s
  let t' := applySubst σ t
  if s' == t' then some σ
  else match s', t' with
  | .var n, e =>
    if occursIn n e then none  -- occurs check
    else some (composeSubst σ [(n, e)])
  | e, .var n =>
    if occursIn n e then none
    else some (composeSubst σ [(n, e)])
  | .id a, .id b => unify a b σ
  | .comp f1 g1, .comp f2 g2 => do let σ' ← unify f1 f2 σ; unify g1 g2 σ'
  | .prod a1 b1, .prod a2 b2 => do let σ' ← unify a1 a2 σ; unify b1 b2 σ'
  | .coprod a1 b1, .coprod a2 b2 => do let σ' ← unify a1 a2 σ; unify b1 b2 σ'
  | .tensor a1 b1, .tensor a2 b2 => do let σ' ← unify a1 a2 σ; unify b1 b2 σ'
  | .hom a1 b1, .hom a2 b2 => do let σ' ← unify a1 a2 σ; unify b1 b2 σ'
  | .fiber a1 b1, .fiber a2 b2 => do let σ' ← unify a1 a2 σ; unify b1 b2 σ'
  | .app f1 x1, .app f2 x2 => do let σ' ← unify f1 f2 σ; unify x1 x2 σ'
  | .natComponent n1 x1, .natComponent n2 x2 => do let σ' ← unify n1 n2 σ; unify x1 x2 σ'
  | .sigma v1 b1 f1, .sigma v2 b2 f2 =>
    if v1 == v2 then do let σ' ← unify b1 b2 σ; unify f1 f2 σ'
    else none
  | .pi v1 b1 f1, .pi v2 b2 f2 =>
    if v1 == v2 then do let σ' ← unify b1 b2 σ; unify f1 f2 σ'
    else none
  | .proj i1 s1, .proj i2 s2 => if i1 == i2 then unify s1 s2 σ else none
  | .inj i1 s1, .inj i2 s2 => if i1 == i2 then unify s1 s2 σ else none
  | .limit d1, .limit d2 => unify d1 d2 σ
  | .colimit d1, .colimit d2 => unify d1 d2 σ
  | _, _ => none

/-- Pattern matching: find substitution σ such that applySubst σ pattern = target.
    Unlike unification, only variables in the pattern can be bound. -/
partial def matchExpr (pat target : Expr) (σ : Substitution := []) : Option Substitution :=
  let pat' := applySubst σ pat
  if pat' == target then some σ
  else match pat', target with
  | .var n, e =>
    -- Check consistency: if n already bound, it must match
    match σ.find? (·.1 == n) with
    | some (_, v) => if v == e then some σ else none
    | none =>
      if occursIn n e then none
      else some (σ ++ [(n, e)])
  | .id a, .id b => matchExpr a b σ
  | .comp f1 g1, .comp f2 g2 => do let σ' ← matchExpr f1 f2 σ; matchExpr g1 g2 σ'
  | .prod a1 b1, .prod a2 b2 => do let σ' ← matchExpr a1 a2 σ; matchExpr b1 b2 σ'
  | .coprod a1 b1, .coprod a2 b2 => do let σ' ← matchExpr a1 a2 σ; matchExpr b1 b2 σ'
  | .tensor a1 b1, .tensor a2 b2 => do let σ' ← matchExpr a1 a2 σ; matchExpr b1 b2 σ'
  | .hom a1 b1, .hom a2 b2 => do let σ' ← matchExpr a1 a2 σ; matchExpr b1 b2 σ'
  | .fiber a1 b1, .fiber a2 b2 => do let σ' ← matchExpr a1 a2 σ; matchExpr b1 b2 σ'
  | .app f1 x1, .app f2 x2 => do let σ' ← matchExpr f1 f2 σ; matchExpr x1 x2 σ'
  | .natComponent n1 x1, .natComponent n2 x2 => do
    let σ' ← matchExpr n1 n2 σ; matchExpr x1 x2 σ'
  | .sigma v1 b1 f1, .sigma v2 b2 f2 =>
    if v1 == v2 then do let σ' ← matchExpr b1 b2 σ; matchExpr f1 f2 σ'
    else none
  | .pi v1 b1 f1, .pi v2 b2 f2 =>
    if v1 == v2 then do let σ' ← matchExpr b1 b2 σ; matchExpr f1 f2 σ'
    else none
  | .proj i1 s1, .proj i2 s2 => if i1 == i2 then matchExpr s1 s2 σ else none
  | .inj i1 s1, .inj i2 s2 => if i1 == i2 then matchExpr s1 s2 σ else none
  | .limit d1, .limit d2 => matchExpr d1 d2 σ
  | .colimit d1, .colimit d2 => matchExpr d1 d2 σ
  | _, _ => none

-- ============================================================
-- Variable renaming (to avoid capture during unification)
-- ============================================================

/-- Collect all variable names in an expression. -/
private partial def varNames (e : Expr) : List String :=
  match e with
  | .var n => [n]
  | .atom _ | .unit | .terminal | .initial => []
  | .id obj => varNames obj
  | .comp f g | .prod f g | .coprod f g | .tensor f g
  | .hom f g | .fiber f g | .app f g | .natComponent f g =>
    varNames f ++ varNames g
  | .sigma _ b f | .pi _ b f => varNames b ++ varNames f
  | .proj _ s | .inj _ s | .limit s | .colimit s => varNames s

/-- Rename all variables in an expression by adding a suffix. -/
private partial def renameVars (e : Expr) (suffix : String) : Expr :=
  match e with
  | .var n => .var (n ++ suffix)
  | .atom _ | .unit | .terminal | .initial => e
  | .id obj => .id (renameVars obj suffix)
  | .comp f g => .comp (renameVars f suffix) (renameVars g suffix)
  | .prod a b => .prod (renameVars a suffix) (renameVars b suffix)
  | .coprod a b => .coprod (renameVars a suffix) (renameVars b suffix)
  | .tensor a b => .tensor (renameVars a suffix) (renameVars b suffix)
  | .hom a b => .hom (renameVars a suffix) (renameVars b suffix)
  | .fiber a b => .fiber (renameVars a suffix) (renameVars b suffix)
  | .app f x => .app (renameVars f suffix) (renameVars x suffix)
  | .natComponent n x => .natComponent (renameVars n suffix) (renameVars x suffix)
  | .sigma v b f => .sigma v (renameVars b suffix) (renameVars f suffix)
  | .pi v b f => .pi v (renameVars b suffix) (renameVars f suffix)
  | .proj i s => .proj i (renameVars s suffix)
  | .inj i s => .inj i (renameVars s suffix)
  | .limit d => .limit (renameVars d suffix)
  | .colimit d => .colimit (renameVars d suffix)

-- ============================================================
-- Term ordering: Lexicographic Path Ordering (LPO)
-- ============================================================

/-- Precedence on Expr head constructors. Higher = bigger. -/
private def headPrecedence : Expr → Nat
  | .initial     => 0
  | .terminal    => 1
  | .unit        => 2
  | .var _       => 3
  | .atom _      => 10
  | .id _        => 20
  | .inj _ _     => 21
  | .proj _ _    => 22
  | .comp _ _    => 30
  | .prod _ _    => 31
  | .coprod _ _  => 32
  | .tensor _ _  => 33
  | .hom _ _     => 34
  | .fiber _ _   => 35
  | .app _ _     => 36
  | .sigma _ _ _ => 40
  | .pi _ _ _    => 41
  | .limit _     => 50
  | .colimit _   => 51
  | .natComponent _ _ => 52

/-- Get the immediate subexpressions of an expression. -/
private def subexprs : Expr → List Expr
  | .atom _      => []
  | .unit        => []
  | .terminal    => []
  | .initial     => []
  | .var _       => []
  | .id e        => [e]
  | .comp a b    => [a, b]
  | .prod a b    => [a, b]
  | .coprod a b  => [a, b]
  | .tensor a b  => [a, b]
  | .hom a b     => [a, b]
  | .fiber a b   => [a, b]
  | .app a b     => [a, b]
  | .natComponent a b => [a, b]
  | .sigma _ b f => [b, f]
  | .pi _ b f    => [b, f]
  | .proj _ s    => [s]
  | .inj _ s     => [s]
  | .limit d     => [d]
  | .colimit d   => [d]

/-- Lexicographic Path Ordering (LPO).
    Returns true if s > t in the ordering (s is "bigger" / more complex). -/
partial def lpoGt (s t : Expr) : Bool :=
  -- Rule 1: s > t if some subexpr of s ≥ t
  if subexprs s |>.any (fun si => si == t || lpoGt si t) then true
  else
    let sHead := headPrecedence s
    let tHead := headPrecedence t
    let tSubs := subexprs t
    if sHead > tHead then
      tSubs.all (lpoGt s)
    else if sHead == tHead then
      match s, t with
      | .atom g1, .atom g2 =>
        decide (g1.name.toString > g2.name.toString)
      | _, _ =>
        let sSubs := subexprs s
        let rec lexCmp (xs ys : List Expr) : Bool :=
          match xs, ys with
          | [], _ => false
          | _, [] => false
          | x :: xs', y :: ys' =>
            if lpoGt x y then tSubs.all (lpoGt s)
            else if x == y then lexCmp xs' ys'
            else false
        sSubs.length == tSubs.length && lexCmp sSubs tSubs
    else false

/-- Compare two expressions: .gt if s > t, .lt if t > s, .eq if equal,
    .eq also for incomparable (caller must handle). -/
def lpoCompare (s t : Expr) : Ordering :=
  if s == t then .eq
  else if lpoGt s t then .gt
  else if lpoGt t s then .lt
  else .eq  -- incomparable

-- ============================================================
-- Rewrite rules and matching
-- ============================================================

/-- A rewrite rule: lhs → rhs, where lhs > rhs in the term ordering. -/
structure Rule where
  lhs : Expr
  rhs : Expr
  deriving Repr, Inhabited

instance : BEq Rule where
  beq r1 r2 := r1.lhs == r2.lhs && r1.rhs == r2.rhs

/-- Apply a single rule at the root of an expression via pattern matching.
    Returns the instantiated RHS if the rule's LHS matches the expression. -/
private def applyRuleRoot (r : Rule) (e : Expr) : Option Expr :=
  match matchExpr r.lhs e with
  | some σ => some (applySubst σ r.rhs)
  | none => none

/-- Apply rules at all positions (leftmost-outermost). -/
private partial def rewriteOnce (rules : List Rule) (e : Expr) : Option Expr :=
  match rules.findSome? (applyRuleRoot · e) with
  | some e' => some e'
  | none =>
    match e with
    | .comp f g =>
      match rewriteOnce rules f with
      | some f' => some (.comp f' g)
      | none    => (rewriteOnce rules g).map (.comp f)
    | .id obj   => (rewriteOnce rules obj).map .id
    | .prod a b =>
      match rewriteOnce rules a with
      | some a' => some (.prod a' b)
      | none    => (rewriteOnce rules b).map (.prod a)
    | .tensor a b =>
      match rewriteOnce rules a with
      | some a' => some (.tensor a' b)
      | none    => (rewriteOnce rules b).map (.tensor a)
    | .hom a b =>
      match rewriteOnce rules a with
      | some a' => some (.hom a' b)
      | none    => (rewriteOnce rules b).map (.hom a)
    | .coprod a b =>
      match rewriteOnce rules a with
      | some a' => some (.coprod a' b)
      | none    => (rewriteOnce rules b).map (.coprod a)
    | .app f x =>
      match rewriteOnce rules f with
      | some f' => some (.app f' x)
      | none    => (rewriteOnce rules x).map (.app f)
    | .fiber m p =>
      match rewriteOnce rules m with
      | some m' => some (.fiber m' p)
      | none    => (rewriteOnce rules p).map (.fiber m)
    | .sigma v b f =>
      match rewriteOnce rules b with
      | some b' => some (.sigma v b' f)
      | none    => (rewriteOnce rules f).map (.sigma v b)
    | .pi v b f =>
      match rewriteOnce rules b with
      | some b' => some (.pi v b' f)
      | none    => (rewriteOnce rules f).map (.pi v b)
    | .proj i s => (rewriteOnce rules s).map (.proj i)
    | .inj i t  => (rewriteOnce rules t).map (.inj i)
    | .limit d  => (rewriteOnce rules d).map .limit
    | .colimit d => (rewriteOnce rules d).map .colimit
    | .natComponent n x =>
      match rewriteOnce rules n with
      | some n' => some (.natComponent n' x)
      | none    => (rewriteOnce rules x).map (.natComponent n)
    | _ => none

/-- Normalize an expression to normal form under the given rules.
    Uses fuel (countdown) to guarantee termination without `partial`. -/
def normalize (rules : List Rule) (e : Expr) (fuel : Nat := 1000) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match rewriteOnce rules e with
    | none => e
    | some e' => normalize rules e' fuel'

-- ============================================================
-- Critical pair computation (with unification)
-- ============================================================

/-- An equation: two expressions that should be equal. -/
structure Equation where
  lhs : Expr
  rhs : Expr
  deriving Repr, Inhabited

instance : BEq Equation where
  beq e1 e2 := e1.lhs == e2.lhs && e1.rhs == e2.rhs

/-- Counter for generating fresh variable suffixes. -/
private def freshSuffix (n : Nat) : String := s!"_{n}"

/-- Find critical pairs by unifying r2's LHS with subterms of r1's LHS.
    r1 and r2 should have disjoint variables (caller must rename). -/
private partial def criticalPairsFrom (r1 r2 : Rule) : List Equation :=
  let rec atPos (e : Expr) (ctx : Expr → Expr) : List Equation :=
    -- Try to unify r2.lhs with the current subterm e
    let rootPairs :=
      -- Don't unify a variable with an entire rule (trivial overlap)
      match e with
      | .var _ => []
      | _ =>
        match unify r2.lhs e with
        | some σ =>
          let lhs := applySubst σ r1.rhs
          let rhs := applySubst σ (ctx r2.rhs)
          if lhs == rhs then [] else [{ lhs, rhs : Equation }]
        | none => []
    -- Recurse into subterms (only for non-variable positions)
    let subPairs := match e with
      | .comp f g =>
        atPos f (fun f' => ctx (.comp f' g)) ++
        atPos g (fun g' => ctx (.comp f g'))
      | .prod a b =>
        atPos a (fun a' => ctx (.prod a' b)) ++
        atPos b (fun b' => ctx (.prod a b'))
      | .tensor a b =>
        atPos a (fun a' => ctx (.tensor a' b)) ++
        atPos b (fun b' => ctx (.tensor a b'))
      | .hom a b =>
        atPos a (fun a' => ctx (.hom a' b)) ++
        atPos b (fun b' => ctx (.hom a b'))
      | .coprod a b =>
        atPos a (fun a' => ctx (.coprod a' b)) ++
        atPos b (fun b' => ctx (.coprod a b'))
      | .id obj => atPos obj (fun o' => ctx (.id o'))
      | .app f x =>
        atPos f (fun f' => ctx (.app f' x)) ++
        atPos x (fun x' => ctx (.app f x'))
      | .fiber m p =>
        atPos m (fun m' => ctx (.fiber m' p)) ++
        atPos p (fun p' => ctx (.fiber m p'))
      | .sigma v b f =>
        atPos b (fun b' => ctx (.sigma v b' f)) ++
        atPos f (fun f' => ctx (.sigma v b f'))
      | .pi v b f =>
        atPos b (fun b' => ctx (.pi v b' f)) ++
        atPos f (fun f' => ctx (.pi v b f'))
      | .proj i s => atPos s (fun s' => ctx (.proj i s'))
      | .inj i t  => atPos t (fun t' => ctx (.inj i t'))
      | .limit d  => atPos d (fun d' => ctx (.limit d'))
      | .colimit d => atPos d (fun d' => ctx (.colimit d'))
      | .natComponent n x =>
        atPos n (fun n' => ctx (.natComponent n' x)) ++
        atPos x (fun x' => ctx (.natComponent n x'))
      | _ => []
    rootPairs ++ subPairs
  atPos r1.lhs (fun x => x)

/-- Compute critical pairs between new rules and all existing rules.
    Only computes (new × all) ∪ (all × new) to avoid redundant work. -/
private def newCriticalPairs
    (existingRules newRules : List Rule) (counter : Nat) : List Equation × Nat :=
  let allRules := existingRules ++ newRules
  -- New rules overlapping with all rules (including themselves)
  let (cps1, ctr1) := newRules.foldl (fun (acc, ctr) r1 =>
    allRules.foldl (fun (acc2, ctr2) r2 =>
      let r2' := { lhs := renameVars r2.lhs (freshSuffix ctr2),
                    rhs := renameVars r2.rhs (freshSuffix ctr2) : Rule }
      (acc2 ++ criticalPairsFrom r1 r2', ctr2 + 1)
    ) (acc, ctr)
  ) ([], counter)
  -- All existing rules overlapping with new rules (avoid double-counting new×new)
  existingRules.foldl (fun (acc, ctr) r1 =>
    newRules.foldl (fun (acc2, ctr2) r2 =>
      let r2' := { lhs := renameVars r2.lhs (freshSuffix ctr2),
                    rhs := renameVars r2.rhs (freshSuffix ctr2) : Rule }
      (acc2 ++ criticalPairsFrom r1 r2', ctr2 + 1)
    ) (acc, ctr)
  ) (cps1, ctr1)

-- ============================================================
-- Knuth-Bendix completion
-- ============================================================

/-- Result of completion attempt. -/
inductive CompletionResult where
  | success (rules : List Rule)
  | failure (reason : String) (partialRules : List Rule)
  deriving Repr

instance : Inhabited CompletionResult := ⟨.success []⟩

/-- Orient an equation into a rule using LPO only.
    Returns none if the equation can't be oriented (incomparable terms).
    No size fallback — LPO is the sole reduction ordering for soundness. -/
private def orient (eq : Equation) : Option Rule :=
  if eq.lhs == eq.rhs then none
  else match lpoCompare eq.lhs eq.rhs with
  | .gt => some { lhs := eq.lhs, rhs := eq.rhs }
  | .lt => some { lhs := eq.rhs, rhs := eq.lhs }
  | .eq => none  -- unorientable: incomparable under LPO

/-- Inter-reduce: simplify RHS's with other rules. If a rule's LHS is
    reducible by another rule, remove it but return the reduced equation
    to be re-processed in the main loop. -/
private def interReduce (rules : List Rule) : (List Rule × List Equation) :=
  -- Step 1: simplify all RHS's
  let simplified := rules.map fun r =>
    let otherRules := rules.filter (· != r)
    { r with rhs := normalize otherRules r.rhs 100 }
  -- Step 2: check LHS reducibility; keep survivors, collect reduced equations
  let (revSurvivors, revNewEqs) := simplified.foldl (fun (survivors, newEqs) r =>
    let otherRules := simplified.filter (· != r)
    match rewriteOnce otherRules r.lhs with
    | none => (r :: survivors, newEqs)
    | some lhs' =>
      if lhs' != r.rhs then (survivors, { lhs := lhs', rhs := r.rhs } :: newEqs)
      else (survivors, newEqs)
  ) ([], [])
  (revSurvivors.reverse, revNewEqs.reverse)

/-- Inner loop for KB completion. Uses incremental critical pair computation. -/
partial def completeLoop
    (rules : List Rule) (pendingEqs : List Equation)
    (iteration maxRules maxIterations varCounter : Nat)
    : CompletionResult :=
  if iteration >= maxIterations then
    .failure s!"did not converge after {maxIterations} iterations" rules
  else if rules.length > maxRules then
    .failure s!"exceeded {maxRules} rules" rules
  else
    -- Orient pending equations into new rules
    let newRules := pendingEqs.filterMap orient
    let unorientable := pendingEqs.filter fun eq => (orient eq).isNone
    if newRules.isEmpty && unorientable.isEmpty then
      -- No new work: convergence check via full critical pairs
      -- (first iteration or after inter-reduction cleared pending)
      let (cps, ctr) := newCriticalPairs rules [] varCounter
      let normalizedCps := cps.filterMap fun eq =>
        let l := normalize rules eq.lhs 200
        let r := normalize rules eq.rhs 200
        if l == r then none
        else some ({ lhs := l, rhs := r } : Equation)
      if normalizedCps.isEmpty then
        .success rules
      else
        completeLoop rules normalizedCps (iteration + 1) maxRules maxIterations ctr
    else if newRules.isEmpty then
      .failure "unorientable critical pairs remain" rules
    else
      -- Compute critical pairs between new and existing rules
      let (cps, ctr) := newCriticalPairs rules newRules varCounter
      let allRules := rules ++ newRules
      -- Inter-reduce the combined set
      let (reduced, extraEqs) := interReduce allRules
      -- Normalize critical pairs under reduced rules
      let normalizedCps := cps.filterMap fun eq =>
        let l := normalize reduced eq.lhs 500
        let r := normalize reduced eq.rhs 500
        if l == r then none
        else some ({ lhs := l, rhs := r } : Equation)
      let allPending := normalizedCps ++ extraEqs
      if allPending.isEmpty then
        .success reduced
      else
        completeLoop reduced allPending (iteration + 1) maxRules maxIterations ctr

/-- Run Knuth-Bendix completion on a set of equations.
    Returns a confluent terminating rewrite system, or failure. -/
def complete
    (equations : List Equation)
    (maxRules : Nat := 50)
    (maxIterations : Nat := 30)
    : CompletionResult :=
  let initRules := equations.filterMap orient
  let unorientable := equations.filter fun eq => (orient eq).isNone
  if initRules.isEmpty && !equations.isEmpty then
    .failure "cannot orient any equation" []
  else
    -- Start with initial rules and feed unorientable equations as pending
    completeLoop initRules unorientable 0 maxRules maxIterations 0

-- ============================================================
-- Integration: Theory axioms → completed rewrite system
-- ============================================================

/-- Convert theory axioms to equations. Now includes quantified axioms —
    variables in quantifiers become .var terms that unification handles. -/
def axiomsToEquations (axioms : List Generator2) : List Equation :=
  axioms.filterMap fun ax =>
    if ax.leftPath == ax.rightPath then none
    else some { lhs := ax.leftPath, rhs := ax.rightPath }

/-- Complete a theory's axioms into a confluent rewrite system.
    Falls back to simple orientation if completion fails. -/
def completeTheory (axioms : List Generator2) : List Rule :=
  let eqs := axiomsToEquations axioms
  -- Guard: skip KB completion for large theories (critical pair explosion)
  if eqs.length > 10 then
    eqs.filterMap orient
  else
    match complete eqs (maxRules := 30) (maxIterations := 15) with
    | .success rules => rules
    | .failure _ partialRules =>
      if partialRules.isEmpty then eqs.filterMap orient
      else partialRules

/-- Normalize an expression using KB-completed rules from a theory's axioms. -/
def kbNormalize (axioms : List Generator2) (e : Expr) (fuel : Nat := 1000) : Expr :=
  let rules := completeTheory axioms
  normalize rules e fuel

/-- Check equality under a theory's axioms via KB normalization. -/
def kbEqual (axioms : List Generator2) (e1 e2 : Expr) : Bool :=
  let rules := completeTheory axioms
  normalize rules e1 1000 == normalize rules e2 1000

end CatLab.KnuthBendix
