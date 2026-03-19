/-
  CatLab — Booleanization (Double Negation Translation)

  Takes a topos or Heyting category and forces ¬¬p → p, collapsing
  Heyting structure to Boolean. This is the syntactic counterpart of
  ¬¬-sheafification: we adjoin double negation elimination and
  excluded middle, turning an intuitionistic theory into a classical one.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Check whether a theory has a Heyting negation morphism. -/
private def hasHeytingNegation (t : Theory) : Bool :=
  t.morphisms.any (fun m => m.id.name == .root "¬" || m.id.name.isNeg?.isSome)

/-- Find all morphisms that are negation operations (using structured Name matching). -/
private def negationMorphisms (t : Theory) : List Generator1 :=
  t.morphisms.filter (fun m =>
    match m.id.name with
    | .root "¬" => true
    | .neg _ => true
    | .app (.root "¬") _ => true
    | _ => false)

/-- Booleanize a theory: adjoin double negation elimination and excluded middle.

    For each object A in the theory:
    - Add ¬¬A → A  (double negation elimination)
    - Add A ∨ ¬A = ⊤  (excluded middle / law of excluded third)

    For each morphism with a Heyting negation ¬f:
    - Add ¬¬f = f  (involutivity of negation on morphisms)

    The resulting doctrine is set to CartesianClosed with a "Boolean" constraint,
    reflecting that all Heyting structure has collapsed. -/
def booleanize (t : Theory) : Theory :=
  -- Derived objects: ¬A and ¬¬A for each object A
  let negObjects := t.objects.flatMap fun obj =>
    let notId : GeneratorId := { name := .neg obj.id.name, kind := .sort }
    let notNotId : GeneratorId := { name := .neg (.neg obj.id.name), kind := .sort }
    [ { id := notId, description := s!"¬{obj.id}" : Generator0 },
      { id := notNotId, description := s!"¬¬{obj.id}" : Generator0 } ]

  -- Double negation elimination: for each object A, a morphism ¬¬A → A
  let dneObjects := t.objects.map fun obj =>
    let a := Expr.atom obj.id
    let notAId : GeneratorId := { name := .neg obj.id.name, kind := .sort }
    let notA := Expr.atom notAId
    let notNotAId : GeneratorId := { name := .neg (.neg obj.id.name), kind := .sort }
    let notNotA := Expr.atom notNotAId
    { id := { name := .nested (.root "dne") obj.id.name.toString
              kind := .morphism }
      domain := notNotA
      codomain := a
      description := s!"Double negation elimination: ¬¬{obj.id} → {obj.id}" : Generator1 }

  -- Excluded middle: for each object A, a morphism ⊤ → A ∨ ¬A
  let emObjects := t.objects.map fun obj =>
    let a := Expr.atom obj.id
    let notA := Expr.atom { name := .neg obj.id.name, kind := .sort : GeneratorId }
    { id := { name := .nested (.root "em") obj.id.name.toString
              kind := .morphism }
      domain := .terminal
      codomain := .coprod a notA
      description := s!"Excluded middle: ⊤ → {obj.id} ∨ ¬{obj.id}" : Generator1 }

  -- Double negation elimination axiom schema:
  -- For each object A, ¬¬A composed with dne gives identity
  let dneAxioms := t.objects.map fun obj =>
    let a := Expr.atom obj.id
    let dne := Expr.atom { name := .nested (.root "dne") obj.id.name.toString
                           kind := .morphism }
    let notNot := Expr.atom { name := .neg (.neg obj.id.name), kind := .sort }
    { id := { name := .nested (.root "dne_section") obj.id.name.toString
              kind := .twoCell }
      leftPath := .comp notNot dne
      rightPath := .id a
      description := s!"¬¬-elimination is a retraction for {obj.id}" : Generator2 }

  -- Excluded middle axiom: em factors through the codiagonal
  let emAxioms := t.objects.map fun obj =>
    let a := Expr.atom obj.id
    let notA := Expr.atom { name := .neg obj.id.name, kind := .sort : GeneratorId }
    let em := Expr.atom { name := .nested (.root "em") obj.id.name.toString
                          kind := .morphism }
    { id := { name := .nested (.root "em_axiom") obj.id.name.toString
              kind := .twoCell }
      leftPath := em
      rightPath := .comp (.inj 0 (.coprod a notA)) (.id (.coprod a notA))
      description := s!"Excluded middle axiom for {obj.id}" : Generator2 }

  -- Involutivity: for each negation morphism, ¬¬f = f
  let negMorphisms := negationMorphisms t
  let involutivityAxioms := negMorphisms.map fun m =>
    { id := { name := .nested (.root "involutive") m.id.name.toString
              kind := .twoCell }
      leftPath := .comp (.atom m.id) (.comp (.atom m.id) (.id m.domain))
      rightPath := .id m.domain
      description := s!"Negation is involutive: ¬¬({m.id}) = id" : Generator2 }

  { t with
    name := s!"Bool({t.name})"
    doctrine := { doctrine := .CartesianClosed
                  constraints := ["Boolean", "¬¬-stable"] }
    objects := t.objects ++ negObjects
    morphisms := t.morphisms ++ dneObjects ++ emObjects
    axioms := t.axioms ++ dneAxioms ++ emAxioms ++ involutivityAxioms }

/-- A convenience wrapper: booleanize and verify that the original theory
    was at least Heyting (had a negation operation). Returns `none` if
    the theory has no negation to collapse. -/
def booleanize? (t : Theory) : Option Theory :=
  if hasHeytingNegation t then some (booleanize t)
  else none

end CatLab
