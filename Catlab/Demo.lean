/-
  CatLab -- Demonstrations

  Runnable examples showing the CAS in action.
-/

import Catlab.Core.Theory
import Catlab.Operators.Mirror
import Catlab.Operators.DayConvolution
import Catlab.Operators.Limits
import Catlab.Library.Monoid
import Catlab.Library.Group
import Catlab.Library.Ring

namespace CatLab.Demo

open CatLab.Library

-- ============================================================
-- Example A: Tensor(Monoids, AbelianGroups) → Rings
-- ============================================================

def exampleA : Theory := tensorTheories TheoryOfMonoids TheoryOfAbelianGroups

#eval do
  let t := exampleA
  IO.println s!"=== Example A: Tensor Product of Theories ==="
  IO.println s!"Input:  {TheoryOfMonoids.name} ⊗ {TheoryOfAbelianGroups.name}"
  IO.println s!"Output: {t.name}"
  IO.println s!"  Objects:   {t.objects.length}"
  IO.println s!"  Morphisms: {t.morphisms.length}"
  IO.println s!"  Axioms:    {t.axioms.length}"
  IO.println ""
  IO.println "Objects:"
  for obj in t.objects do
    IO.println s!"  • {obj.id.name}: {obj.description}"
  IO.println ""
  IO.println "Morphisms:"
  for mor in t.morphisms do
    IO.println s!"  • {mor.id.name}: {mor.description}"
  IO.println ""
  IO.println "Axioms (inherited + interchange):"
  for ax in t.axioms do
    IO.println s!"  • {ax.id.name}: {ax.description}"

-- ============================================================
-- Example B: Mirror(BooleanAlgebra) → Stone Spaces
-- ============================================================

def TheoryOfBooleanAlgebra : Theory :=
  let B := Expr.atom ⟨"B", 0⟩
  { name := "BooleanAlgebra"
    doctrine := { doctrine := .CartesianClosed }
    objects := [{ id := ⟨"B", 0⟩, description := "The carrier lattice" }]
    morphisms := [
      { id := ⟨"∧", 0⟩, domain := .prod B B, codomain := B,
        description := "Meet (AND): B × B → B" },
      { id := ⟨"∨", 0⟩, domain := .prod B B, codomain := B,
        description := "Join (OR): B × B → B" },
      { id := ⟨"¬", 0⟩, domain := B, codomain := B,
        description := "Complement (NOT): B → B" },
      { id := ⟨"⊤", 0⟩, domain := .terminal, codomain := B,
        description := "Top (TRUE): 1 → B" },
      { id := ⟨"⊥", 0⟩, domain := .terminal, codomain := B,
        description := "Bottom (FALSE): 1 → B" }
    ]
    axioms := [
      { id := ⟨"meet_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∧", 0⟩) (.id B)) (.atom ⟨"∧", 0⟩)
        rightPath := .comp (.prod (.id B) (.atom ⟨"∧", 0⟩)) (.atom ⟨"∧", 0⟩)
        description := "Meet is associative" },
      { id := ⟨"meet_comm", 0⟩
        leftPath := .atom ⟨"∧", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∧", 0⟩)
        description := "Meet is commutative" },
      { id := ⟨"join_assoc", 0⟩
        leftPath := .comp (.prod (.atom ⟨"∨", 0⟩) (.id B)) (.atom ⟨"∨", 0⟩)
        rightPath := .comp (.prod (.id B) (.atom ⟨"∨", 0⟩)) (.atom ⟨"∨", 0⟩)
        description := "Join is associative" },
      { id := ⟨"join_comm", 0⟩
        leftPath := .atom ⟨"∨", 0⟩
        rightPath := .comp (.atom ⟨"swap", 0⟩) (.atom ⟨"∨", 0⟩)
        description := "Join is commutative" },
      { id := ⟨"complement", 0⟩
        leftPath := .comp (.prod (.id B) (.atom ⟨"¬", 0⟩)) (.atom ⟨"∧", 0⟩)
        rightPath := .atom ⟨"⊥", 0⟩
        description := "a ∧ ¬a = ⊥" },
      { id := ⟨"excluded_middle", 0⟩
        leftPath := .comp (.prod (.id B) (.atom ⟨"¬", 0⟩)) (.atom ⟨"∨", 0⟩)
        rightPath := .atom ⟨"⊤", 0⟩
        description := "a ∨ ¬a = ⊤" }
    ] }

def exampleB : Theory := mirror TheoryOfBooleanAlgebra

#eval do
  let t := exampleB
  IO.println s!"=== Example B: Stone Duality ==="
  IO.println s!"Input:  Mirror({TheoryOfBooleanAlgebra.name})"
  IO.println s!"Output: {t.name}"
  IO.println ""
  IO.println "Morphisms (arrows reversed — logic becomes geometry):"
  for mor in t.morphisms do
    IO.println s!"  • {mor.id.name}: {mor.description}"
  IO.println ""
  IO.println "Axioms (sides swapped):"
  for ax in t.axioms do
    IO.println s!"  • {ax.id.name}: {ax.description}"

-- ============================================================
-- Example: Pullback computation
-- ============================================================

#eval do
  IO.println s!"=== Pullback Example ==="
  let f : Generator1 := { id := ⟨"f", 0⟩, domain := .atom ⟨"A", 0⟩, codomain := .atom ⟨"C", 0⟩ }
  let g : Generator1 := { id := ⟨"g", 0⟩, domain := .atom ⟨"B", 0⟩, codomain := .atom ⟨"C", 0⟩ }
  let pb := computePullback f g
  IO.println s!"Pullback of f : A → C and g : B → C"
  IO.println s!"  New object: {pb.object.id.name}"
  for mor in pb.morphisms do
    IO.println s!"  Projection: {mor.id.name}"
  for ax in pb.axioms do
    IO.println s!"  Axiom: {ax.description}"

end CatLab.Demo
