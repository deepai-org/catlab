/-
  CatLab — Loop Space Operator

  Given a pointed type (X, x), the loop space Ω(X, x) is the type
    path(X, x, x)
  of loops at the base point.

  The theory of Ω(X, x) has:
    • The loop type ΩX (a sort)
    • refl : 1 → ΩX  (the trivial loop)
    • concat : ΩX × ΩX → ΩX  (path concatenation)
    • inv : ΩX → ΩX  (path inversion)
    • Left/right unit laws, inverse law, associativity

  This gives ΩX the structure of an ∞-group (group up to coherent homotopy).
  At the 1-truncated level, π₁(X, x) = ||Ω(X, x)||₀ is a group.
-/

import Catlab.Core.Theory

namespace CatLab

/-- Build the loop space theory Ω(T) from a theory T.
    Finds a basepoint (morphism 1 → X for some object X) and constructs
    the loop space at that point. If no basepoint exists, picks the first
    object and adds a formal basepoint.

    The result is a group-like theory capturing the loop space structure. -/
def loopSpace (t : Theory) : Theory :=
  -- Find a pointed object: a morphism with domain = terminal
  let pointed := t.morphisms.find? fun m =>
    match m.domain with | .terminal => true | _ => false
  let (spaceId, basepointId) : GeneratorId × GeneratorId := match pointed with
    | some m => (match m.codomain with
                 | .atom gid => gid
                 | _ => match t.objects.head? with
                        | some o => o.id | none => gid "X",
                 m.id)
    | none => (match t.objects.head? with
               | some o => o.id | none => gid "X",
               { name := .root "pt", kind := .morphism : GeneratorId })

  let spaceName := spaceId.name.toString
  let loopName := s!"Ω{spaceName}"
  let loopId : GeneratorId := { name := .root loopName, kind := .sort }
  let loopExpr := Expr.atom loopId

  -- refl : 1 → ΩX  (trivial loop)
  let reflId : GeneratorId := { name := .root "refl_loop", kind := .morphism }

  -- concat : ΩX × ΩX → ΩX  (path concatenation)
  let concatId : GeneratorId := { name := .root "concat", kind := .morphism }

  -- inv : ΩX → ΩX  (path reversal)
  let invId : GeneratorId := { name := .root "inv", kind := .morphism }

  { name := loopName
    doctrine := { doctrine := .MartinLofTypeTheory }
    objects := [
      { id := loopId
        description := s!"Loop space Ω({spaceName}) = path({spaceName}, {basepointId.name}, {basepointId.name})" }
    ]
    morphisms := [
      { id := reflId
        domain := .terminal
        codomain := loopExpr
        description := s!"Trivial loop: refl({basepointId.name}) : 1 → Ω({spaceName})" },
      { id := concatId
        domain := .prod loopExpr loopExpr
        codomain := loopExpr
        description := s!"Path concatenation: concat : Ω({spaceName}) × Ω({spaceName}) → Ω({spaceName})" },
      { id := invId
        domain := loopExpr
        codomain := loopExpr
        description := s!"Path inversion: inv : Ω({spaceName}) → Ω({spaceName})" }
    ]
    axioms := [
      -- Left unit: concat(refl, p) = p
      { id := gid "concat_left_unit"
        leftPath := .comp
          (.prod (.atom reflId) (.id loopExpr))
          (.atom concatId)
        rightPath := .id loopExpr
        description := "Left unit: concat(refl, p) = p" },
      -- Right unit: concat(p, refl) = p
      { id := gid "concat_right_unit"
        leftPath := .comp
          (.prod (.id loopExpr) (.atom reflId))
          (.atom concatId)
        rightPath := .id loopExpr
        description := "Right unit: concat(p, refl) = p" },
      -- Left inverse: concat(inv(p), p) = refl
      { id := gid "concat_left_inv"
        leftPath := .comp
          (.prod (.atom invId) (.id loopExpr))
          (.atom concatId)
        rightPath := .comp (.atom { name := .root "!", kind := .morphism }) (.atom reflId)
        description := "Left inverse: concat(inv(p), p) = refl" },
      -- Right inverse: concat(p, inv(p)) = refl
      { id := gid "concat_right_inv"
        leftPath := .comp
          (.prod (.id loopExpr) (.atom invId))
          (.atom concatId)
        rightPath := .comp (.atom { name := .root "!", kind := .morphism }) (.atom reflId)
        description := "Right inverse: concat(p, inv(p)) = refl" }
    ] }

end CatLab
