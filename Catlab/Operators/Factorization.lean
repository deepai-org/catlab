/-
  CatLab — Factorization System Envelope

  Given a category and a designated class of morphisms, freely adjoin a
  formal (E, M) orthogonal factorization system.

  For each morphism f : A → B we add:
    - An image object Im(f)
    - An E-morphism e_f : A → Im(f)
    - An M-morphism m_f : Im(f) → B
    - Axiom: m_f ∘ e_f = f

  For each commutative square with e in E and m in M we add:
    - A unique diagonal fill-in d
    - Orthogonality axioms: both triangles commute
-/

import Catlab.Core.Theory

namespace CatLab

/-- Data specifying which morphisms belong to the left (E) and right (M)
    classes of an orthogonal factorization system. -/
structure FactorizationData where
  leftClass : List GeneratorId   -- E-morphisms (e.g., epis)
  rightClass : List GeneratorId  -- M-morphisms (e.g., monos)
  deriving Repr, Inhabited

/-- Freely adjoin an (E, M) orthogonal factorization system to a theory.

    For every morphism f : A → B in the theory, we add:
    1. Im(f) — a factorization object
    2. e_f : A → Im(f) (in E) and m_f : Im(f) → B (in M)
    3. m_f ∘ e_f = f
    4. Diagonal fill-ins for commutative squares with e in E, m in M
    5. Orthogonality axioms for those diagonals -/
def factorizationEnvelope (t : Theory) (fd : FactorizationData) : Theory :=
  -- 1. For each morphism, add the image object Im(f)
  let imageObjects := t.morphisms.map fun f =>
    let imName : Name := .app (.root "Im") f.id.name
    ({ id := { name := imName, kind := .sort }
       description := s!"Image object Im({f.id.name})" }
      : Generator0)

  -- 2. For each morphism f : A → B, add e_f : A → Im(f) and m_f : Im(f) → B
  let eMorphisms := t.morphisms.map fun f =>
    let imId : GeneratorId := { name := .app (.root "Im") f.id.name, kind := .sort }
    ({ id := { name := .nested f.id.name "e", kind := .morphism }
       domain := f.domain
       codomain := .atom imId
       description := s!"E-morphism e_{f.id.name} : dom(f) → Im(f)" }
      : Generator1)

  let mMorphisms := t.morphisms.map fun f =>
    let imId : GeneratorId := { name := .app (.root "Im") f.id.name, kind := .sort }
    ({ id := { name := .nested f.id.name "m", kind := .morphism }
       domain := .atom imId
       codomain := f.codomain
       description := s!"M-morphism m_{f.id.name} : Im(f) → cod(f)" }
      : Generator1)

  -- 3. Factorization axiom: m_f ∘ e_f = f
  let factorizationAxioms := t.morphisms.map fun f =>
    let eId : GeneratorId := { name := .nested f.id.name "e", kind := .morphism }
    let mId : GeneratorId := { name := .nested f.id.name "m", kind := .morphism }
    ({ id := { name := .nested f.id.name "factor", kind := .twoCell }
       leftPath := .comp (.atom eId) (.atom mId)
       rightPath := .atom f.id
       description := s!"m_{f.id.name} ∘ e_{f.id.name} = {f.id.name}" }
      : Generator2)

  -- 4. Diagonal fill-ins for orthogonality.
  --    For each e in E (e : A → B) and m in M (m : C → D), adjoin
  --    d : B → C — the unique diagonal making both triangles commute.
  let eMorphismDecls := fd.leftClass.filterMap fun eId =>
    t.morphisms.find? (fun g => g.id == eId)

  let mMorphismDecls := fd.rightClass.filterMap fun mId =>
    t.morphisms.find? (fun g => g.id == mId)

  let diagonals := eMorphismDecls.flatMap fun e =>
    mMorphismDecls.map fun m => (e, m)

  let diagonalMorphisms := diagonals.map fun (e, m) =>
    let diagName : Name := .nested (.pair e.id.name m.id.name) "diag"
    ({ id := { name := diagName, kind := .morphism }
       domain := e.codomain
       codomain := m.domain
       description := s!"Diagonal fill-in for ({e.id.name}, {m.id.name})" }
      : Generator1)

  -- 5. Orthogonality axioms (as schemas quantified over u, v):
  --    For any square with e on top, m on the right, u on the left, v on the bottom:
  --      upper triangle:  e ; d = u    (d ∘ e = u)
  --      lower triangle:  d ; m = v    (m ∘ d = v)
  let upperAxioms := diagonals.map fun (e, m) =>
    let pairName : Name := .pair e.id.name m.id.name
    let diagId : GeneratorId := { name := .nested pairName "diag", kind := .morphism }
    ({ id := { name := .nested pairName "ortho_upper", kind := .twoCell }
       quantifiers := [
         { name := "u", kind := .morphism }
       ]
       leftPath := .comp (.atom e.id) (.atom diagId)
       rightPath := .var "u"
       description := s!"Upper triangle: d ∘ e = u for ({e.id.name}, {m.id.name})" }
      : Generator2)

  let lowerAxioms := diagonals.map fun (e, m) =>
    let pairName : Name := .pair e.id.name m.id.name
    let diagId : GeneratorId := { name := .nested pairName "diag", kind := .morphism }
    ({ id := { name := .nested pairName "ortho_lower", kind := .twoCell }
       quantifiers := [
         { name := "v", kind := .morphism }
       ]
       leftPath := .comp (.atom diagId) (.atom m.id)
       rightPath := .var "v"
       description := s!"Lower triangle: m ∘ d = v for ({e.id.name}, {m.id.name})" }
      : Generator2)

  { t with
    name := s!"Fact({t.name})"
    objects := t.objects ++ imageObjects
    morphisms := t.morphisms ++ eMorphisms ++ mMorphisms ++ diagonalMorphisms
    axioms := t.axioms ++ factorizationAxioms ++ upperAxioms ++ lowerAxioms }

end CatLab
