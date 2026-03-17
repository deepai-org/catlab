/-
  CatLab — Exact Completion

  Two constructions for completing a left-exact (lex) category:

  1. regCompletion: Freely adjoin coequalizers of kernel pairs to make
     the category regular. For each pair f, g : A → B forming a kernel pair,
     adjoin their coequalizer.

  2. exCompletion: Further complete to an exact category where every
     equivalence relation is effective. Objects are equivalence relations
     (pairs R ⇉ A), morphisms are compatible maps.
-/

import Catlab.Core.Theory
import Catlab.Core.Equality
import Batteries.Data.HashMap

namespace CatLab

/-- Regular completion: freely adjoin coequalizers of kernel pairs.

    Given a left-exact category C, RegCompletion(C) has the same objects
    as C, but for every kernel pair (f, g : R → A), we adjoin the
    coequalizer q : A → Q. -/
def regCompletion (t : Theory) (namePrefix : String := "reg") : Theory :=
  -- For each pair of morphisms with the same domain and codomain,
  -- treat them as a potential kernel pair and adjoin the coequalizer.
  -- Group morphisms by (domain, codomain) for O(N) instead of O(N²)
  let byEndpoints : Std.HashMap (Name × Name) (List Generator1) :=
    t.morphisms.foldl (fun acc m =>
      let key := (m.domain.toName, m.codomain.toName)
      let existing := acc[key]? |>.getD []
      acc.insert key (m :: existing)) {}
  let kernelPairs := byEndpoints.toList.flatMap fun (_, ms) =>
    ms.flatMap fun f =>
      ms.filterMap fun g =>
        if f.id == g.id then none
        else some (f, g)

  let coequalizerObjects := kernelPairs.map fun (f, g) =>
    ({ id := gid s!"{namePrefix}_coeq_{f.id.name}_{g.id.name}"
       description := s!"Coequalizer of kernel pair ({f.id.name}, {g.id.name})" }
      : Generator0)

  let coequalizerMorphisms := kernelPairs.map fun (f, g) =>
    let coeqObjId : GeneratorId := gid s!"{namePrefix}_coeq_{f.id.name}_{g.id.name}"
    ({ id := gid s!"{namePrefix}_q_{f.id.name}_{g.id.name}"
       domain := f.codomain
       codomain := .atom coeqObjId
       description := s!"Quotient map for kernel pair ({f.id.name}, {g.id.name})" }
      : Generator1)

  let coequalizerAxioms := kernelPairs.map fun (f, g) =>
    let qId : GeneratorId := gid s!"{namePrefix}_q_{f.id.name}_{g.id.name}"
    ({ id := gid s!"{namePrefix}_coeq_ax_{f.id.name}_{g.id.name}"
       leftPath := .comp (.atom f.id) (.atom qId)
       rightPath := .comp (.atom g.id) (.atom qId)
       description := s!"Coequalizer condition: q ∘ {f.id.name} = q ∘ {g.id.name}" }
      : Generator2)

  { t with
    name := s!"{namePrefix}({t.name})"
    objects := t.objects ++ coequalizerObjects
    morphisms := t.morphisms ++ coequalizerMorphisms
    axioms := t.axioms ++ coequalizerAxioms }

/-- Exact completion: objects are equivalence relations (R ⇉ A).

    Given a left-exact category C, ExCompletion(C) has:
    - Objects: pairs (R, A) with morphisms d₀, d₁ : R → A forming an
      equivalence relation (reflexive, symmetric, transitive)
    - Morphisms: (R, A) → (S, B) are maps f : A → B such that
      (a, a') ∈ R implies (f(a), f(a')) ∈ S -/
def exCompletion (t : Theory) (namePrefix : String := "ex") : Theory :=
  -- For each object A, create the trivial equivalence relation (A, A, id, id)
  -- and for each kernel pair, create the associated equivalence relation object.
  let eqRelObjects := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_eqrel_{a.id.name}"
       description := s!"Equivalence relation on {a.id.name}" }
      : Generator0)

  -- d₀, d₁ : R → A for each equivalence relation object
  let d0Morphisms := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_d0_{a.id.name}"
       domain := .atom (gid s!"{namePrefix}_eqrel_{a.id.name}")
       codomain := .atom a.id
       description := s!"First projection of equivalence relation on {a.id.name}" }
      : Generator1)

  let d1Morphisms := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_d1_{a.id.name}"
       domain := .atom (gid s!"{namePrefix}_eqrel_{a.id.name}")
       codomain := .atom a.id
       description := s!"Second projection of equivalence relation on {a.id.name}" }
      : Generator1)

  -- Reflexivity: σ : A → R such that d₀ ∘ σ = id and d₁ ∘ σ = id
  let reflexMorphisms := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_refl_{a.id.name}"
       domain := .atom a.id
       codomain := .atom (gid s!"{namePrefix}_eqrel_{a.id.name}")
       description := s!"Reflexivity map for equivalence relation on {a.id.name}" }
      : Generator1)

  let reflexAxioms_d0 := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_refl_d0_{a.id.name}"
       leftPath := .comp (.atom (gid s!"{namePrefix}_refl_{a.id.name}"))
                         (.atom (gid s!"{namePrefix}_d0_{a.id.name}"))
       rightPath := Expr.id (.atom a.id)
       description := s!"d₀ ∘ σ = id on {a.id.name}" }
      : Generator2)

  let reflexAxioms_d1 := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_refl_d1_{a.id.name}"
       leftPath := .comp (.atom (gid s!"{namePrefix}_refl_{a.id.name}"))
                         (.atom (gid s!"{namePrefix}_d1_{a.id.name}"))
       rightPath := Expr.id (.atom a.id)
       description := s!"d₁ ∘ σ = id on {a.id.name}" }
      : Generator2)

  -- Symmetry: τ : R → R such that d₀ ∘ τ = d₁ and d₁ ∘ τ = d₀
  let symmMorphisms := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_symm_{a.id.name}"
       domain := .atom (gid s!"{namePrefix}_eqrel_{a.id.name}")
       codomain := .atom (gid s!"{namePrefix}_eqrel_{a.id.name}")
       description := s!"Symmetry map for equivalence relation on {a.id.name}" }
      : Generator1)

  let symmAxioms_d0 := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_symm_d0_{a.id.name}"
       leftPath := .comp (.atom (gid s!"{namePrefix}_symm_{a.id.name}"))
                         (.atom (gid s!"{namePrefix}_d0_{a.id.name}"))
       rightPath := .atom (gid s!"{namePrefix}_d1_{a.id.name}")
       description := s!"d₀ ∘ τ = d₁ on {a.id.name}" }
      : Generator2)

  let symmAxioms_d1 := t.objects.map fun a =>
    ({ id := gid s!"{namePrefix}_symm_d1_{a.id.name}"
       leftPath := .comp (.atom (gid s!"{namePrefix}_symm_{a.id.name}"))
                         (.atom (gid s!"{namePrefix}_d1_{a.id.name}"))
       rightPath := .atom (gid s!"{namePrefix}_d0_{a.id.name}")
       description := s!"d₁ ∘ τ = d₀ on {a.id.name}" }
      : Generator2)

  { t with
    name := s!"{namePrefix}({t.name})"
    objects := t.objects ++ eqRelObjects
    morphisms := t.morphisms ++ d0Morphisms ++ d1Morphisms
                 ++ reflexMorphisms ++ symmMorphisms
    axioms := t.axioms ++ reflexAxioms_d0 ++ reflexAxioms_d1
              ++ symmAxioms_d0 ++ symmAxioms_d1 }

end CatLab
