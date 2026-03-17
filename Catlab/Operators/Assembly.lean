/-
  CatLab — Category of Assemblies over a PCA

  Objects: sets with realizability relations (assemblies).
  Morphisms: tracked functions — functions between underlying sets
  that are tracked by a realizer in the PCA.

  This category sits between Set and the realizability topos:
  Set ← Asm(A) → RT(A)
-/

import Catlab.Core.Theory
import Catlab.Operators.Realizability

namespace CatLab

/-- Construct the category of assemblies over a PCA.

    Objects: assemblies (X, ⦃-⦄_X) — a set X with a realizability
    relation assigning to each x ∈ X a nonempty set of realizers in A.

    Morphisms: tracked functions f : (X, ⦃-⦄_X) → (Y, ⦃-⦄_Y) —
    a set-theoretic function f : X → Y together with a tracker e ∈ A
    such that for all x ∈ X, a ∈ ⦃x⦄_X implies e·a is defined and
    e·a ∈ ⦃f(x)⦄_Y.

    This is a regular category with all finite limits, and is the
    exact/regular completion of the partitioned assemblies. -/
def assemblyCategory (pca : PCA) : Theory :=
  -- Generic assembly objects
  let asmX : Generator0 :=
    { id := gid s!"Asm_X({pca.name})"
      description := s!"Generic assembly X over {pca.name}" }

  let asmY : Generator0 :=
    { id := gid s!"Asm_Y({pca.name})"
      description := s!"Generic assembly Y over {pca.name}" }

  let asmZ : Generator0 :=
    { id := gid s!"Asm_Z({pca.name})"
      description := s!"Generic assembly Z over {pca.name}" }

  -- Terminal assembly: one-element set, every element realized by K
  let terminalAsm : Generator0 :=
    { id := gid s!"1_Asm({pca.name})"
      description := "Terminal assembly: singleton realized by K" }

  -- The discrete assembly on A itself (the free assembly on the PCA carrier)
  let carrierAsm : Generator0 :=
    { id := gid s!"∇({pca.name})"
      description := s!"Discrete assembly on carrier of {pca.name}" }

  -- Tracked morphism f : X → Y
  let trackedF : Generator1 :=
    { id := gid s!"f_tracked" (k := .morphism)
      domain := .atom (gid s!"Asm_X({pca.name})")
      codomain := .atom (gid s!"Asm_Y({pca.name})")
      description := "Tracked function f : X → Y" }

  -- Tracked morphism g : Y → Z
  let trackedG : Generator1 :=
    { id := gid s!"g_tracked" (k := .morphism)
      domain := .atom (gid s!"Asm_Y({pca.name})")
      codomain := .atom (gid s!"Asm_Z({pca.name})")
      description := "Tracked function g : Y → Z" }

  -- Identity is tracked by the identity combinator SKK
  let idTracked : Generator1 :=
    { id := gid s!"id_tracked" (k := .morphism)
      domain := .atom (gid s!"Asm_X({pca.name})")
      codomain := .atom (gid s!"Asm_X({pca.name})")
      description := "Identity tracked by SKK" }

  -- Composition: if f tracked by e and g tracked by e', then g∘f tracked by S(K e')(e)
  let compTracked : Generator1 :=
    { id := gid s!"gf_tracked" (k := .morphism)
      domain := .atom (gid s!"Asm_X({pca.name})")
      codomain := .atom (gid s!"Asm_Z({pca.name})")
      description := "Composition g ∘ f, tracked by S(Ke')(e)" }

  -- Terminal morphism: unique map to terminal assembly
  let terminalMap : Generator1 :=
    { id := gid s!"!_Asm" (k := .morphism)
      domain := .atom (gid s!"Asm_X({pca.name})")
      codomain := .atom (gid s!"1_Asm({pca.name})")
      description := "Unique map to terminal assembly, tracked by K" }

  -- Axiom: composition is tracked
  let compAxiom : Generator2 :=
    { id := gid "comp_tracked_ax" (k := .twoCell)
      leftPath := .comp (.atom (gid s!"f_tracked" (k := .morphism)))
                        (.atom (gid s!"g_tracked" (k := .morphism)))
      rightPath := .atom (gid s!"gf_tracked" (k := .morphism))
      description := "Composition of tracked functions is tracked" }

  -- Axiom: identity is left unit
  let idLeftAxiom : Generator2 :=
    { id := gid "id_left_Asm" (k := .twoCell)
      leftPath := .comp (.atom (gid s!"id_tracked" (k := .morphism)))
                        (.atom (gid s!"f_tracked" (k := .morphism)))
      rightPath := .atom (gid s!"f_tracked" (k := .morphism))
      description := "Identity is left unit for tracked composition" }

  -- Axiom: identity is right unit
  let idRightAxiom : Generator2 :=
    { id := gid "id_right_Asm" (k := .twoCell)
      leftPath := .comp (.atom (gid s!"f_tracked" (k := .morphism)))
                        (.atom (gid s!"id_tracked" (k := .morphism)))
      rightPath := .atom (gid s!"f_tracked" (k := .morphism))
      description := "Identity is right unit for tracked composition" }

  -- Axiom: terminal map is unique
  let terminalAxiom : Generator2 :=
    { id := gid "terminal_unique_Asm" (k := .twoCell)
      leftPath := .atom (gid s!"!_Asm" (k := .morphism))
      rightPath := .atom (gid s!"!_Asm" (k := .morphism))
      description := "Terminal map is unique" }

  { name := s!"Asm({pca.name})"
    doctrine := { doctrine := .Category }
    objects := [asmX, asmY, asmZ, terminalAsm, carrierAsm]
    morphisms := [trackedF, trackedG, idTracked, compTracked, terminalMap]
    axioms := [compAxiom, idLeftAxiom, idRightAxiom, terminalAxiom] }

end CatLab
