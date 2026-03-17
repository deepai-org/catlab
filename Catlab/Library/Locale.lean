/-
  CatLab -- Locales (Pointless Topology / Frames)

  Derived as: macneilleCompletion(TheoryOfLattices)

  The MacNeille completion of a lattice freely adjoins all meets and joins,
  giving a complete lattice.  A complete lattice satisfying the frame
  distributivity law  a ∧ ⋁S = ⋁{a ∧ s | s ∈ S}  is a frame; the opposite
  category of the category of frames is the category of locales.

  The MacNeille completion of a distributive lattice (our Lattice theory,
  which already has distributivity) yields a complete distributive lattice =
  frame, so this derivation is faithful.

  Point-free topology: locales generalise topological spaces.  Every sober
  topological space has an associated locale (its frame of opens), and every
  locale arises this way iff it is "spatial".
-/

import Catlab.Core.Theory
import Catlab.Operators.MacNeille
import Catlab.Library.Lattice

namespace CatLab.Library

/-- The theory of locales (frames), derived as the MacNeille completion of the
    theory of lattices.  The completion freely adds all meets and joins to the
    lattice, giving a complete distributive lattice = frame. -/
def TheoryOfLocale : Theory :=
  { macneilleCompletion TheoryOfLattices with
    name     := "Locale"
    doctrine := { doctrine := .Locale } }

end CatLab.Library
