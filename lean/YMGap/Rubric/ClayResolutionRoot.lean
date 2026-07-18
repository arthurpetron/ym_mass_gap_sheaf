/-
Clay-resolution classification scaffold and corrected functional-root export.

The first version of this module incorrectly treated the ordinary state GNS
space as the physical OS Hilbert space.  The repository's constructive
`PositiveIsometricTimeNoGo` theorem shows why that cannot work: invariant
Euclidean time is isometric on `E(a* b)`, and positivity/self-adjointness then
collapse the proposed physical transfer to the identity.

The corrected physical prerequisite is now
`YMGap.Continuum.CanonicalOSRoot.PositiveTimeOSRoot`, which uses the ordinary
Wilson form only as an ambient Euclidean space and pins the physical datum only
to the reflected positive-time form.  This rubric module retains only the
narrow Cartan-classification pin.  A Cartan type is not a global compact gauge
group; the eventual Clay target must add a global-form and faithful-action pin
before attaching this classification datum to a Wilson lattice family.
-/

import YMGap.MassGap.AllSimpleTypes
import YMGap.Continuum.CanonicalOSRoot

namespace YMGap.Rubric.ClayResolutionRoot

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.RG
open YMGap.MassGap.AllSimpleTypes
open YMGap.Continuum.CanonicalOSRoot

/-! ## Compact-simple Lie-type classification pin -/

/-- A compact-simple Cartan type together with the exact representative datum
used by the existing all-simple-types reduction.

The equality `repPinned` forbids replacing the selected Cartan type by an
unrelated convenient `RepData`.  This is only Lie-type classification data,
not a specification of the global compact group or its faithful lattice action. -/
structure PinnedSimpleLieType (T : CartanType) : Type where
  simpleRank : IsSimpleRank T
  rep : RepData
  repPinned : rep = repDataOf T
  admissible : AdmissibleSimpleGroup rep

/-- The classification data already proved in `AllSimpleTypes` gives the
canonical pin for every genuine-simple Cartan type. -/
def pinnedSimpleLieType (T : CartanType) (hT : IsSimpleRank T) :
    PinnedSimpleLieType T where
  simpleRank := hT
  rep := repDataOf T
  repPinned := rfl
  admissible := admissible_of_cartanType T hT

end YMGap.Rubric.ClayResolutionRoot

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Rubric.ClayResolutionRoot.pinnedSimpleLieType
