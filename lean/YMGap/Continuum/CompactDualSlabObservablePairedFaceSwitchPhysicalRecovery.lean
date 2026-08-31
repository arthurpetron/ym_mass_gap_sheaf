/-
# Physical recovery for the paired-face switch at a fixed mask

The complete face-switch decoder mixes two logically separate questions:

1. do two sources producing one final target use the same strand-component
   mask; and
2. once the mask is fixed, what source data does the output recover?

This module closes the physical half of the second question.  Equality of
the two final target pairs gives equality of both face-swapped physical
fields.  If the two source masks are equal, applying the same pointwise
transposition again recovers both original physical labellings exactly.

No auxiliary-assignment recovery or mask-recovery theorem is asserted.
Those are now the only data-level parts of the face-switch decoder left open.

Constructive contract: function equality and the literal Boolean face-swap
involution only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder

namespace YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchPhysicalRecovery

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchDecoder
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Equal final switched pairs and equal source strand masks recover both
source physical labellings. -/
theorem slabObservablePairedFaceSwitchable_sourcePhysical_eq_of_targetPair_eq_of_mask_eq
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (first second : SlabObservablePairedFaceSwitchablePair
      D rootFaceId targetFaceId)
    (htargetPair : slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget first =
      slabObservablePairedFaceSwitchableTargetPair
        D rootFaceId targetFaceId htarget second)
    (hmask : slabObservableTwoReplicaPairPairedFaceSwapMask
        D first.pair targetFaceId =
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D second.pair targetFaceId) :
    first.pair.1.1.1 = second.pair.1.1.1 ∧
      first.pair.2.1.1 = second.pair.2.1.1 := by
  let firstMask := slabObservableTwoReplicaPairPairedFaceSwapMask
    D first.pair targetFaceId
  let secondMask := slabObservableTwoReplicaPairPairedFaceSwapMask
    D second.pair targetFaceId
  have hleftTarget :
      twoReplicaFaceSwapLeft firstMask
          first.pair.1.1.1 first.pair.2.1.1 =
        twoReplicaFaceSwapLeft secondMask
          second.pair.1.1.1 second.pair.2.1.1 := by
    calc
      twoReplicaFaceSwapLeft firstMask
          first.pair.1.1.1 first.pair.2.1.1 =
          (slabObservablePairedFaceSwitchableTargetPair
            D rootFaceId targetFaceId htarget first).1.1.1 := by
        exact (slabObservablePairedFaceSwitchableLeftEntry_physical
          D rootFaceId targetFaceId htarget first).symm
      _ = (slabObservablePairedFaceSwitchableTargetPair
            D rootFaceId targetFaceId htarget second).1.1.1 :=
        congrArg (fun pair => pair.1.1.1) htargetPair
      _ = twoReplicaFaceSwapLeft secondMask
          second.pair.1.1.1 second.pair.2.1.1 :=
        slabObservablePairedFaceSwitchableLeftEntry_physical
          D rootFaceId targetFaceId htarget second
  have hrightTarget :
      twoReplicaFaceSwapRight firstMask
          first.pair.1.1.1 first.pair.2.1.1 =
        twoReplicaFaceSwapRight secondMask
          second.pair.1.1.1 second.pair.2.1.1 := by
    calc
      twoReplicaFaceSwapRight firstMask
          first.pair.1.1.1 first.pair.2.1.1 =
          (slabObservablePairedFaceSwitchableTargetPair
            D rootFaceId targetFaceId htarget first).2.1.1 := by
        exact (slabObservablePairedFaceSwitchableRightEntry_physical
          D rootFaceId targetFaceId htarget first).symm
      _ = (slabObservablePairedFaceSwitchableTargetPair
            D rootFaceId targetFaceId htarget second).2.1.1 :=
        congrArg (fun pair => pair.2.1.1) htargetPair
      _ = twoReplicaFaceSwapRight secondMask
          second.pair.1.1.1 second.pair.2.1.1 :=
        slabObservablePairedFaceSwitchableRightEntry_physical
          D rootFaceId targetFaceId htarget second
  have hmaskNamed : firstMask = secondMask := hmask
  constructor
  · calc
      first.pair.1.1.1 =
          twoReplicaFaceSwapLeft firstMask
            (twoReplicaFaceSwapLeft firstMask
              first.pair.1.1.1 first.pair.2.1.1)
            (twoReplicaFaceSwapRight firstMask
              first.pair.1.1.1 first.pair.2.1.1) :=
        (twoReplicaFaceSwapLeft_involutive firstMask
          first.pair.1.1.1 first.pair.2.1.1).symm
      _ = twoReplicaFaceSwapLeft firstMask
            (twoReplicaFaceSwapLeft secondMask
              second.pair.1.1.1 second.pair.2.1.1)
            (twoReplicaFaceSwapRight secondMask
              second.pair.1.1.1 second.pair.2.1.1) := by
        rw [hleftTarget, hrightTarget]
      _ = twoReplicaFaceSwapLeft secondMask
            (twoReplicaFaceSwapLeft secondMask
              second.pair.1.1.1 second.pair.2.1.1)
            (twoReplicaFaceSwapRight secondMask
              second.pair.1.1.1 second.pair.2.1.1) := by
        rw [hmaskNamed]
      _ = second.pair.1.1.1 :=
        twoReplicaFaceSwapLeft_involutive secondMask
          second.pair.1.1.1 second.pair.2.1.1
  · calc
      first.pair.2.1.1 =
          twoReplicaFaceSwapRight firstMask
            (twoReplicaFaceSwapLeft firstMask
              first.pair.1.1.1 first.pair.2.1.1)
            (twoReplicaFaceSwapRight firstMask
              first.pair.1.1.1 first.pair.2.1.1) :=
        (twoReplicaFaceSwapRight_involutive firstMask
          first.pair.1.1.1 first.pair.2.1.1).symm
      _ = twoReplicaFaceSwapRight firstMask
            (twoReplicaFaceSwapLeft secondMask
              second.pair.1.1.1 second.pair.2.1.1)
            (twoReplicaFaceSwapRight secondMask
              second.pair.1.1.1 second.pair.2.1.1) := by
        rw [hleftTarget, hrightTarget]
      _ = twoReplicaFaceSwapRight secondMask
            (twoReplicaFaceSwapLeft secondMask
              second.pair.1.1.1 second.pair.2.1.1)
            (twoReplicaFaceSwapRight secondMask
              second.pair.1.1.1 second.pair.2.1.1) := by
        rw [hmaskNamed]
      _ = second.pair.2.1.1 :=
        twoReplicaFaceSwapRight_involutive secondMask
          second.pair.1.1.1 second.pair.2.1.1

end YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchPhysicalRecovery

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedFaceSwitchPhysicalRecovery.slabObservablePairedFaceSwitchable_sourcePhysical_eq_of_targetPair_eq_of_mask_eq
