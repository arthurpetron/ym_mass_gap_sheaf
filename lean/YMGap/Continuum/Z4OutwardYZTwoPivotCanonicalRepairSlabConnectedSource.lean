/-
# Accepted connected source on the two-pivot outward Y/Z repair surface

The reusable binary-support compiler turns the explicit closed connected
surface into an accepted cutoff-one, coupling-one `11 x 00` source with the
same outward Y/Z marked plaquettes as the obstructed one-pivot sector.

This is only a production source.  Its two exceptional local carriers must
still be selected and proved component-preserving before it becomes a good
repair receiver.

Constructive contract: the explicit carrier and Sigma-valued positive-witness
compiler only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4OutwardYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

def outwardYZCanonicalRepairBinaryConnectedCarrier :
    SlabBinarySupportConnectedCarrier where
  support := outwardYZCanonicalRepairSwitchSurface
  rootPlaquette := outwardYQueryFace
  targetPlaquette := outwardZQueryFace
  support_subset_slab_five :=
    outwardYZCanonicalRepairSwitchSurface_subset_slab_five
  support_nodup := outwardYZCanonicalRepairSwitchSurface_nodup
  support_even := outwardYZCanonicalRepairSwitchSurface_evenFaceIncidence
  root_mem := List.mem_append.mpr
    (Or.inr outwardYZCanonicalRepairRoot_mem_rootLobe)
  target_mem := List.mem_append.mpr
    (Or.inl outwardYZCanonicalRepairTarget_mem_targetLobe)
  support_connected := outwardYZCanonicalRepairSurface_connected

abbrev outwardYZCanonicalRepairPhysicalData :=
  binarySupportConnectedPhysicalData

abbrev outwardYZCanonicalRepairRootFaceId : Nat :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.rootFaceId

abbrev outwardYZCanonicalRepairTargetFaceId : Nat :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.targetFaceId

abbrev outwardYZCanonicalRepairLeftFineWitness :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.leftFineWitness

abbrev outwardYZCanonicalRepairRightFineWitness :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.rightFineWitness

abbrev outwardYZCanonicalRepairSourcePair :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.sourcePair

@[simp] theorem outwardYZCanonicalRepairCarrier_leftPhysical :
    outwardYZCanonicalRepairBinaryConnectedCarrier.leftPhysical =
      slabBinarySupportLabelling 5
        outwardYZCanonicalRepairSwitchSurface := by
  rfl

@[simp] theorem outwardYZCanonicalRepairCarrier_rightPhysical :
    outwardYZCanonicalRepairBinaryConnectedCarrier.rightPhysical =
      slabBinarySupportLabelling 5 [] := by
  rfl

theorem outwardYZCanonicalRepairRootFaceId_physical :
    outwardYZCanonicalRepairRootFaceId ∈ slabPhysicalFaceEdges 5 :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.rootFaceId_physical

theorem outwardYZCanonicalRepairTargetFaceId_physical :
    outwardYZCanonicalRepairTargetFaceId ∈ slabPhysicalFaceEdges 5 :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.targetFaceId_physical

theorem outwardYZCanonicalRepairSourcePair_mem_fourCell :
    outwardYZCanonicalRepairSourcePair ∈
      slabObservableFourCellSourcePairs
        outwardYZCanonicalRepairPhysicalData
        outwardYZCanonicalRepairRootFaceId
        outwardYZCanonicalRepairTargetFaceId :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.sourcePair_mem_fourCell

theorem outwardYZCanonicalRepairSourcePair_connected :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      outwardYZCanonicalRepairPhysicalData
      outwardYZCanonicalRepairRootFaceId
      outwardYZCanonicalRepairTargetFaceId
      outwardYZCanonicalRepairSourcePair = true :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.sourcePair_connected

def outwardYZCanonicalRepairConnectedStrandSource :=
  outwardYZCanonicalRepairBinaryConnectedCarrier.connectedStrandSource

#print axioms outwardYZCanonicalRepairBinaryConnectedCarrier
#print axioms outwardYZCanonicalRepairLeftFineWitness
#print axioms outwardYZCanonicalRepairRightFineWitness
#print axioms outwardYZCanonicalRepairSourcePair_mem_fourCell
#print axioms outwardYZCanonicalRepairConnectedStrandSource

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabConnectedSource
