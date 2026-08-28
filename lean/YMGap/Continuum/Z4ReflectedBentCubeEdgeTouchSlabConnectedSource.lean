/-
# An accepted connected source for the reflected bent-cube cut

Feed the closed connected reflected carrier to the reusable binary-support
compiler.  At coupling one, cutoff one, and half-width two, positivity of the
finite physical terms constructively supplies accepted global fusion
assignments for the sixteen-face support and for the vacuum.  Their literal
`11 x 00` pair is an accepted connected strand source.

The numerical marked target is also proved to be the exact half-time
reflection of the numerical root, so every later recoupling construction is
already typed at the same-object OS face pair.

Constructive contract: the explicit reflected carrier and the reusable
Sigma-witness compiler only; no choice, `Classical`, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier

def reflectedBentBinaryConnectedCarrier :
    SlabBinarySupportConnectedCarrier where
  support := reflectedBentSwitchSurface
  rootPlaquette := reflectedBentRootPlaquette
  targetPlaquette := reflectedBentTargetPlaquette
  support_subset_slab_five :=
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_subset_slab_five
  support_nodup :=
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_nodup
  support_even :=
    YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_evenFaceIncidence
  root_mem := List.mem_append.mpr
    (Or.inl reflectedBentRoot_mem)
  target_mem := List.mem_append.mpr
    (Or.inr reflectedBentTarget_mem)
  support_connected := reflectedBentSwitchSurface_connected

abbrev reflectedBentPhysicalData :=
  binarySupportConnectedPhysicalData

abbrev reflectedBentRootFaceId : Nat :=
  reflectedBentBinaryConnectedCarrier.rootFaceId

abbrev reflectedBentTargetFaceId : Nat :=
  reflectedBentBinaryConnectedCarrier.targetFaceId

abbrev reflectedBentLeftFineWitness :=
  reflectedBentBinaryConnectedCarrier.leftFineWitness

abbrev reflectedBentRightFineWitness :=
  reflectedBentBinaryConnectedCarrier.rightFineWitness

abbrev reflectedBentSourcePair :=
  reflectedBentBinaryConnectedCarrier.sourcePair

@[simp] theorem reflectedBentCarrier_leftPhysical :
    reflectedBentBinaryConnectedCarrier.leftPhysical =
      slabBinarySupportLabelling 5 reflectedBentSwitchSurface := by
  rfl

@[simp] theorem reflectedBentCarrier_rightPhysical :
    reflectedBentBinaryConnectedCarrier.rightPhysical =
      slabBinarySupportLabelling 5 [] := by
  rfl

theorem reflectedBentRootFaceId_physical :
    reflectedBentRootFaceId ∈ slabPhysicalFaceEdges 5 :=
  reflectedBentBinaryConnectedCarrier.rootFaceId_physical

theorem reflectedBentTargetFaceId_physical :
    reflectedBentTargetFaceId ∈ slabPhysicalFaceEdges 5 :=
  reflectedBentBinaryConnectedCarrier.targetFaceId_physical

theorem reflectedBentTargetFaceId_eq_reflect :
    reflectedBentTargetFaceId =
      slabFaceReflectId reflectedBentPhysicalData.extent
        reflectedBentRootFaceId := by
  decide

theorem reflectedBentRootFaceId_lower :
    reflectedBentRootFaceId ∈
      centralLowerFaceIds reflectedBentPhysicalData.half := by
  decide

theorem reflectedBentSourcePair_mem_fourCell :
    reflectedBentSourcePair ∈
      slabObservableFourCellSourcePairs reflectedBentPhysicalData
        reflectedBentRootFaceId reflectedBentTargetFaceId :=
  reflectedBentBinaryConnectedCarrier.sourcePair_mem_fourCell

theorem reflectedBentSourcePair_connected :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      reflectedBentPhysicalData reflectedBentRootFaceId
      reflectedBentTargetFaceId reflectedBentSourcePair = true :=
  reflectedBentBinaryConnectedCarrier.sourcePair_connected

def reflectedBentConnectedStrandSource :=
  reflectedBentBinaryConnectedCarrier.connectedStrandSource

#print axioms reflectedBentBinaryConnectedCarrier
#print axioms reflectedBentTargetFaceId_eq_reflect
#print axioms reflectedBentRootFaceId_lower
#print axioms reflectedBentLeftFineWitness
#print axioms reflectedBentRightFineWitness
#print axioms reflectedBentConnectedStrandSource

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
