/-
# An accepted connected source for the aligned diagonal cut

The two diagonal unit-cube surfaces are connected through their displayed
common pivot edge.  Package that geometric path data in the generic binary
support compiler.  At coupling one, cutoff one, and half-width two, the
compiler constructively returns accepted global fusion assignments for the
twelve-face support and the vacuum and packages their literal `11 x 00`
pair as a connected strand source.

Constructive contract: an explicit bridge edge and the reusable
Sigma-witness compiler; no choice, `Classical`, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchCutCarrier
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

/-! ## 1. One explicit bridge between the two cube boundaries -/

def alignedDiagonalNearBridgeFace : Z4Plaq :=
  axisShiftPlaquette zeroAxisOffset (cubeFace .topXY)

def alignedDiagonalFarBridgeFace : Z4Plaq :=
  axisShiftPlaquette alignedDiagonalYZOffset (cubeFace .bottomXY)

theorem alignedDiagonalNearBridgeFace_mem :
    alignedDiagonalNearBridgeFace ∈ alignedDiagonalNearSurface := by
  decide

theorem alignedDiagonalFarBridgeFace_mem :
    alignedDiagonalFarBridgeFace ∈ alignedDiagonalFarSurface := by
  decide

def alignedDiagonalBridgeAdjacent :
    z4Chain.toLattice.Adjacent
      alignedDiagonalNearBridgeFace alignedDiagonalFarBridgeFace :=
  ⟨alignedDiagonalYZPivot, by decide, by decide⟩

def alignedDiagonalYZSurface_connected :
    PolymerModel.connectedIn
      (L := z4Chain.toLattice) alignedDiagonalYZSurface :=
  connectedIn_append_of_bridge
    (axisCubeSurface_connected zeroAxisOffset)
    (axisCubeSurface_connected alignedDiagonalYZOffset)
    alignedDiagonalNearBridgeFace_mem alignedDiagonalFarBridgeFace_mem
    alignedDiagonalBridgeAdjacent

/-! ## 2. Instantiate the generic connected-source compiler -/

def alignedDiagonalBinaryConnectedCarrier :
    SlabBinarySupportConnectedCarrier where
  support := alignedDiagonalYZSurface
  rootPlaquette := alignedDiagonalNearQueryFace
  targetPlaquette := alignedDiagonalFarQueryFace
  support_subset_slab_five :=
    alignedDiagonalSwitchSurface_subset_slab_five
  support_nodup := alignedDiagonalYZSurface_nodup
  support_even := alignedDiagonalYZSurface_evenFaceIncidence
  root_mem := List.mem_append.mpr
    (Or.inl alignedDiagonalNearQueryFace_mem)
  target_mem := List.mem_append.mpr
    (Or.inr alignedDiagonalFarQueryFace_mem)
  support_connected := alignedDiagonalYZSurface_connected

abbrev alignedDiagonalSwitchPhysicalData :=
  binarySupportConnectedPhysicalData

abbrev alignedDiagonalSwitchRootFaceId : Nat :=
  alignedDiagonalBinaryConnectedCarrier.rootFaceId

abbrev alignedDiagonalSwitchTargetFaceId : Nat :=
  alignedDiagonalBinaryConnectedCarrier.targetFaceId

abbrev alignedDiagonalSwitchLeftFineWitness :=
  alignedDiagonalBinaryConnectedCarrier.leftFineWitness

abbrev alignedDiagonalSwitchRightFineWitness :=
  alignedDiagonalBinaryConnectedCarrier.rightFineWitness

abbrev alignedDiagonalSwitchSourcePair :=
  alignedDiagonalBinaryConnectedCarrier.sourcePair

@[simp] theorem alignedDiagonalCarrier_leftPhysical :
    alignedDiagonalBinaryConnectedCarrier.leftPhysical =
      alignedDiagonalSwitchLeftPhysical := rfl

@[simp] theorem alignedDiagonalCarrier_rightPhysical :
    alignedDiagonalBinaryConnectedCarrier.rightPhysical =
      alignedDiagonalSwitchRightPhysical := rfl

theorem alignedDiagonalSwitchRootFaceId_physical :
    alignedDiagonalSwitchRootFaceId ∈ slabPhysicalFaceEdges 5 :=
  alignedDiagonalBinaryConnectedCarrier.rootFaceId_physical

theorem alignedDiagonalSwitchTargetFaceId_physical :
    alignedDiagonalSwitchTargetFaceId ∈ slabPhysicalFaceEdges 5 :=
  alignedDiagonalBinaryConnectedCarrier.targetFaceId_physical

theorem alignedDiagonalSwitchSourcePair_mem_fourCell :
    alignedDiagonalSwitchSourcePair ∈
      slabObservableFourCellSourcePairs alignedDiagonalSwitchPhysicalData
        alignedDiagonalSwitchRootFaceId alignedDiagonalSwitchTargetFaceId :=
  alignedDiagonalBinaryConnectedCarrier.sourcePair_mem_fourCell

theorem alignedDiagonalSwitchSourcePair_connected :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      alignedDiagonalSwitchPhysicalData alignedDiagonalSwitchRootFaceId
      alignedDiagonalSwitchTargetFaceId alignedDiagonalSwitchSourcePair =
        true :=
  alignedDiagonalBinaryConnectedCarrier.sourcePair_connected

def alignedDiagonalSwitchConnectedStrandSource :=
  alignedDiagonalBinaryConnectedCarrier.connectedStrandSource

#print axioms alignedDiagonalBridgeAdjacent
#print axioms alignedDiagonalYZSurface_connected
#print axioms alignedDiagonalBinaryConnectedCarrier
#print axioms alignedDiagonalSwitchLeftFineWitness
#print axioms alignedDiagonalSwitchRightFineWitness
#print axioms alignedDiagonalSwitchSourcePair_mem_fourCell
#print axioms alignedDiagonalSwitchSourcePair_connected
#print axioms alignedDiagonalSwitchConnectedStrandSource

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabConnectedSource
