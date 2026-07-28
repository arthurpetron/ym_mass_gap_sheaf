/-
# The three-sheet row is accepted by the binary multicover

The cutoff-two adjacent-cube row refutes decomposition into at most two
binary sheets.  It does not refute an arbitrary finite binary multicover:
the two cube boundaries and their symmetric difference are three closed
binary sheets whose pointwise sum is exactly the doubled ordinary union.

This module packages those three sheets as `BinaryEvenSlabLayer` values,
constructs the corrected multicover, and sends it all the way to an actual
member of the finite whole-slab joint-carrier enumeration.

## Axiom gate

Finite geometry and exact arithmetic only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
import YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction

namespace YMGap.Continuum.BF4SU2OuterBinaryMulticoverCounterexampleRepair

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4AdjacentCubeCancellationCarrier
open YMGap.Continuum.Z4AxisCubeSixFaceActivity
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4UnitCubeIncidenceParity

private theorem leftCube_subset :
    ∀ plaquette,
      plaquette ∈ axisCubeSurface zeroAxisOffset →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  apply zeroXAxisPlainUnionSurface_subset_slab_three plaquette
  unfold zeroXAxisPlainUnionSurface
  simp only [List.mem_eraseDups, List.mem_append]
  exact Or.inl hplaquette

private theorem rightCube_subset :
    ∀ plaquette,
      plaquette ∈ axisCubeSurface xAxisOffset →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  apply zeroXAxisPlainUnionSurface_subset_slab_three plaquette
  unfold zeroXAxisPlainUnionSurface
  simp only [List.mem_eraseDups, List.mem_append]
  exact Or.inr hplaquette

private theorem cancelledSurface_subset :
    ∀ plaquette,
      plaquette ∈ zeroXAxisCancelledSurface →
      plaquette ∈ boundaryCompleteSlabPlaquettes 3 := by
  intro plaquette hplaquette
  apply zeroXAxisPlainUnionSurface_subset_slab_three plaquette
  unfold zeroXAxisPlainUnionSurface
  simp only [List.mem_eraseDups, List.mem_append]
  exact List.mem_append.mp (List.mem_filter.mp hplaquette).1

def leftCubeLayer : BinaryEvenSlabLayer counterScalePair :=
  binaryEvenSlabLayerOfSupport counterScalePair
    (axisCubeSurface zeroAxisOffset)
    leftCube_subset
    (axisCubeSurface_nodup zeroAxisOffset)
    (axisShift_evenFaceIncidence
      zeroAxisOffset unitCubeSurface_evenFaceIncidence)

def rightCubeLayer : BinaryEvenSlabLayer counterScalePair :=
  binaryEvenSlabLayerOfSupport counterScalePair
    (axisCubeSurface xAxisOffset)
    rightCube_subset
    (axisCubeSurface_nodup xAxisOffset)
    (axisShift_evenFaceIncidence
      xAxisOffset unitCubeSurface_evenFaceIncidence)

def cancelledLayer : BinaryEvenSlabLayer counterScalePair :=
  binaryEvenSlabLayerOfSupport counterScalePair
    zeroXAxisCancelledSurface
    cancelledSurface_subset
    zeroXAxisCancelledSurface_nodup
    zeroXAxisCancelledSurface_evenFaceIncidence

theorem leftCubeLayer_state :
    leftCubeLayer.state = leftCubeIndicator := rfl

theorem rightCubeLayer_state :
    rightCubeLayer.state = rightCubeIndicator := rfl

theorem cancelledLayer_state :
    cancelledLayer.state = cancelledIndicator := rfl

theorem threeLayerStates_reconstruct :
    sumLayerStates [leftCubeLayer, rightCubeLayer, cancelledLayer] =
      plainUnionSpinTwoState := by
  funext id
  have hpoint :=
    congrFun threeSheetCarrier_eq_plainUnionSpinTwoState id
  simp only [sumLayerStates, leftCubeLayer_state,
    rightCubeLayer_state, cancelledLayer_state] at ⊢
  unfold addEdgeLabelling at hpoint ⊢
  unfold zeroEdgeLabelling at ⊢
  omega

/-- The positive cutoff-two row rejected by the old bounded decomposition
has a literal three-sheet multicover. -/
def plainUnionSpinTwoState_multicover :
    BinaryEvenSlabMulticover
      counterScalePair plainUnionSpinTwoState where
  layers := [leftCubeLayer, rightCubeLayer, cancelledLayer]
  reconstruct := threeLayerStates_reconstruct

/-- The repaired multicover constructs a semantic coherent row. -/
def plainUnionSpinTwoState_jointSelection :
    WholeSlabJointChannelSelection
      counterScalePair plainUnionSpinTwoState :=
  plainUnionSpinTwoState_multicover.toJointChannelSelection
    plainUnionSpinTwoState_mem (by decide)

/-- More strongly, it constructs an actual code retained by the executable
finite whole-slab carrier enumeration. -/
def plainUnionSpinTwoState_enumeratedCarrier :
    WholeSlabEnumeratedJointCarrier
      counterScalePair plainUnionSpinTwoState :=
  plainUnionSpinTwoState_multicover.toEnumeratedJointCarrier
    plainUnionSpinTwoState_mem (by decide)

theorem plainUnionSpinTwoState_jointCarrierCodes_length_pos :
    0 <
      (wholeSlabJointCarrierCodes
        counterScalePair plainUnionSpinTwoState).length :=
  plainUnionSpinTwoState_enumeratedCarrier.toNonempty.candidates_positive

#print axioms leftCubeLayer
#print axioms rightCubeLayer
#print axioms cancelledLayer
#print axioms leftCubeLayer_state
#print axioms rightCubeLayer_state
#print axioms cancelledLayer_state
#print axioms threeLayerStates_reconstruct
#print axioms plainUnionSpinTwoState_multicover
#print axioms plainUnionSpinTwoState_jointSelection
#print axioms plainUnionSpinTwoState_enumeratedCarrier
#print axioms plainUnionSpinTwoState_jointCarrierCodes_length_pos

end YMGap.Continuum.BF4SU2OuterBinaryMulticoverCounterexampleRepair
