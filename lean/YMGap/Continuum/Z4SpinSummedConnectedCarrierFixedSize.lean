/-
# Fixed-size spin-summed connected-carrier summation

At a fixed union-support size the canonical carrier encoding is unchanged.
Its color coordinate receives the decorated face envelope, while its two
background coordinates receive the exact target-box spin-summed family
activities.  The background sum is therefore the product of the full target
partition and the literal embedded target partition.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
import YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight
import YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

namespace YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4SpinSummedColoredSupportWeight
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

local infix:50 " ≈ " => Q'.eqv

def spinSummedConnectedCarrierTargetWeight
    (cutoff n size : Nat) (carrier : ConnectedCarrier) : Q' :=
  anchorDecoratedFaceEnvelope ^ size *
    (parametricKSupportFamilyActivity cutoff n carrier.2.1 *
      parametricKSupportFamilyActivity cutoff n carrier.2.2)

def spinSummedConnectedSourceSizeSum
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (size : Nat) : Q' :=
  listQSum (fun entry : ConnectedSourceEntry root hsmall =>
      spinSummedSourcePairWeight cutoff entry.val)
    (connectedSourceEntriesAtSize hsmall size)

theorem spinSummedConnectedSourceSizeSum_le_carrierTarget
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) {rootFace size : Nat}
    (hrootFace : rootFace ∈ root) :
    spinSummedConnectedSourceSizeSum cutoff (root := root) hsmall size ≤
      listQSum (spinSummedConnectedCarrierTargetWeight cutoff n size)
        (connectedCarrierTargetList small n rootFace size) := by
  unfold spinSummedConnectedSourceSizeSum
  apply listQSum_le_of_injective
    (connectedSourceEntriesAtSize hsmall size)
    (connectedCarrierTargetList small n rootFace size)
    (fun entry : ConnectedSourceEntry root hsmall =>
      spinSummedSourcePairWeight cutoff entry.val)
    (spinSummedConnectedCarrierTargetWeight cutoff n size)
    (connectedCarrier hsmall)
    (connectedSourceEntriesAtSize_nodup hsmall size)
  · intro entry hentry
    have hsize : (connectedCarrierSupport hsmall entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact connectedCarrier_mem_target hsmall entry hrootFace hsize
  · intro first _ second _ heq
    exact connectedCarrier_injective hsmall first second heq
  · intro entry hentry
    have hsize : (connectedCarrierSupport hsmall entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    have hbound :=
      spinSummedConnectedSourcePairWeight_le_support_background
        cutoff hsmall entry
    rw [hsize] at hbound
    simpa [spinSummedConnectedCarrierTargetWeight, connectedCarrier,
      spinSummedConnectedBackgroundPairWeight] using hbound
  · intro carrier _
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedFaceEnvelope
        anchorDecoratedFaceEnvelope_nonnegative size)
      (Q'.mul_nonneg _ _
        (parametricKSupportFamilyActivity_nonnegative
          cutoff n carrier.2.1)
        (parametricKSupportFamilyActivity_nonnegative
          cutoff n carrier.2.2))

theorem spinSummedConnectedCarrierTargetSum_eqv
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (rootFace size : Nat) :
    listQSum (spinSummedConnectedCarrierTargetWeight cutoff n size)
        (connectedCarrierTargetList small n rootFace size) ≈
      spinSummedColoredPinnedSizeWeightSum n rootFace size *
        (parametricKCompatibleSupportGasPartition cutoff n *
          parametricKEmbeddedTargetPartition cutoff small n) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorDecoratedFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      parametricKSupportFamilyActivity cutoff n background.1 *
        parametricKSupportFamilyActivity cutoff n background.2)
    (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies n)
      (embeddedCompatibleFamilies small n))
  have hinner := listQSum_cartesian_product
    (parametricKSupportFamilyActivity cutoff n)
    (parametricKSupportFamilyActivity cutoff n)
    (canonicalCompatibleAmbientFamilies n)
    (embeddedCompatibleFamilies small n)
  have hembedded := listQSum_perm
    (parametricKSupportFamilyActivity cutoff n)
    (embeddedCompatibleFamilies_perm_target hsmall)
  unfold connectedCarrierTargetList spinSummedConnectedCarrierTargetWeight
    spinSummedColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ hinner ?_
  unfold parametricKCompatibleSupportGasPartition
    parametricKEmbeddedTargetPartition
  exact Q'.mul_eqv_congr_left _ _ _ hembedded

theorem spinSummedConnectedSourceSizeSum_le_geom_partition
    (cutoff : Nat) {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) {rootFace size : Nat}
    (hrootFace : rootFace ∈ root) :
    spinSummedConnectedSourceSizeSum cutoff (root := root) hsmall size ≤
      anchorDecoratedEffectiveRatio ^ size *
        (parametricKCompatibleSupportGasPartition cutoff n *
          parametricKEmbeddedTargetPartition cutoff small n) := by
  have htarget := spinSummedConnectedSourceSizeSum_le_carrierTarget
    cutoff hsmall hrootFace (size := size)
  have hfactor := spinSummedConnectedCarrierTargetSum_eqv
    cutoff hsmall rootFace size
  have hpartition0 : (0 : Q') ≤
      parametricKCompatibleSupportGasPartition cutoff n *
        parametricKEmbeddedTargetPartition cutoff small n :=
    Q'.mul_nonneg _ _
      (parametricKCompatibleSupportGasPartition_nonnegative cutoff n)
      (parametricKEmbeddedTargetPartition_nonnegative cutoff small n)
  have hcolored := Q'.mul_le_mul_of_nonneg_right _ _ _
    (spinSummedColoredPinnedSizeWeightSum_le_geom n rootFace size)
    hpartition0
  exact Q'.le_trans' _ _ _ htarget
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hcolored)

end YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize.spinSummedConnectedSourceSizeSum_le_carrierTarget
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize.spinSummedConnectedCarrierTargetSum_eqv
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize.spinSummedConnectedSourceSizeSum_le_geom_partition
