/-
# A strict two-step four-cell bound from global paired-support decay

The global paired-support estimate has rate

  (25/9) * (16/25)^(distance+1).

At lattice separation at least two this is at most

  (25/9) * (16/25)^3 = 4096/5625 < 1.

This module contracts that numerical fact with the exact fractional
four-cell reduction.  It yields both an unnormalized determinant inequality
and a normalized one-sided four-cell excess bound.  The result is still a
fixed-anchor finite-slab theorem.  It is not yet an identification with a
same-object Osterwalder--Schrader transfer form.

Constructive contract: exact rational order, finite sums, and positive
division only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

/-! ## 1. The earned strict scalar -/

/-- The explicit strict rate left after summing every paid peel mass at
separation at least two. -/
def slabObservablePairedSupportTwoStepRate : Q' :=
  Q'.mkPos 4096 5625 (by decide)

theorem slabObservablePairedSupportTwoStepRate_lt_one :
    slabObservablePairedSupportTwoStepRate < (1 : Q') := by
  decide

/-- The full global envelope contracts strictly once the two selected faces
have lattice distance at least two. -/
theorem slabObservablePairedSupportGlobalAnchorRate_le_twoStepRate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (hseparated : 2 ≤
      linfDist
        (slabPlaquetteAt D.extent rootFaceId)
        (slabPlaquetteAt D.extent targetFaceId)) :
    slabObservablePairedSupportGlobalAnchorRate
        D rootFaceId targetFaceId ≤
      slabObservablePairedSupportTwoStepRate := by
  unfold slabObservablePairedSupportGlobalAnchorRate
  have hexponent : 3 ≤
      linfDist
        (slabPlaquetteAt D.extent rootFaceId)
        (slabPlaquetteAt D.extent targetFaceId) + 1 := by
    omega
  have hpower := pow_base_antitone
    (r := slabObservablePairedGlobalEntropyAnchorRatio)
    (by decide)
    (Q'.le_of_lt
      slabObservablePairedGlobalEntropyAnchorRatio_lt_one)
    hexponent
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 25 9 (by decide)) hpower (by decide)
  exact Q'.le_trans' _ _ _ hscaled (by decide)

/-! ## 2. Unnormalized and normalized four-cell contraction -/

/-- At separation at least two, the source determinant cell is no larger
than the opposite cell plus the strict rate times the exact two-replica
partition. -/
theorem slabObservableFourCell_defect_le_twoStepRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (hseparated : 2 ≤
      linfDist
        (slabPlaquetteAt (centralExtent half) rootFaceId)
        (slabPlaquetteAt (centralExtent half) targetFaceId)) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) ≤
      listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetComplementEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetEntries
              D rootFaceId targetFaceId) +
        slabObservablePairedSupportTwoStepRate *
          (D.physicalPartition * D.physicalPartition) := by
  let D := anchorSlabPhysicalData cutoff half
  have hfour := slabObservableFourCell_defect_le_pairedSupportConnected
    cutoff half rootFaceId targetFaceId htarget
  have hconnected :=
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare
      cutoff half rootFaceId targetFaceId htarget
  have hrate :=
    slabObservablePairedSupportGlobalAnchorRate_le_twoStepRate
      D rootFaceId targetFaceId hseparated
  have hpartitionNonnegative :
      (0 : Q') ≤ D.physicalPartition * D.physicalPartition :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
      (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
  have hrateScaled := Q'.mul_le_mul_of_nonneg_right _ _
    (D.physicalPartition * D.physicalPartition)
    hrate hpartitionNonnegative
  exact Q'.le_trans' _ _ _ hfour
    (Q'.add_le_add (Q'.le_refl' _)
      (Q'.le_trans' _ _ _ hconnected hrateScaled))

/-- The signed four-cell determinant divided by the exact square partition.
This is the algebraic Boolean covariance numerator, but no OS observable or
time-translation identification is asserted here. -/
def slabObservableNormalizedFourCellExcess
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  Q'.divPos
    (listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) +
      -(listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetComplementEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetEntries
              D rootFaceId targetFaceId)))
    (D.physicalPartition * D.physicalPartition)
    (YMGap.Continuum.HKPos.q_mul_pos
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

/-- **Strict normalized two-step four-cell bound.**  The one-sided normalized
determinant excess is bounded by `4096/5625 < 1`, uniformly in the finite
cutoff and slab extent at the fixed production coupling. -/
theorem slabObservableNormalizedFourCellExcess_le_twoStepRate
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (centralExtent half))
    (hseparated : 2 ≤
      linfDist
        (slabPlaquetteAt (centralExtent half) rootFaceId)
        (slabPlaquetteAt (centralExtent half) targetFaceId)) :
    slabObservableNormalizedFourCellExcess
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetFaceId ≤
      slabObservablePairedSupportTwoStepRate := by
  unfold slabObservableNormalizedFourCellExcess
  apply Q'.divPos_le_of_le_mul
  exact Q'.sub_le_of_le_add
    (slabObservableFourCell_defect_le_twoStepRate
      cutoff half rootFaceId targetFaceId htarget hseparated)

#print axioms slabObservablePairedSupportTwoStepRate
#print axioms slabObservablePairedSupportTwoStepRate_lt_one
#print axioms slabObservablePairedSupportGlobalAnchorRate_le_twoStepRate
#print axioms slabObservableFourCell_defect_le_twoStepRate
#print axioms slabObservableNormalizedFourCellExcess
#print axioms slabObservableNormalizedFourCellExcess_le_twoStepRate

end YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
