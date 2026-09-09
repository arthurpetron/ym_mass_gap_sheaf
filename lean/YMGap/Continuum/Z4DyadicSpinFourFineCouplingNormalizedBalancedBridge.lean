/-
# Balanced raw defect to normalized centered-remainder bridge

The cancellation-preserving normalized recentering introduced a
unit-normalized blocking residual.  That residual is not a new analytic
quantity: for the literal physical kernel it is exactly the older balanced
coupling-one raw scale defect divided by the positive coarse/unit partition
square product.

Below fine coupling one, the actual fine partition is at most the
coupling-one partition.  Consequently the existing balanced raw calibration,
which is normalized by the smaller actual fine partition square, implies the
unit-normalized residual calibration with no loss in its constant.  Combining
this fact with the exact coupling-margin factorization gives one compiler from
the two honest raw inputs

  balanced blocking defect + signed centered margin quotient

to the preferred quadratic centered-remainder estimate.

Neither raw input is inhabited here.  In particular, this module proves no
volume-uniform estimate, all-cutoff persistence, continuum measure, OS/GNS
reconstruction, Hamiltonian gap, or Yang--Mills mass gap.

Constructive contract: exact rational algebra, positive-denominator division,
and finite partition monotonicity only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverFiberScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (h : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ h

private theorem abs_divPos_le_of_abs_le_mul_local
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hraw : Q'.abs numerator ≤ budget * denominator) :
    Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegRaw := Q'.neg_le_neg hraw
    have hnegAbs : -(Q'.abs numerator) ≤ numerator := by
      have h := Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegRaw hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self numerator) hraw

/-! ## 1. Exact normalized form of the balanced raw defect -/

/-- The normalized coarse covariance is its four-cell determinant divided by
the coarse partition square. -/
theorem normalizedSlabFaceBooleanCovariance_eqv_fourCell_divPos
    (D : SlabPhysicalData) (root target : Nat) :
    normalizedSlabFaceBooleanCovariance D root target ≈
      Q'.divPos
        (physicalFaceRawFourCellCross D root target)
        (D.physicalPartition * D.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)) := by
  let partition := D.physicalPartition
  let cross := physicalFaceRawFourCellCross D root target
  let cubic := coarseFaceRawCovarianceNumerator D root target
  have hpartition : (0 : Q') < partition := by
    simpa only [partition] using
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
  have hsquare : (0 : Q') < partition * partition :=
    Q'.mul_pos hpartition hpartition
  have hcube : (0 : Q') < partition * (partition * partition) :=
    Q'.mul_pos hpartition hsquare
  have hcubic : cubic ≈ cross * partition := by
    simpa only [cubic, cross] using
      (coarseFaceRawCovarianceNumerator_eqv_fourCell_mul_partition
        D root target)
  refine Q'.eqv_trans _
    (Q'.divPos cubic (partition * (partition * partition)) hcube) _ ?_ ?_
  · simpa only [cubic, partition, rawCovarianceDenominator] using
      (normalizedFaceCovariance_eqv_raw_divPos D root target)
  refine Q'.eqv_trans _
    (Q'.divPos cross (partition * partition) hsquare) _ ?_ ?_
  · apply divPos_eqv_of_eqv_mul_local hcube
    refine Q'.eqv_trans _ (cross * partition) _ hcubic ?_
    apply Q'.eqv_symm
    refine Q'.eqv_trans _
      ((Q'.divPos cross (partition * partition) hsquare *
          (partition * partition)) * partition) _ ?_ ?_
    · ring_qeqv
    · exact Q'.mul_eqv_congr_right _ _ partition
        (Q'.divPos_mul_eqv cross (partition * partition) hsquare)
  · exact Q'.eqv_refl _

/-- Positive denominator obtained from the coarse and coupling-one fine
partition squares. -/
def fineUnitCouplingBalancedRawColumnScaleDefectDenominator
    (S : SlabScalePair) : Q' :=
  (S.coarse.physicalPartition * S.coarse.physicalPartition) *
    (fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S)

theorem fineUnitCouplingBalancedRawColumnScaleDefectDenominator_pos
    (S : SlabScalePair) :
    (0 : Q') <
      fineUnitCouplingBalancedRawColumnScaleDefectDenominator S := by
  unfold fineUnitCouplingBalancedRawColumnScaleDefectDenominator
  exact Q'.mul_pos
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
    (Q'.mul_pos
      (fineUnitCouplingPhysicalPartition_pos S)
      (fineUnitCouplingPhysicalPartition_pos S))

/-- The unit-normalized blocking residual is exactly the balanced raw scale
defect divided by the positive coarse/unit partition-square product. -/
theorem normalizedCoarse_sub_fineUnitPushed_eqv_balanced_divPos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget -
        fineUnitCouplingPushedNormalizedRawColumnCross
          (physicalKernel S hfineCutoff hcoarseCoupling)
          M.coarseRoot M.coarseTarget ≈
      Q'.divPos
        (fineUnitCouplingBalancedRawColumnScaleDefect
          S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget)
        (fineUnitCouplingBalancedRawColumnScaleDefectDenominator S)
        (fineUnitCouplingBalancedRawColumnScaleDefectDenominator_pos S) := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let coarseCross :=
    coarseObservableFourCellRawColumnCross
      S M.coarseRoot M.coarseTarget
  let unitCross := fineUnitCouplingPushedRawColumnCross
    (physicalKernel S hfineCutoff hcoarseCoupling)
    M.coarseRoot M.coarseTarget
  have hcoarseSquare : (0 : Q') < coarseSquare :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
  have hunitSquare : (0 : Q') < unitSquare :=
    Q'.mul_pos
      (fineUnitCouplingPhysicalPartition_pos S)
      (fineUnitCouplingPhysicalPartition_pos S)
  have hdenominator : (0 : Q') < coarseSquare * unitSquare :=
    Q'.mul_pos hcoarseSquare hunitSquare
  have hreceiverCrossEq :
      physicalReceiverPairFourCellCross
          S.coarse M.coarseRoot M.coarseTarget =
        coarseObservableFourCellRawColumnCross
          S M.coarseRoot M.coarseTarget := rfl
  have hcross :
      physicalFaceRawFourCellCross
          S.coarse M.coarseRoot M.coarseTarget ≈
        coarseCross := by
    refine Q'.eqv_trans _
      (physicalReceiverPairFourCellCross
        S.coarse M.coarseRoot M.coarseTarget) _ ?_ ?_
    · exact physicalFaceRawFourCellCross_eqv_receiverPairCross
        S.coarse M.coarseRoot M.coarseTarget
    · rw [hreceiverCrossEq]
      exact Q'.eqv_refl _
  have hcoarse :
      normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget ≈
        Q'.divPos coarseCross coarseSquare hcoarseSquare := by
    refine Q'.eqv_trans _
      (Q'.divPos
        (physicalFaceRawFourCellCross
          S.coarse M.coarseRoot M.coarseTarget)
        coarseSquare hcoarseSquare) _ ?_ ?_
    · simpa only [coarseSquare] using
        (normalizedSlabFaceBooleanCovariance_eqv_fourCell_divPos
          S.coarse M.coarseRoot M.coarseTarget)
    · apply divPos_eqv_congr_numerator_local hcoarseSquare
      exact hcross
  refine Q'.eqv_trans _
    (Q'.divPos coarseCross coarseSquare hcoarseSquare -
      Q'.divPos unitCross unitSquare hunitSquare) _ ?_ ?_
  · exact sub_eqv_both_local hcoarse (by
      unfold fineUnitCouplingPushedNormalizedRawColumnCross
      simp only [unitCross, unitSquare]
      exact Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (Q'.divPos
      (coarseCross * unitSquare - unitCross * coarseSquare)
      (coarseSquare * unitSquare) hdenominator) _ ?_ ?_
  · exact divPos_sub_divPos_eq_crossDifference
      coarseCross unitCross coarseSquare unitSquare
        hcoarseSquare hunitSquare
  apply divPos_eqv_congr_numerator_local hdenominator
  refine Q'.eqv_trans _
    (unitSquare * coarseCross - coarseSquare * unitCross) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_comm_eqv coarseCross unitSquare)
      (Q'.mul_comm_eqv unitCross coarseSquare)
  · exact Q'.eqv_refl _

/-! ## 2. Calibration transport and the combined matched-AF compiler -/

/-- Below coupling one, the existing balanced raw calibration implies the
unit-normalized blocking-residual calibration with the same constant.  The
balanced premise uses the smaller actual fine partition square, so no
normalization loss is introduced. -/
theorem fineUnitCouplingNormalizedBlockingResidualCalibration_of_balanced
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S) (g balancedCeiling : Q')
    (hg : (0 : Q') ≤ g)
    (hbalancedCeiling : (0 : Q') ≤ balancedCeiling)
    (hbalanced :
      FineUnitCouplingBalancedRawColumnScaleDefectCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          g balancedCeiling) :
    FineUnitCouplingNormalizedBlockingResidualCalibration
      (physicalKernel S hfineCutoff hcoarseCoupling)
      M g balancedCeiling := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let budget := balancedCeiling * (g * g)
  let numerator := fineUnitCouplingBalancedRawColumnScaleDefect
    S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let denominator :=
    fineUnitCouplingBalancedRawColumnScaleDefectDenominator S
  have hactualPartition0 : (0 : Q') ≤ S.fine.physicalPartition :=
    Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hunitPartition0 :
      (0 : Q') ≤ fineUnitCouplingPhysicalPartition S :=
    Q'.le_of_lt (fineUnitCouplingPhysicalPartition_pos S)
  have hpartition :=
    finePhysicalPartition_le_unitCoupling S hfineCoupling_le_one
  have hsquare : actualSquare ≤ unitSquare := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _
        S.fine.physicalPartition hpartition hactualPartition0)
      (Q'.mul_le_mul_of_nonneg_left _ _
        (fineUnitCouplingPhysicalPartition S)
        hpartition hunitPartition0)
  have hcoarseSquare0 : (0 : Q') ≤ coarseSquare :=
    Q'.le_of_lt
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
        (slabParametricKPhysicalPartition_pos
          S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent))
  have hdenominatorOrder :
      coarseSquare * actualSquare ≤ coarseSquare * unitSquare :=
    Q'.mul_le_mul_of_nonneg_left _ _ coarseSquare
      hsquare hcoarseSquare0
  have hbudget0 : (0 : Q') ≤ budget :=
    Q'.mul_nonneg balancedCeiling (g * g)
      hbalancedCeiling (Q'.mul_nonneg g g hg hg)
  have hraw : Q'.abs numerator ≤ budget * denominator := by
    have hbase : Q'.abs numerator ≤
        budget * (coarseSquare * actualSquare) := by
      simpa only [numerator, budget, coarseSquare, actualSquare,
        FineUnitCouplingBalancedRawColumnScaleDefectCalibration] using
        hbalanced
    refine Q'.le_trans' _ _ _ hbase ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ budget
        hdenominatorOrder hbudget0) ?_
    unfold denominator
      fineUnitCouplingBalancedRawColumnScaleDefectDenominator
    simp only [coarseSquare, unitSquare]
    exact Q'.le_refl' _
  unfold FineUnitCouplingNormalizedBlockingResidualCalibration
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (normalizedCoarse_sub_fineUnitPushed_eqv_balanced_divPos
          S hfineCutoff hcoarseCoupling M))) ?_
  simpa only [numerator, denominator, budget] using
    (abs_divPos_le_of_abs_le_mul_local
      (fineUnitCouplingBalancedRawColumnScaleDefectDenominator_pos S)
      hraw)

/-- Final cancellation-aware compiler.  A balanced raw blocking calibration
and a signed margin-quotient ceiling imply the preferred centered-remainder
`O(g^2)` estimate with total constant
`balancedCeiling + 2 * marginCeiling`. -/
theorem centeredCylinderRemainder_abs_le_of_balanced_and_margin
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g balancedCeiling marginCeiling : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (hbalancedCeiling : (0 : Q') ≤ balancedCeiling)
    (hmarginCeiling : (0 : Q') ≤ marginCeiling)
    (hbalanced :
      FineUnitCouplingBalancedRawColumnScaleDefectCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          g balancedCeiling)
    (hmargin :
      FineUnitCouplingCenteredNormalizedMarginRawCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M marginCeiling) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (balancedCeiling + Q'.ofNat 2 * marginCeiling) * (g * g) := by
  have hreference :
      FineUnitCouplingNormalizedBlockingResidualCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M g balancedCeiling :=
    fineUnitCouplingNormalizedBlockingResidualCalibration_of_balanced
      S hfineCutoff hcoarseCoupling hfineCoupling_le_one M
      g balancedCeiling (Q'.le_of_lt hg) hbalancedCeiling hbalanced
  have hchange :
      FineUnitCouplingCenteredNormalizedChangeRawCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M g (Q'.ofNat 2 * marginCeiling) :=
    fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_margin
      (physicalKernel S hfineCutoff hcoarseCoupling)
      M family law g marginCeiling hg hgle hcoupling
      hmarginCeiling hmargin
  exact
    centeredCylinderRemainder_abs_le_of_unitNormalizedResidual_and_centeredChange
      (physicalKernel S hfineCutoff hcoarseCoupling)
      M g balancedCeiling (Q'.ofNat 2 * marginCeiling)
      hreference hchange

#print axioms normalizedSlabFaceBooleanCovariance_eqv_fourCell_divPos
#print axioms fineUnitCouplingBalancedRawColumnScaleDefectDenominator
#print axioms fineUnitCouplingBalancedRawColumnScaleDefectDenominator_pos
#print axioms normalizedCoarse_sub_fineUnitPushed_eqv_balanced_divPos
#print axioms fineUnitCouplingNormalizedBlockingResidualCalibration_of_balanced
#print axioms centeredCylinderRemainder_abs_le_of_balanced_and_margin

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge
