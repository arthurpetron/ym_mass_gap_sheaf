/-
# The Gibbs-refresh cross is the existing connected physical remainder

The concrete coarse Gibbs refresh and the production physical kernel push
the same actual fine Gibbs mass.  Their signed four-cell discrepancy is
therefore not a new analytic quantity: after the common raw normalization is
removed, it is exactly the centered cylinder remainder already isolated for
the two selected coarse face events.

Precisely,

  refreshCross - physicalKernelCross
    = Z_f^2 * centeredCylinderRemainder.

The centered remainder is also the signed expectation of the established
pointwise-unit-bounded three-cylinder observable.  Hence a quadratic bound
for that one observable, or conservatively for the full physical remainder
`L1`, compiles directly to the aggregate raw-column calibration.

No quadratic estimate is manufactured here.  In particular, the generic
`remainderL1 <= 2` bound is not a refining-scale estimate.  All-cutoff and
volume-uniform persistence, the continuum measure, OS/GNS reconstruction,
the Hamiltonian gap, and the Yang--Mills mass gap remain open.

Constructive contract: exact finite rational algebra and positive-factor
cancellation only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering
import YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross

namespace YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverAssignmentSaturatedScaleDefect
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering
open YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

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

private theorem covarianceNormalization_regroup_local
    (coarse fine value : Q') :
    value *
        ((coarse * (coarse * coarse)) *
          (fine * (fine * fine))) ≈
      (coarse * fine) *
        (((coarse * coarse) * (fine * fine)) * value) := by
  ring_qeqv

private theorem abs_mul_nonnegative_left_eqv_local
    (factor value : Q') (hfactor : (0 : Q') ≤ factor) :
    Q'.abs (factor * value) ≈ factor * Q'.abs value := by
  refine Q'.eqv_trans _ (Q'.abs (value * factor)) _
    (Q'.abs_eqv_congr (Q'.mul_comm_eqv factor value)) ?_
  refine Q'.eqv_trans _ (Q'.abs value * factor) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right value hfactor) ?_
  exact Q'.mul_comm_eqv (Q'.abs value) factor

/-! ## 1. Cancel the raw covariance normalization -/

/-- The assignment-saturated raw-column scale defect is the actual coarse
and fine partition-square product times the existing centered cylinder
remainder. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_partitionSquares_mul_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget ≈
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (S.fine.physicalPartition * S.fine.physicalPartition)) *
        centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let coarseZ := S.coarse.physicalPartition
  let fineZ := S.fine.physicalPartition
  let scaleDefect :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let rawCross :=
    connectedCovarianceRawCrossDefect K M
  let centered := centeredCylinderRemainder K M
  let squareProduct := (coarseZ * coarseZ) * (fineZ * fineZ)
  let denominator := connectedCovarianceRawCrossDenominator S
  have hcoarse : (0 : Q') < coarseZ := by
    simpa only [coarseZ] using
      (slabParametricKPhysicalPartition_pos
        S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent)
  have hfine : (0 : Q') < fineZ := by
    simpa only [fineZ] using
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hraw : rawCross ≈ (coarseZ * fineZ) * scaleDefect := by
    refine Q'.eqv_trans _
      (physicalConnectedCovarianceRawCrossDefect
        S hfineCutoff hcoarseCoupling M) _ ?_ ?_
    · exact
        (connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
          S hfineCutoff hcoarseCoupling M)
    refine Q'.eqv_trans _
      ((coarseZ * fineZ) *
        actualPositiveExpandedAssignmentSaturatedScaleDefectCross
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget) _ ?_ ?_
    · simpa only [coarseZ, fineZ] using
        (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedAssignmentSaturatedScaleDefect
          S hfineCutoff hcoarseCoupling M)
    · exact Q'.mul_eqv_congr_left (coarseZ * fineZ) _ _
        (by
          simpa only [scaleDefect] using
            (actualPositiveExpandedAssignmentSaturatedScaleDefectCross_eqv_rawColumn
              S hfineCutoff hcoarseCoupling
              M.coarseRoot M.coarseTarget))
  have hdenominator : (0 : Q') < denominator := by
    simp only [denominator, connectedCovarianceRawCrossDenominator,
      rawCovarianceDenominator]
    exact Q'.mul_pos
      (Q'.mul_pos hcoarse (Q'.mul_pos hcoarse hcoarse))
      (Q'.mul_pos hfine (Q'.mul_pos hfine hfine))
  have hcentered :
      centered ≈ Q'.divPos rawCross denominator hdenominator := by
    exact centeredCylinderRemainder_eqv_covarianceRawCross_divPos K M
  have hscaled :
      (coarseZ * fineZ) * scaleDefect ≈
        (coarseZ * fineZ) * (squareProduct * centered) := by
    refine Q'.eqv_trans _ rawCross _ (Q'.eqv_symm hraw) ?_
    refine Q'.eqv_trans _
      (Q'.divPos rawCross denominator hdenominator * denominator) _
      (Q'.eqv_symm
        (Q'.divPos_mul_eqv rawCross denominator hdenominator)) ?_
    refine Q'.eqv_trans _ (centered * denominator) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ denominator
        (Q'.eqv_symm hcentered)
    · simpa only [denominator, connectedCovarianceRawCrossDenominator,
        rawCovarianceDenominator, squareProduct] using
        (covarianceNormalization_regroup_local coarseZ fineZ centered)
  exact Q'.mul_left_cancel_of_pos (Q'.mul_pos hcoarse hfine) hscaled

/-- The refresh-versus-production signed four-cell cross is exactly the
actual fine partition square times the centered cylinder remainder. -/
theorem coarseGibbsRefreshCross_sub_physicalKernelCross_eqv_finePartitionSquare_mul_centeredRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    coarseGibbsRefreshPushedRawFourCellCross
          S M.coarseRoot M.coarseTarget -
        pushedFaceRawFourCellCross
          (physicalKernel S hfineCutoff hcoarseCoupling)
          M.coarseRoot M.coarseTarget ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
        centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare := S.fine.physicalPartition * S.fine.physicalPartition
  let difference :=
    coarseGibbsRefreshPushedRawFourCellCross
          S M.coarseRoot M.coarseTarget -
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M.coarseRoot M.coarseTarget
  let scaleDefect :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let centered :=
    centeredCylinderRemainder
      (physicalKernel S hfineCutoff hcoarseCoupling) M
  have hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  have hrefresh : scaleDefect ≈ coarseSquare * difference := by
    simpa only [scaleDefect, coarseSquare, difference] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_refresh_sub_physicalKernel
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget)
  have hcentered : scaleDefect ≈ (coarseSquare * fineSquare) * centered := by
    simpa only [scaleDefect, coarseSquare, fineSquare, centered] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_partitionSquares_mul_centeredRemainder
        S hfineCutoff hcoarseCoupling M)
  apply Q'.mul_left_cancel_of_pos
    (Q'.mul_pos hcoarse hcoarse)
  refine Q'.eqv_trans _ scaleDefect _ (Q'.eqv_symm hrefresh) ?_
  refine Q'.eqv_trans _ ((coarseSquare * fineSquare) * centered) _
    hcentered ?_
  exact Q'.mul_assoc_eqv coarseSquare fineSquare centered

/-! ## 2. The one-observable and `L1` producers -/

/-- The same raw cross is `Z_f^2` times the signed remainder expectation of
the established pointwise-unit-bounded connected observable. -/
theorem coarseGibbsRefreshCross_sub_physicalKernelCross_eqv_finePartitionSquare_mul_connectedRemainderExpectation
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    coarseGibbsRefreshPushedRawFourCellCross
          S M.coarseRoot M.coarseTarget -
        pushedFaceRawFourCellCross
          (physicalKernel S hfineCutoff hcoarseCoupling)
          M.coarseRoot M.coarseTarget ≈
      (S.fine.physicalPartition * S.fine.physicalPartition) *
        remainderObservableExpectation
          (physicalKernel S hfineCutoff hcoarseCoupling)
          (connectedRemainderObservable
            (physicalKernel S hfineCutoff hcoarseCoupling) M) := by
  refine Q'.eqv_trans _
    ((S.fine.physicalPartition * S.fine.physicalPartition) *
      centeredCylinderRemainder
        (physicalKernel S hfineCutoff hcoarseCoupling) M) _ ?_ ?_
  · exact
      coarseGibbsRefreshCross_sub_physicalKernelCross_eqv_finePartitionSquare_mul_centeredRemainder
        S hfineCutoff hcoarseCoupling M
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (connectedRemainderExpectation_eqv_centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M))

/-- Cancellation-aware quadratic input for the concrete Gibbs-refresh
branch. -/
def CoarseGibbsRefreshConnectedRemainderCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (centeredCylinderRemainder
        (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
    kernelCeiling * (g * g)

/-- A quadratic estimate on the centered remainder inhabits the sole
Gibbs-refresh signed-cross input. -/
theorem coarseGibbsRefreshPhysicalKernelCrossCalibration_of_connectedRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hcentered :
      CoarseGibbsRefreshConnectedRemainderCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    CoarseGibbsRefreshPhysicalKernelCrossCalibration
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
        g kernelCeiling := by
  let fineSquare := S.fine.physicalPartition * S.fine.physicalPartition
  let difference :=
    coarseGibbsRefreshPushedRawFourCellCross
          S M.coarseRoot M.coarseTarget -
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M.coarseRoot M.coarseTarget
  let centered := centeredCylinderRemainder
    (physicalKernel S hfineCutoff hcoarseCoupling) M
  have heq : difference ≈ fineSquare * centered := by
    simpa only [difference, fineSquare, centered] using
      (coarseGibbsRefreshCross_sub_physicalKernelCross_eqv_finePartitionSquare_mul_centeredRemainder
        S hfineCutoff hcoarseCoupling M)
  have hfineSquare0 : (0 : Q') ≤ fineSquare := by
    unfold fineSquare
    exact Q'.mul_nonneg _ _
      (Q'.le_of_lt
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))
      (Q'.le_of_lt
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))
  have habs : Q'.abs difference ≤ fineSquare * Q'.abs centered := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr heq))
      (Q'.le_trans' _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le fineSquare centered) ?_)
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ (Q'.abs centered)
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hfineSquare0))
  have hscaled :
      fineSquare * Q'.abs centered ≤
        fineSquare * (kernelCeiling * (g * g)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ fineSquare
      (by
        simpa only [CoarseGibbsRefreshConnectedRemainderCalibration,
          centered] using hcentered)
      hfineSquare0
  refine Q'.le_trans' _ _ _ habs
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv ?_))
  simp only [fineSquare]
  ring_qeqv

/-- A direct centered-remainder calibration compiles all the way to the
existing aggregate raw-column consumer. -/
theorem positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefreshConnectedRemainder
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hcentered :
      CoarseGibbsRefreshConnectedRemainderCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling) :
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
        (kernelCeiling * (g * g)) := by
  exact positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefresh
    S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
    g kernelCeiling
    (coarseGibbsRefreshPhysicalKernelCrossCalibration_of_connectedRemainder
      S hfineCutoff hcoarseCoupling M g kernelCeiling hcentered)

/-- The aggregate raw-column calibration is not stronger on this branch:
the exact positive partition factor cancels back to the selected centered
remainder with no coefficient loss. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_rawColumnCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hraw :
      PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          (kernelCeiling * (g * g))) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  let factor :=
    (S.coarse.physicalPartition * S.coarse.physicalPartition) *
      (S.fine.physicalPartition * S.fine.physicalPartition)
  let raw := positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
    S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
  let centered := centeredCylinderRemainder
    (physicalKernel S hfineCutoff hcoarseCoupling) M
  have hcoarse := slabParametricKPhysicalPartition_pos
    S.coarse.coupling_nonnegative S.coarse.cutoff S.coarse.extent
  have hfine := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  have hfactorPos : (0 : Q') < factor := by
    simpa only [factor] using
      (Q'.mul_pos (Q'.mul_pos hcoarse hcoarse)
        (Q'.mul_pos hfine hfine))
  have hrawEq : raw ≈ factor * centered := by
    simpa only [raw, factor, centered] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_partitionSquares_mul_centeredRemainder
        S hfineCutoff hcoarseCoupling M)
  have habsEq : Q'.abs raw ≈ factor * Q'.abs centered := by
    refine Q'.eqv_trans _ (Q'.abs (factor * centered)) _
      (Q'.abs_eqv_congr hrawEq) ?_
    exact abs_mul_nonnegative_left_eqv_local factor centered
      (Q'.le_of_lt hfactorPos)
  have hrawBound :
      Q'.abs raw ≤ (kernelCeiling * (g * g)) * factor := by
    simpa only [PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration,
      raw, factor] using hraw
  have hscaled :
      factor * Q'.abs centered ≤
        factor * (kernelCeiling * (g * g)) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm habsEq))
      (Q'.le_trans' _ _ _ hrawBound
        (Q'.le_of_eqv
          (Q'.mul_comm_eqv (kernelCeiling * (g * g)) factor)))
  unfold CoarseGibbsRefreshConnectedRemainderCalibration
  simpa only [centered] using
    (Q'.le_of_mul_le_mul_left hscaled hfactorPos)

/-- Exact equivalence of the preferred normalized connected calibration and
the formerly exposed aggregate raw-column calibration. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_iff_rawColumnCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q') :
    CoarseGibbsRefreshConnectedRemainderCalibration
        S hfineCutoff hcoarseCoupling M g kernelCeiling ↔
      PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          (kernelCeiling * (g * g)) := by
  constructor
  · exact
      positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefreshConnectedRemainder
        S hfineCutoff hcoarseCoupling M g kernelCeiling
  · exact
      coarseGibbsRefreshConnectedRemainderCalibration_of_rawColumnCross
        S hfineCutoff hcoarseCoupling M g kernelCeiling

/-- The earlier coupling-one reference residual and localized selected-cell
Casimir moment route therefore supplies the preferred centered calibration
itself.  Both analytic premises remain explicit and uninhabited. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_fineUnitReference_and_localizedMoment
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (M : SlabFaceBlockMap S)
    (referenceCeiling momentCeiling : Q')
    (hreference :
      FineUnitCouplingReferenceRawColumnScaleDefectCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          g referenceCeiling)
    (hmoment :
      FineUnitCouplingLocalizedFourCellCasimirMomentBound
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          momentCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g
        (referenceCeiling + Q'.ofNat 2 * momentCeiling) := by
  apply coarseGibbsRefreshConnectedRemainderCalibration_of_rawColumnCross
  exact positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_reference_and_moment
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one
    family law g hg hgle hcoupling M.coarseRoot M.coarseTarget
    referenceCeiling momentCeiling hreference hmoment

/-- Cancellation-preserving alternative to the global coupling-one split.
The unit-reference blocking residual is normalized by the unit partition,
while the cross loss and partition drift remain together in one signed raw
numerator until after cancellation. -/
theorem coarseGibbsRefreshConnectedRemainderCalibration_of_unitNormalizedResidual_and_centeredChange
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g referenceCeiling changeCeiling : Q')
    (hreference :
      FineUnitCouplingNormalizedBlockingResidualCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M g referenceCeiling)
    (hchange :
      FineUnitCouplingCenteredNormalizedChangeRawCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M g changeCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g
        (referenceCeiling + changeCeiling) := by
  unfold CoarseGibbsRefreshConnectedRemainderCalibration
  exact
    centeredCylinderRemainder_abs_le_of_unitNormalizedResidual_and_centeredChange
      (physicalKernel S hfineCutoff hcoarseCoupling)
      M g referenceCeiling changeCeiling hreference hchange

/-- Conservative alternative input: a quadratic bound on the full physical
pushforward remainder `L1`. -/
def CoarseGibbsRefreshPhysicalRemainderL1Calibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (g kernelCeiling : Q') : Prop :=
  (physicalKernel S hfineCutoff hcoarseCoupling).remainderL1 ≤
    kernelCeiling * (g * g)

theorem coarseGibbsRefreshConnectedRemainderCalibration_of_physicalRemainderL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hremainder :
      CoarseGibbsRefreshPhysicalRemainderL1Calibration
        S hfineCutoff hcoarseCoupling g kernelCeiling) :
    CoarseGibbsRefreshConnectedRemainderCalibration
      S hfineCutoff hcoarseCoupling M g kernelCeiling := by
  exact Q'.le_trans' _ _ _
    (centeredCylinderRemainder_abs_le_remainderL1
      (physicalKernel S hfineCutoff hcoarseCoupling) M)
    (by
      simpa only [CoarseGibbsRefreshPhysicalRemainderL1Calibration] using
        hremainder)

/-- The conservative `L1` route also reaches the aggregate raw-column
calibration, but does not preserve the selected-cylinder cancellation in its
analytic premise. -/
theorem positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefreshPhysicalRemainderL1
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (g kernelCeiling : Q')
    (hremainder :
      CoarseGibbsRefreshPhysicalRemainderL1Calibration
        S hfineCutoff hcoarseCoupling g kernelCeiling) :
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
        (kernelCeiling * (g * g)) := by
  exact
    positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefreshConnectedRemainder
      S hfineCutoff hcoarseCoupling M g kernelCeiling
      (coarseGibbsRefreshConnectedRemainderCalibration_of_physicalRemainderL1
        S hfineCutoff hcoarseCoupling M g kernelCeiling hremainder)

#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_partitionSquares_mul_centeredRemainder
#print axioms coarseGibbsRefreshCross_sub_physicalKernelCross_eqv_finePartitionSquare_mul_centeredRemainder
#print axioms coarseGibbsRefreshCross_sub_physicalKernelCross_eqv_finePartitionSquare_mul_connectedRemainderExpectation
#print axioms CoarseGibbsRefreshConnectedRemainderCalibration
#print axioms coarseGibbsRefreshPhysicalKernelCrossCalibration_of_connectedRemainder
#print axioms positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefreshConnectedRemainder
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_rawColumnCross
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_iff_rawColumnCross
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_fineUnitReference_and_localizedMoment
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_unitNormalizedResidual_and_centeredChange
#print axioms CoarseGibbsRefreshPhysicalRemainderL1Calibration
#print axioms coarseGibbsRefreshConnectedRemainderCalibration_of_physicalRemainderL1
#print axioms positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_gibbsRefreshPhysicalRemainderL1

end YMGap.Continuum.Z4DyadicSpinFourGibbsRefreshConnectedRemainder
