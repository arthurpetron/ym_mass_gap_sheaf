/-
# A named subunit heat rate for the connected joint summand

The preceding exact factorization exposes two heat powers which pay the
connected contour: the cutoff-one fine source exponent and the SU(2)-specific
coarse excitation excess.  If both explicitly named lattice couplings lie
below one common rational rate `rate < 1`, base monotonicity combines these
powers at `rate`.  Exponent antitonicity and the physical activity floor then
give a geometric suppression factor per unit of plaquette separation.

The resulting distance fugacity is exactly `rate^3`, and its strict
subunit property is proved from the stated coupling window.  This file bounds
only the suppression factor.  The parity-ground reference weight, finite
entropy sum, row normalization, and volume uniformity remain separate.

Constructive contract: explicit rational inequalities and previously checked
finite-carrier witnesses only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
import YMGap.Continuum.FusedAmplitudeDerivation
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Combine the two physical heat powers under one named ceiling -/

/-- If the fine and coarse couplings are both at most `rate`, the complete
joint suppression is bounded by one `rate` power carrying the sum of the two
physical activity exponents. -/
theorem finePacketOrientedJointSuppressionFactor_le_commonRatePower
    (S : SlabScalePair) (rate : Q')
    (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketOrientedJointSuppressionFactor
        S orientation first second pair ≤
      qpow rate
        (3 * (fineCouplingPhysicalOccupiedFaceCount S first +
            fineCouplingPhysicalOccupiedFaceCount S second) +
          finePacketOrientedTotalTargetCasimirExcess
            S orientation first second pair) := by
  have hfinePower := qpow_mono_base
    S.fine.coupling_nonnegative hfineRate
      (3 * (fineCouplingPhysicalOccupiedFaceCount S first +
        fineCouplingPhysicalOccupiedFaceCount S second))
  have hcoarsePower := qpow_mono_base
    S.coarse.coupling_nonnegative hcoarseRate
      (finePacketOrientedTotalTargetCasimirExcess
        S orientation first second pair)
  have hrate0 : (0 : Q') ≤ rate := Q'.le_trans' _ _ _
    S.fine.coupling_nonnegative hfineRate
  unfold finePacketOrientedJointSuppressionFactor
  refine Q'.le_trans' _
    (qpow rate
        (3 * (fineCouplingPhysicalOccupiedFaceCount S first +
          fineCouplingPhysicalOccupiedFaceCount S second)) *
      qpow S.coarse.coupling
        (finePacketOrientedTotalTargetCasimirExcess
          S orientation first second pair)) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _ hfinePower
      (qpow_nonneg S.coarse.coupling S.coarse.coupling_nonnegative _)
  refine Q'.le_trans' _
    (qpow rate
        (3 * (fineCouplingPhysicalOccupiedFaceCount S first +
          fineCouplingPhysicalOccupiedFaceCount S second)) *
      qpow rate
        (finePacketOrientedTotalTargetCasimirExcess
          S orientation first second pair)) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hcoarsePower
      (qpow_nonneg rate hrate0 _)
  exact Q'.ge_of_eqv
    (HeatKernelRGStep.qpow_add rate
      (3 * (fineCouplingPhysicalOccupiedFaceCount S first +
        fineCouplingPhysicalOccupiedFaceCount S second))
      (finePacketOrientedTotalTargetCasimirExcess
        S orientation first second pair))

/-! ## 2. The explicit distance fugacity -/

def finePacketJointDistanceFugacity (rate : Q') : Q' :=
  qpow rate 3

theorem finePacketJointDistanceFugacity_lt_one
    {rate : Q'} (hrate0 : (0 : Q') ≤ rate)
    (hrate1 : rate < (1 : Q')) :
    finePacketJointDistanceFugacity rate < (1 : Q') := by
  unfold finePacketJointDistanceFugacity
  simpa only using
    (HeatKernelGap.qpow_succ_lt_one hrate0 hrate1 2)

/-- A connected oriented lowering path is suppressed by one explicit
`rate^3` factor for every plaquette in its distance-plus-one floor. -/
theorem finePacketOrientedConnectedPath_jointSuppression_le_distanceFugacity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (path : FinePacketObservableConnectedDisagreementPath
      S first.1 second.1 observableFaceId pair) :
    finePacketOrientedJointSuppressionFactor
        S orientation first.1 second.1 pair ≤
      qpow (finePacketJointDistanceFugacity rate)
        (linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) := by
  have hcombined :=
    finePacketOrientedJointSuppressionFactor_le_commonRatePower
      S rate hfineRate hcoarseRate orientation first.1 second.1 pair
  have hfloor := finePacketOrientedConnectedPath_scaledHeatActivity_floor
    S hfineCutoff orientation first second observableFaceId
      hobservableFace pair hlowering path
  have hrate0 : (0 : Q') ≤ rate := Q'.le_trans' _ _ _
    S.fine.coupling_nonnegative hfineRate
  have hrateLeOne : rate ≤ (1 : Q') := Q'.le_of_lt hrate1
  have hdistance := HeatKernelRGStep.qpow_antitone
    hrate0 hrateLeOne
    (3 * (linfDist
      (slabPlaquetteAt S.coarse.extent observableFaceId)
      (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1))
    (3 * (fineCouplingPhysicalOccupiedFaceCount S first.1 +
        fineCouplingPhysicalOccupiedFaceCount S second.1) +
      finePacketOrientedTotalTargetCasimirExcess
        S orientation first.1 second.1 pair)
    hfloor
  refine Q'.le_trans' _ _ _ hcombined
    (Q'.le_trans' _ _ _ hdistance ?_)
  exact Q'.ge_of_eqv
    (HeatKernelRGStep.qpow_qpow rate 3
      (linfDist
        (slabPlaquetteAt S.coarse.extent observableFaceId)
        (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1))

/-! ## 3. Attach the rate to every nonzero connected orientation -/

theorem finePacketForwardNonzeroConnectedPair_jointSuppression_le_distanceFugacity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketForwardLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    let path := finePacketFaceResponseConnectedActivePairPath
      S first.1 second.1 observableFaceId hobservableFace pair hpair
    finePacketOrientedJointSuppressionFactor
        S .forward first.1 second.1 pair ≤
      qpow (finePacketJointDistanceFugacity rate)
        (linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) := by
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  exact
    finePacketOrientedConnectedPath_jointSuppression_le_distanceFugacity
      S hfineCutoff rate hfineRate hcoarseRate hrate1 .forward
      first second observableFaceId hobservableFace pair hlowering
      (finePacketFaceResponseConnectedActivePairPath
        S first.1 second.1 observableFaceId hobservableFace pair hpair)

theorem finePacketReverseNonzeroConnectedPair_jointSuppression_le_distanceFugacity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketReverseLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    let path := finePacketFaceResponseConnectedActivePairPath
      S first.1 second.1 observableFaceId hobservableFace pair hpair
    finePacketOrientedJointSuppressionFactor
        S .reverse first.1 second.1 pair ≤
      qpow (finePacketJointDistanceFugacity rate)
        (linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) := by
  have hactive := (List.mem_filter.mp hpair).1
  have hphysical := (List.mem_filter.mp hactive).1
  have hlowering :=
    finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hphysical hne
  exact
    finePacketOrientedConnectedPath_jointSuppression_le_distanceFugacity
      S hfineCutoff rate hfineRate hcoarseRate hrate1 .reverse
      first second observableFaceId hobservableFace pair hlowering
      (finePacketFaceResponseConnectedActivePairPath
        S first.1 second.1 observableFaceId hobservableFace pair hpair)

/-! ## 4. Axiom audit -/

#print axioms finePacketOrientedJointSuppressionFactor_le_commonRatePower
#print axioms finePacketJointDistanceFugacity
#print axioms finePacketJointDistanceFugacity_lt_one
#print axioms finePacketOrientedConnectedPath_jointSuppression_le_distanceFugacity
#print axioms finePacketForwardNonzeroConnectedPair_jointSuppression_le_distanceFugacity
#print axioms finePacketReverseNonzeroConnectedPair_jointSuppression_le_distanceFugacity

end YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
