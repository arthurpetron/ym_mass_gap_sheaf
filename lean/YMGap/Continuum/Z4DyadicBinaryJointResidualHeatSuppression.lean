/-
# Preserve residual heat after extracting connected distance

The common-rate estimate for a connected joint source-target contribution
contains more heat activity than the three units per plaquette needed to pay
its observable-to-source distance.  Discarding that excess activity leaves a
coupling-one sum with artificial volume congestion.

This module instead defines the residual exponent constructively as

`total common-rate exponent - 3 * (distance + 1)`.

The connected activity floor proves exact natural-number reconstruction, so
the common rate power factors as

`(rate^3)^(distance + 1) * rate^residual`.

Consequently the actual two-coupling suppression is bounded by that product.
The residual heat is retained for the subsequent component/exterior sum; no
entropy or volume-uniform bound is asserted here.

Constructive contract: natural subtraction is guarded by the proved activity
floor, and all rational identities are explicit; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression

namespace YMGap.Continuum.Z4DyadicBinaryJointResidualHeatSuppression

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Total, extracted, and residual exponents -/

/-- The exponent after both physical couplings have been raised to one common
upper rate.  It still contains the complete fine occupation and coarse SU(2)
excitation excess. -/
def finePacketOrientedJointCommonRateExponent
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Nat :=
  3 * (fineCouplingPhysicalOccupiedFaceCount S first +
      fineCouplingPhysicalOccupiedFaceCount S second) +
    finePacketOrientedTotalTargetCasimirExcess
      S orientation first second pair

/-- Exactly the exponent spent on observable-to-source distance. -/
def finePacketConnectedDistanceHeatExponent
    (S : SlabScalePair) (observableFaceId sourceFaceId : Nat) : Nat :=
  3 * (linfDist
      (slabPlaquetteAt S.coarse.extent observableFaceId)
      (slabPlaquetteAt S.coarse.extent sourceFaceId) + 1)

/-- Heat activity remaining after the geometric distance has been paid. -/
def finePacketOrientedConnectedResidualHeatExponent
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (pair : EdgeLabelling × EdgeLabelling)
    (path : FinePacketObservableConnectedDisagreementPath
      S first second observableFaceId pair) : Nat :=
  finePacketOrientedJointCommonRateExponent
      S orientation first second pair -
    finePacketConnectedDistanceHeatExponent
      S observableFaceId path.sourceFaceId

/-- The proved connected activity floor makes residual subtraction exact. -/
theorem finePacketOrientedConnected_distance_add_residual_eq_commonRateExponent
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (path : FinePacketObservableConnectedDisagreementPath
      S first.1 second.1 observableFaceId pair) :
    finePacketConnectedDistanceHeatExponent
        S observableFaceId path.sourceFaceId +
      finePacketOrientedConnectedResidualHeatExponent
        S orientation first.1 second.1 observableFaceId pair path =
      finePacketOrientedJointCommonRateExponent
        S orientation first.1 second.1 pair := by
  unfold finePacketConnectedDistanceHeatExponent
    finePacketOrientedConnectedResidualHeatExponent
    finePacketOrientedJointCommonRateExponent
  exact Nat.add_sub_of_le
    (finePacketOrientedConnectedPath_scaledHeatActivity_floor
      S hfineCutoff orientation first second observableFaceId
        hobservableFace pair hlowering path)

/-! ## 2. Exact common-rate factorization -/

/-- The common-rate power retains every unit not spent on distance. -/
theorem finePacketOrientedConnected_commonRatePower_eqv_distance_mul_residual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q')
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (path : FinePacketObservableConnectedDisagreementPath
      S first.1 second.1 observableFaceId pair) :
    qpow rate
        (finePacketOrientedJointCommonRateExponent
          S orientation first.1 second.1 pair) ≈
      qpow (finePacketJointDistanceFugacity rate)
          (linfDist
            (slabPlaquetteAt S.coarse.extent observableFaceId)
            (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) *
        qpow rate
          (finePacketOrientedConnectedResidualHeatExponent
            S orientation first.1 second.1 observableFaceId pair path) := by
  have hexponent :=
    finePacketOrientedConnected_distance_add_residual_eq_commonRateExponent
      S hfineCutoff orientation first second observableFaceId
        hobservableFace pair hlowering path
  rw [← hexponent]
  refine Q'.eqv_trans _ _ _
    (HeatKernelRGStep.qpow_add rate
      (finePacketConnectedDistanceHeatExponent
        S observableFaceId path.sourceFaceId)
      (finePacketOrientedConnectedResidualHeatExponent
        S orientation first.1 second.1 observableFaceId pair path)) ?_
  unfold finePacketConnectedDistanceHeatExponent
    finePacketJointDistanceFugacity
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (HeatKernelRGStep.qpow_qpow rate 3
        (linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1)))

/-! ## 3. Refined suppression inequality -/

/-- Extract distance from the actual two-coupling heat factor while retaining
the residual common-rate power needed for exterior summation. -/
theorem finePacketOrientedConnectedPath_jointSuppression_le_distance_mul_residual
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
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
            (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) *
        qpow rate
          (finePacketOrientedConnectedResidualHeatExponent
            S orientation first.1 second.1 observableFaceId pair path) := by
  have hcommon :=
    finePacketOrientedJointSuppressionFactor_le_commonRatePower
      S rate hfineRate hcoarseRate orientation first.1 second.1 pair
  have hfactor :=
    finePacketOrientedConnected_commonRatePower_eqv_distance_mul_residual
      S hfineCutoff rate orientation first second observableFaceId
        hobservableFace pair hlowering path
  exact Q'.le_trans' _ _ _ hcommon (Q'.le_of_eqv hfactor)

/-! ## 4. Axiom audit -/

#print axioms finePacketOrientedJointCommonRateExponent
#print axioms finePacketConnectedDistanceHeatExponent
#print axioms finePacketOrientedConnectedResidualHeatExponent
#print axioms finePacketOrientedConnected_distance_add_residual_eq_commonRateExponent
#print axioms finePacketOrientedConnected_commonRatePower_eqv_distance_mul_residual
#print axioms finePacketOrientedConnectedPath_jointSuppression_le_distance_mul_residual

end YMGap.Continuum.Z4DyadicBinaryJointResidualHeatSuppression
