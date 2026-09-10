/-
# Normalized response domination by the connected-event fraction

The preceding exact normalization turns the connected envelope into a finite
event probability.  This file closes the algebraic bridge back to the actual
observable: the absolute difference of the two normalized tilted-row face
responses is at most that connected-event fraction.

Thus every denominator from the two source-dependent rows is now eliminated
from the strictness frontier.  What remains is mathematical rather than
bookkeeping: prove an explicit subunit bound for the connected event from a
relative excitation or component-boundary activity estimate.

No strict rate, beta-uniformity, volume-uniformity, completed spectral gap,
continuum theory, or Clay theorem is asserted here.

Constructive contract: exact rational denominator clearing and order
transport only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
import YMGap.Continuum.TsumDeriv

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedResponseFraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt

local infix:50 " ≈ " => Q'.eqv

private theorem abs_mul_nonnegative_left_eqv_local
    (factor value : Q') (hfactor : (0 : Q') ≤ factor) :
    Q'.abs (factor * value) ≈ factor * Q'.abs value := by
  refine Q'.eqv_trans _ (Q'.abs (value * factor)) _
    (Q'.abs_eqv_congr (Q'.mul_comm_eqv factor value)) ?_
  refine Q'.eqv_trans _ (Q'.abs value * factor) _
    (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right value hfactor) ?_
  exact Q'.mul_comm_eqv (Q'.abs value) factor

private theorem abs_response_mul_two_scale_eqv_two_cross_abs_local
    (response scale rawCross : Q')
    (hscale : (0 : Q') ≤ scale)
    (hclear : response * scale ≈ rawCross) :
    Q'.abs response * ((2 : Q') * scale) ≈
      Q'.abs ((2 : Q') * rawCross) := by
  refine Q'.eqv_trans _
    ((2 : Q') * (Q'.abs response * scale)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((Q'.abs response * (2 : Q')) * scale) _ ?_ ?_
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.abs response) (2 : Q') scale)
    refine Q'.eqv_trans _
      (((2 : Q') * Q'.abs response) * scale) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ scale
        (Q'.mul_comm_eqv (Q'.abs response) (2 : Q'))
    · exact Q'.mul_assoc_eqv (2 : Q') (Q'.abs response) scale
  refine Q'.eqv_trans _
    ((2 : Q') * Q'.abs (response * scale)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (YMGap.Continuum.TsumDeriv.abs_mul_nonneg_right
          response hscale))
  refine Q'.eqv_trans _
    ((2 : Q') * Q'.abs rawCross) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.abs_eqv_congr hclear)
  exact Q'.eqv_symm
    (abs_mul_nonnegative_left_eqv_local
      (2 : Q') rawCross (Q'.le_of_lt (Q'.ofNat_succ_pos 1)))

/-- The actual difference of the two normalized one-face responses is bounded
by the explicitly normalized connected-event mass.  This is the last exact
algebraic bridge before the strict connected-activity estimate. -/
theorem positivePhysicalTiltedGibbsFaceResponseDifference_abs_le_connectedEnvelopeFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    Q'.abs
        (positivePhysicalSourceTiltedGibbsEventMass
            S hfineCutoff hcoarseCoupling first
              (slabPhysicalFacePositiveB observableFaceId) -
          positivePhysicalSourceTiltedGibbsEventMass
            S hfineCutoff hcoarseCoupling second
              (slabPhysicalFacePositiveB observableFaceId)) ≤
      finePacketConnectedEnvelopeFraction
        S hfineCutoff hcoarseCoupling first second observableFaceId := by
  let response :=
    positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling first
          (slabPhysicalFacePositiveB observableFaceId) -
      positivePhysicalSourceTiltedGibbsEventMass
        S hfineCutoff hcoarseCoupling second
          (slabPhysicalFacePositiveB observableFaceId)
  let scale :=
    positivePhysicalSourceTiltedGibbsRowMass S first *
      positivePhysicalSourceTiltedGibbsRowMass S second
  let rawCross :=
    positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
      S first second (slabPhysicalFacePositiveB observableFaceId)
  let connectedMass :=
    listQSum
      (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
      (finePacketFaceResponseConnectedActivePairs
        S first.1 second.1 observableFaceId)
  have hfirstMass := positivePhysicalSourceTiltedGibbsRowMass_pos
    S hfineCutoff hcoarseCoupling first
  have hsecondMass := positivePhysicalSourceTiltedGibbsRowMass_pos
    S hfineCutoff hcoarseCoupling second
  have hscalePos : (0 : Q') < scale :=
    Q'.mul_pos hfirstMass hsecondMass
  have hclear : response * scale ≈ rawCross := by
    exact positivePhysicalTiltedGibbsEventResponseDifference_mul_masses_eqv_rawCross
      S hfineCutoff hcoarseCoupling first second
        (slabPhysicalFacePositiveB observableFaceId)
  have habsClear :
      Q'.abs response * finePacketConnectedEnvelopeNormalizationMass
          S first second ≈
        Q'.abs ((2 : Q') * rawCross) := by
    unfold finePacketConnectedEnvelopeNormalizationMass
    exact abs_response_mul_two_scale_eqv_two_cross_abs_local
      response scale rawCross (Q'.le_of_lt hscalePos) hclear
  have hrawBound : Q'.abs ((2 : Q') * rawCross) ≤ connectedMass := by
    exact two_mul_positivePhysicalTiltedGibbsRawCross_abs_le_connectedEnvelopeSum
      S hfineCutoff first second observableFaceId hobservableFace
  have hmul :
      Q'.abs response * finePacketConnectedEnvelopeNormalizationMass
          S first second ≤ connectedMass :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv habsClear) hrawBound
  unfold finePacketConnectedEnvelopeFraction
  exact Q'.le_divPos_of_mul_le _ _
    (finePacketConnectedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)
    hmul

/-! ## Axiom audit -/

#print axioms positivePhysicalTiltedGibbsFaceResponseDifference_abs_le_connectedEnvelopeFraction

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedResponseFraction
