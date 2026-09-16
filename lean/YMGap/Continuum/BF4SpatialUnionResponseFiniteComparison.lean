/-
# Positive-response comparison on the actual current finite diagonal

The three actual current moments are compared with the embedded original
full response action, using one common cutoff and both actual partitions.
The joint error and two capped marginal errors total 6*c*c*A*rho^depth.
The proved original signed numerator floor is normalized and transported
to the filtered law. Upper/lower order is swapped only by coefficient/Haar
commutativity, never by an unsupported termwise-prefix assertion.

The final pin is to the existing connectedScalar at the actual diagonal
index s+1. No regulator limit is exchanged here, and no positivity for
the unfiltered action is assumed. Continuum and physical-scale claims
are outside this finite, fixed-nome comparison.
-/

import YMGap.Continuum.BF4SpatialUnionResponseBoundary
import YMGap.Continuum.BF4SpatialUnionResponseProbePins
import YMGap.Continuum.BF4SpatialUnionResponseActionPin
import YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
import YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm

namespace YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (heatProduct_supported)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialBoxBoundary (boxAmplitude)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl (chartProbe chartProbe_interval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedProbeControl (chartProbe_separated)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
  (paddedWidth recenter recenter_time)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialVariance (recenter_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator (connectedScalar)
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (lower upper lower_supported upper_supported)
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4SpatialUnionResponseGeometry
open YMGap.Continuum.BF4SpatialUnionResponseBoundary (depth)
open YMGap.Continuum.BF4SpatialUnionResponseProbePins
open YMGap.Continuum.BF4SpatialUnionResponseActionPin (insideIds insideIds_physical)
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:arg => List.length (boundaryCompleteSlabLinks extent)

def ambientCovariance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s stage : Nat) : Q' :=
  finiteCovariance w hw0 hw1 (targetExtent s) (ambientIds s)
    (fun _ hi => ambientIds_physical s hi) (currentUpper s) (currentLower s) stage

def filteredCovariance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s stage : Nat) : Q' :=
  finiteCovariance w hw0 hw1 (targetExtent s) (insideIds s) (insideIds_physical s)
    (currentUpper s) (currentLower s) stage

def errorAmplitude (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) : Q' :=
  (6*singleCap*singleCap)*boxAmplitude w hd hs 7

def errorBound (w : Q') (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (s : Nat) : Q' :=
  errorAmplitude w hd hs * (entropyRate 625 (adjustedCoreRate w hd))^(depth s)

private theorem twice_budget (c A r : Q') : ((c+c)*A)*r ≈ (2*c)*(A*r) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.add (.var 0) (.var 0)) (.var 1)) (.var 2))
    (.mul (.mul (.const 2) (.var 0)) (.mul (.var 1) (.var 2)))
    (by decide) (fun | 0 => c | 1 => A | _ => r)

private theorem square_budget (c A r : Q') :
    (((c*c)+(c*c))*A)*r ≈ (2*c*c)*(A*r) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))) (.var 1)) (.var 2))
    (.mul (.mul (.mul (.const 2) (.var 0)) (.var 0)) (.mul (.var 1) (.var 2)))
    (by decide) (fun | 0 => c | 1 => A | _ => r)

private theorem joint_eq (s : Nat) :
    chartProbe 1 (s+1) 3 (s+1) centralProbe (physicalTime 3 centralProbe) =
      polyMul (currentUpper s) (currentLower s) :=
  chartProbe_separated 1 (s+1) 0 3 (s+1) centralProbe centralProbe (by decide)

/-- The original signed connected difference, with all three actual moment
errors discharged and the same current probes on both action lists. -/
theorem covariance_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (s stage : Nat) :
    Q'.abs (ambientCovariance hw0 hw1 s stage + -(filteredCovariance hw0 hw1 s stage)) ≤
      errorBound w hd hs s := by
  have h0 := BF4SpatialUnionResponseBoundary.finiteValue_bound hw0 hw1 hsmall hd hs s
    (chartProbe 1 (s+1) 3 (s+1) centralProbe (physicalTime 3 centralProbe))
    (singleCap*singleCap) (joint_interval s) (joint_local s) stage
  rw [joint_eq] at h0
  have h1 := BF4SpatialUnionResponseBoundary.finiteValue_bound hw0 hw1 hsmall hd hs s
    (currentUpper s) singleCap (currentUpper_interval s) (currentUpper_local s) stage
  have h2 := BF4SpatialUnionResponseBoundary.finiteValue_bound hw0 hw1 hsmall hd hs s
    (currentLower s) singleCap (currentLower_interval s) (currentLower_local s) stage
  have h := finite_covariance_comparison w hw0 hw1 (targetExtent s) (ambientIds s)
    (fun _ hi => ambientIds_physical s hi) (insideIds s) (insideIds_physical s)
    (currentUpper s) (currentLower s) singleCap
    (boxAmplitude w hd hs 7 * (entropyRate 625 (adjustedCoreRate w hd))^(depth s))
    (currentUpper_interval s) (currentLower_interval s) stage
    (Q'.le_trans' _ _ _ h0 (Q'.le_of_eqv (square_budget _ _ _)))
    (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (twice_budget _ _ _)))
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (twice_budget _ _ _)))
  exact Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem finiteCovariance_swap {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (stage : Nat) :
    finiteCovariance w hw0 hw1 extent ids hi p q stage ≈
      finiteCovariance w hw0 hw1 extent ids hi q p stage :=
  Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _
      (@haar_of_coeff (blocks extent) _ _ ((RatPolyCoeffEqv.mul_comm p q).mul_right _)))
    (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv _ _))

/-- The original LOWER-UPPER floor is preserved when the current chart's
UPPER-LOWER order is restored by coefficient/Haar commutativity. -/
theorem source_floor (s stage : Nat) (hstage : 1 ≤ stage) :
    responseFloor ≤ finiteCovariance nome nome_pos nome_lt_one (sourceExtent s)
      (slabPhysicalFaceEdges (sourceExtent s)) (fun _ hi => hi)
      (upper (enlarge s shiftedProbe)) (lower (enlarge s shiftedProbe)) stage := by
  have h := finite_covariance_floor nome nome_pos nome_lt_one (sourceExtent s)
    (slabPhysicalFaceEdges (sourceExtent s)) (fun _ hi => hi)
    (lower (enlarge s shiftedProbe)) (upper (enlarge s shiftedProbe)) responseFloor stage
    (original_numerator_floor (headCutoff nome+stage) s
      (Nat.le_trans hstage (Nat.le_add_left _ _)))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (finiteCovariance_swap nome_pos nome_lt_one
    (sourceExtent s) (slabPhysicalFaceEdges (sourceExtent s)) (fun _ hi => hi)
    (lower (enlarge s shiftedProbe)) (upper (enlarge s shiftedProbe)) stage))

/-- Actual full-source action transport, with no premise asserting the floor. -/
theorem filtered_floor (s stage : Nat) (hstage : 1 ≤ stage) :
    responseFloor ≤ filteredCovariance nome_pos nome_lt_one s stage := by
  have hp := BF4SpatialUnionResponseActionPin.finiteCovariance_pin nome_pos nome_lt_one s
    (upper (enlarge s shiftedProbe)) (lower (enlarge s shiftedProbe))
    (upper_supported _) (lower_supported _) (currentUpper s) (currentLower s)
    (currentUpper_interval s).support (currentLower_interval s).support
    (upper_translation_prefix s) (lower_translation_prefix s) stage
  exact Q'.le_trans' _ _ _ (source_floor s stage hstage) (Q'.ge_of_eqv hp)

/-- The desired unfiltered finite value has only the PROVED geometric error
left to pay. The positive floor itself comes from the original action. -/
theorem finite_lower_bound (hsmall : heatRatio nome ≤ HalfPow.half)
    (hd : heatRemainderBound nome < 1)
    (hs : entropyRate 625 (adjustedCoreRate nome hd) < 1)
    (s stage : Nat) (hstage : 1 ≤ stage) :
    responseFloor ≤ ambientCovariance nome_pos nome_lt_one s stage + errorBound nome hd hs s :=
  Q'.le_trans' _ _ _ (filtered_floor s stage hstage)
    (ExpNeg.le_add_of_abs_sub_le (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm _ _))
      (covariance_bound nome_pos nome_lt_one hsmall hd hs s stage)))

private theorem finiteValue_prefix {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hq : SupportedQuaternionBlocks (blocks extent) q)
    (he : QuaternionPrefixPolynomialEqv (blocks extent) p q) (stage : Nat) :
    finiteValue w hw0 hw1 extent ids hi p stage ≈ finiteValue w hw0 hw1 extent ids hi q stage :=
  Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_prefixPolynomialEqv _
    (he.mul (.refl _ _))
    (supported_polyMul hp (heatProduct_supported w (headCutoff w+stage) extent ids))
    (supported_polyMul hq (heatProduct_supported w (headCutoff w+stage) extent ids)))

/-- Pin to the EXISTING connected diagonal. The three unit/joint moments
use precisely its common original action, cutoff and chart. -/
theorem diagonal_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (s : Nat) :
    connectedScalar hw0 hw1 (paddedWidth 1 (s+1)) (s+1) 3
      (recenter (s+1) centralProbe) (physicalTime 3 (recenter (s+1) centralProbe)) (s+1) ≈
      ambientCovariance hw0 hw1 s (s+1) := by
  have h1 := finiteValue_prefix hw0 hw1 (targetExtent s) (ambientIds s)
    (fun _ hi => ambientIds_physical s hi)
    (chartProbe 1 (s+1) 3 (s+1) centralProbe (unit 1)) (currentUpper s)
    (chartProbe_interval 1 (s+1) 3 (s+1) centralProbe (unit 1) (by decide) (by decide)).support
    (currentUpper_interval s).support (upper_marginal_prefix s) (s+1)
  have h2 := finiteValue_prefix hw0 hw1 (targetExtent s) (ambientIds s)
    (fun _ hi => ambientIds_physical s hi)
    (chartProbe 1 (s+1) 3 (s+1) (unit 1) (physicalTime 3 centralProbe)) (currentLower s)
    (chartProbe_interval 1 (s+1) 3 (s+1) (unit 1) (physicalTime 3 centralProbe)
      (by decide) (by decide)).support
    (currentLower_interval s).support (lower_marginal_prefix s) (s+1)
  unfold connectedScalar
  rw [← recenter_time (s+1) 3 centralProbe, ← recenter_unit 1 (s+1)]
  let F := fun p => finiteValue w hw0 hw1 (targetExtent s) (ambientIds s)
    (fun _ hi => ambientIds_physical s hi) p (s+1)
  change F (chartProbe 1 (s+1) 3 (s+1) centralProbe (physicalTime 3 centralProbe)) +
    -(F (chartProbe 1 (s+1) 3 (s+1) centralProbe (unit 1)) *
      F (chartProbe 1 (s+1) 3 (s+1) (unit 1) (physicalTime 3 centralProbe))) ≈
    F (polyMul (currentUpper s) (currentLower s)) + -(F (currentUpper s)*F (currentLower s))
  rw [joint_eq]
  exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ (qmul h1 h2))

end YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison

#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.ambientCovariance
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.filteredCovariance
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.errorAmplitude
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.errorBound
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.covariance_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.source_floor
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.filtered_floor
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.finite_lower_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResponseFiniteComparison.diagonal_pin
