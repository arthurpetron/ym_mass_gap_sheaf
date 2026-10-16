/-
# Selected-window vector jet as a true finite covariance

The selected-window pair of the physical vector jet, centered at its finite
OWN one-step mean, is rewritten as the actual cross-time covariance under the
same selected ORIGINAL face-set law plus one endpoint-centering square.  The
square already has the geometric endpoint-mixing payment.

This isolates the cancellation-preserving object needed for a later
selected-action/full-action comparison.  It does not compare those actions,
remove a cutoff, pay the complete strict margin, or prove a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
  (endpoint_means_eqv)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
  (placedSpan sourceSpan windowRatio_span_mul_originalFiniteValue)
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowExpectationBridgeBound
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyVectorJetBulkNorthWeightDeficit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPhysicalFaceEdges)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Actual cross-time covariance of the two placed vector jets under the
same finite selected ORIGINAL face-set law. -/
def originalBulkVectorQuadraticJetSelectedCrossCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  finiteCovariance w hw0 hw1
    (originalBulkVectorQuadraticJetExtent s n L)
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical s n L)
    (originalBulkVectorQuadraticJetPlaced s hs n 0 L)
    (originalBulkVectorQuadraticJetPlaced s hs n L L)
    stage

/-- The only correction from the finite OWN center to the selected-law
endpoint mean.  Symmetric external boundaries make the two endpoint means
equal, so the correction is one square. -/
def originalBulkVectorQuadraticJetSelectedCenterMismatchSquare
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  let mismatch :=
    originalBulkVectorQuadraticJetSelectedMean
        hw0 hw1 s hs stage n L 0 +
      -originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  mismatch * mismatch

private theorem rawPair_span_originalFiniteValue
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width n L extent : Nat} (jet : RatPoly)
    (leftSchedule rightSchedule :
      List (Q' × List (Nat × List FaceFactor)))
    (hleftSource : HaarCarrierEqv ((L + 1) * N width)
      (sourceSpan width leftSchedule) jet)
    (hrightSource : HaarCarrierEqv ((L + 1) * N width)
      (sourceSpan width rightSchedule)
      (liftBoundary (L * N width) jet))
    (hwidth : width ≤ extent)
    (htime : 0 + (n + (L + n)) ≤ extent)
    (hleftWithin : ∀ x, x ∈ leftSchedule → ∀ entry, entry ∈ x.2 →
      entry.1 ≤ L)
    (hleftFaces : ∀ x, x ∈ leftSchedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces width)
    (hrightWithin : ∀ x, x ∈ rightSchedule → ∀ entry, entry ∈ x.2 →
      entry.1 ≤ L)
    (hrightFaces : ∀ x, x ∈ rightSchedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces width)
    (stage : Nat) :
    rawPair hw0 hw1 (headCutoff w + stage) width
        (Nat.le_add_right _ _) n L jet ≈
      finiteValue w hw0 hw1 extent
        (chainIds extent width 0 (n + (L + n)))
        (fun _ hi => chainIds_physical hi)
        (polyMul
          (placedSpan extent (0 + n) leftSchedule)
          (placedSpan extent (0 + n) rightSchedule))
        stage := by
  exact Q'.eqv_trans _ _ _
    (windowRatio_carrier_congr hw0 hw1
      (headCutoff w + stage) width (Nat.le_add_right _ _) n L n
      (HaarCarrierEqv.mul hleftSource.symm hrightSource.symm))
    (windowRatio_span_mul_originalFiniteValue
      hw0 hw1 hwidth htime leftSchedule rightSchedule
      hleftWithin hleftFaces hrightWithin hrightFaces stage)

private theorem endpoint_value_eqv {leftWindow rightWindow leftValue rightValue : Q'}
    (hleft : leftWindow ≈ leftValue)
    (hright : rightWindow ≈ rightValue)
    (hendpoint : leftWindow ≈ rightWindow) :
    rightValue ≈ leftValue :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm hright)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hendpoint) hleft)

private theorem windowRatio_carrier_span_originalFiniteValue
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width n L extent : Nat} (jet : RatPoly)
    (schedule : List (Q' × List (Nat × List FaceFactor)))
    (hsource : HaarCarrierEqv ((L + 1) * N width)
      (sourceSpan width schedule) jet)
    (hwidth : width ≤ extent)
    (htime : 0 + (n + (L + n)) ≤ extent)
    (hwithin : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 →
      entry.1 ≤ L)
    (hfaces : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces width)
    (stage : Nat) :
    windowRatio hw0 hw1 (headCutoff w + stage) width
        (Nat.le_add_right _ _) n L n jet ≈
      finiteValue w hw0 hw1 extent
        (chainIds extent width 0 (n + (L + n)))
        (fun _ hi => chainIds_physical hi)
        (placedSpan extent n schedule) stage := by
  exact Q'.eqv_trans _ _ _
    (windowRatio_carrier_congr hw0 hw1 (headCutoff w + stage) width
      (Nat.le_add_right _ _) n L n hsource.symm)
    (by simpa only [Nat.zero_add] using
      (windowRatio_span_originalFiniteValue hw0 hw1 hwidth htime
        schedule hwithin hfaces stage))

private theorem centered_covariance_split_of_pins
    {window raw mean liftedMean productValue leftMean rightMean center : Q'}
    (hcentered : window ≈
      raw + -((center + center) * mean) + center * center)
    (hpair : raw ≈ productValue)
    (hleft : mean ≈ leftMean)
    (hright : liftedMean ≈ rightMean)
    (hendpoint : mean ≈ liftedMean) :
    window ≈
      (productValue + -(leftMean * rightMean)) +
        ((leftMean + -center) * (leftMean + -center)) := by
  have hrightLeft : rightMean ≈ leftMean :=
    endpoint_value_eqv hleft hright hendpoint
  have hreplace :
      raw + -((center + center) * mean) + center * center ≈
        productValue + -((center + center) * leftMean) + center * center :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hpair
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (center + center) _ _ hleft)))
      (Q'.eqv_refl _)
  have halgebra :
      productValue + -((center + center) * leftMean) + center * center ≈
        (productValue + -(leftMean * leftMean)) +
          ((leftMean + -center) * (leftMean + -center)) := by
    exact poly_identity_of_normal_eq
      (.add
        (.add (.var 0)
          (.neg (.mul (.add (.var 2) (.var 2)) (.var 1))))
        (.mul (.var 2) (.var 2)))
      (.add
        (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
        (.mul (.add (.var 1) (.neg (.var 2)))
          (.add (.var 1) (.neg (.var 2)))))
      (by decide)
      (fun | 0 => productValue | 1 => leftMean | _ => center)
  have hcross :
      productValue + -(leftMean * rightMean) ≈
        productValue + -(leftMean * leftMean) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left leftMean _ _ hrightLeft))
  have hfinal :
      (productValue + -(leftMean * leftMean)) +
          ((leftMean + -center) * (leftMean + -center)) ≈
        (productValue + -(leftMean * rightMean)) +
          ((leftMean + -center) * (leftMean + -center)) :=
    Q'.add_eqv_congr' hcross.symm (Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ hcentered
    (Q'.eqv_trans _ _ _ hreplace (Q'.eqv_trans _ _ _ halgebra hfinal))

private theorem centeredPair_span_originalFiniteCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    {width n L extent : Nat} (jet : RatPoly)
    (leftSchedule rightSchedule :
      List (Q' × List (Nat × List FaceFactor)))
    (hjet : SupportedQuaternionBlocks (N width) jet)
    (hleftSource : HaarCarrierEqv ((L + 1) * N width)
      (sourceSpan width leftSchedule) jet)
    (hrightSource : HaarCarrierEqv ((L + 1) * N width)
      (sourceSpan width rightSchedule)
      (liftBoundary (L * N width) jet))
    (hwidth : width ≤ extent)
    (htime : 0 + (n + (L + n)) ≤ extent)
    (hleftWithin : ∀ x, x ∈ leftSchedule → ∀ entry, entry ∈ x.2 →
      entry.1 ≤ L)
    (hleftFaces : ∀ x, x ∈ leftSchedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces width)
    (hrightWithin : ∀ x, x ∈ rightSchedule → ∀ entry, entry ∈ x.2 →
      entry.1 ≤ L)
    (hrightFaces : ∀ x, x ∈ rightSchedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces width)
    (stage : Nat) (center : Q') :
    centeredPair hw0 hw1 (headCutoff w + stage) width
        (Nat.le_add_right _ _) n L jet center ≈
      finiteCovariance w hw0 hw1 extent
          (chainIds extent width 0 (n + (L + n)))
          (fun _ hi => chainIds_physical hi)
          (placedSpan extent n leftSchedule)
          (placedSpan extent n rightSchedule)
          stage +
        ((finiteValue w hw0 hw1 extent
              (chainIds extent width 0 (n + (L + n)))
              (fun _ hi => chainIds_physical hi)
              (placedSpan extent n leftSchedule) stage + -center) *
          (finiteValue w hw0 hw1 extent
              (chainIds extent width 0 (n + (L + n)))
              (fun _ hi => chainIds_physical hi)
              (placedSpan extent n leftSchedule) stage + -center)) := by
  let ids := chainIds extent width 0 (n + (L + n))
  let hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent :=
    fun _ hi => chainIds_physical hi
  let leftSource := sourceSpan width leftSchedule
  let rightSource := sourceSpan width rightSchedule
  let leftPlaced := placedSpan extent n leftSchedule
  let rightPlaced := placedSpan extent n rightSchedule
  let raw := rawPair hw0 hw1 (headCutoff w + stage) width
    (Nat.le_add_right _ _) n L jet
  let mean := windowRatio hw0 hw1 (headCutoff w + stage) width
    (Nat.le_add_right _ _) n L n jet
  let liftedMean := windowRatio hw0 hw1 (headCutoff w + stage) width
    (Nat.le_add_right _ _) n L n
    (liftBoundary (L * N width) jet)
  let productValue := finiteValue w hw0 hw1 extent ids hids
    (polyMul leftPlaced rightPlaced) stage
  let leftMean := finiteValue w hw0 hw1 extent ids hids leftPlaced stage
  let rightMean := finiteValue w hw0 hw1 extent ids hids rightPlaced stage
  have hcentered := centered_pair_pin hw0 hw1
    (headCutoff w + stage) width (Nat.le_add_right _ _) n L hjet center
  have hpair : raw ≈ productValue := by
    simpa only [Nat.zero_add, raw, productValue, ids, hids, leftPlaced,
      rightPlaced, leftSource, rightSource] using
      (rawPair_span_originalFiniteValue hw0 hw1 jet leftSchedule
        rightSchedule hleftSource hrightSource hwidth htime hleftWithin
        hleftFaces hrightWithin hrightFaces stage)
  have hleft : mean ≈ leftMean := by
    simpa only [leftMean, mean, ids, hids, leftPlaced] using
      (windowRatio_carrier_span_originalFiniteValue hw0 hw1 jet
        leftSchedule hleftSource hwidth htime hleftWithin hleftFaces stage)
  have hright : liftedMean ≈ rightMean := by
    simpa only [rightMean, liftedMean, ids, hids, rightPlaced] using
      (windowRatio_carrier_span_originalFiniteValue hw0 hw1
        (liftBoundary (L * N width) jet) rightSchedule hrightSource
        hwidth htime hrightWithin hrightFaces stage)
  have hendpoint := endpoint_means_eqv hw0 hw1
    (headCutoff w + stage) width (Nat.le_add_right _ _) n L hjet
  change centeredPair hw0 hw1 (headCutoff w + stage) width
      (Nat.le_add_right _ _) n L jet center ≈
    (productValue + -(leftMean * rightMean)) +
      ((leftMean + -center) * (leftMean + -center))
  exact centered_covariance_split_of_pins
    hcentered hpair hleft hright hendpoint

/-- Exact cancellation-preserving split of the selected-window pair into its
true selected-law cross covariance and the OWN-center mismatch square. -/
theorem originalBulkVectorQuadraticJetWindowPair_selectedCrossCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    originalBulkVectorQuadraticJetWindowPair
        hw0 hw1 s hs stage n L ≈
      originalBulkVectorQuadraticJetSelectedCrossCovariance
          hw0 hw1 s hs stage n L +
        originalBulkVectorQuadraticJetSelectedCenterMismatchSquare
          hw0 hw1 s hs stage n L := by
  let width := s * s
  let jet := originalBulkVectorQuadraticJet s hs
  let center := originalBulkVectorQuadraticJetOwnMean
    hw0 hw1 s hs stage n
  let extent := originalBulkVectorQuadraticJetExtent s n L
  let leftSchedule := originalBulkVectorQuadraticJetSchedule s hs 0
  let rightSchedule := originalBulkVectorQuadraticJetSchedule s hs L
  let leftSource := sourceSpan width leftSchedule
  let rightSource := sourceSpan width rightSchedule
  have hleftSource : HaarCarrierEqv ((L + 1) * N width)
      leftSource jet := by
    simpa only [width, leftSource, leftSchedule, Nat.zero_mul,
      liftBoundary] using
      (originalBulkVectorQuadraticJetSchedule_source_full
        s hs 0 L (Nat.zero_le _))
  have hrightSource : HaarCarrierEqv ((L + 1) * N width)
      rightSource (liftBoundary (L * N width) jet) := by
    simpa only [width, rightSource, rightSchedule, jet] using
      (originalBulkVectorQuadraticJetSchedule_source_full
        s hs L L (Nat.le_refl _))
  have hwidth : width ≤ extent := by
    unfold width extent originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  have htime : 0 + (n + (L + n)) ≤ extent := by
    unfold extent originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  have h := centeredPair_span_originalFiniteCovariance hw0 hw1 jet
    leftSchedule rightSchedule
    (originalBulkVectorQuadraticJet_supported s hs)
    hleftSource hrightSource hwidth htime
    (fun x hx entry hentry =>
      Nat.le_trans
        (originalBulkVectorQuadraticJetSchedule_within
          s hs 0 x hx entry hentry)
        (Nat.zero_le _))
    (originalBulkVectorQuadraticJetSchedule_faces s hs 0)
    (originalBulkVectorQuadraticJetSchedule_within s hs L)
    (originalBulkVectorQuadraticJetSchedule_faces s hs L)
    stage center
  simpa only [originalBulkVectorQuadraticJetWindowPair, laggedWindowPair,
    centeredPair, originalBulkVectorQuadraticJetOwnShifted,
    originalBulkVectorQuadraticJetSelectedCrossCovariance,
    originalBulkVectorQuadraticJetSelectedCenterMismatchSquare,
    originalBulkVectorQuadraticJetSelectedMean,
    originalBulkVectorQuadraticJetPlaced,
    originalBulkVectorQuadraticJetIds,
    originalBulkVectorQuadraticJetExtent, width, jet, center, extent,
    leftSchedule, rightSchedule] using h

/-- The finite endpoint-centering square is already paid by the existing
geometric endpoint-mixing error. -/
theorem originalBulkVectorQuadraticJetSelectedCenterMismatchSquare_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    originalBulkVectorQuadraticJetSelectedCenterMismatchSquare
        hw0 hw1 s hs stage n L ≤
      originalBulkVectorQuadraticJetSelectedMeanError
          hw0 hw1 s hs n *
        originalBulkVectorQuadraticJetSelectedMeanError
          hw0 hw1 s hs n := by
  unfold originalBulkVectorQuadraticJetSelectedCenterMismatchSquare
  exact originalBulkVectorQuadraticJetSelectedMean_zero_mismatch_square_le
    hw0 hw1 s hs stage n L

/-- The selected-window covariance and center correction on the common
pair normalization `(2^66)^2`. -/
def originalBulkVectorQuadraticJetScaledSelectedCrossCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  let scale := globalCayleyVectorJetNorthWeightScale
  (scale * scale) *
    originalBulkVectorQuadraticJetSelectedCrossCovariance
      hw0 hw1 s hs stage n L

def originalBulkVectorQuadraticJetScaledSelectedCenterMismatchSquare
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) : Q' :=
  let scale := globalCayleyVectorJetNorthWeightScale
  (scale * scale) *
    originalBulkVectorQuadraticJetSelectedCenterMismatchSquare
      hw0 hw1 s hs stage n L

/-- Exact scaled split consumed by the selected-window/full-slab law bridge. -/
theorem originalBulkVectorQuadraticJetScaledWindowPair_selectedCrossCovariance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    originalBulkVectorQuadraticJetScaledWindowPair
        hw0 hw1 s hs stage n L ≈
      originalBulkVectorQuadraticJetScaledSelectedCrossCovariance
          hw0 hw1 s hs stage n L +
        originalBulkVectorQuadraticJetScaledSelectedCenterMismatchSquare
          hw0 hw1 s hs stage n L := by
  let scaleSquare := globalCayleyVectorJetNorthWeightScale *
    globalCayleyVectorJetNorthWeightScale
  have h := originalBulkVectorQuadraticJetWindowPair_selectedCrossCovariance
    hw0 hw1 s hs stage n L
  change scaleSquare * originalBulkVectorQuadraticJetWindowPair
      hw0 hw1 s hs stage n L ≈
    scaleSquare * originalBulkVectorQuadraticJetSelectedCrossCovariance
        hw0 hw1 s hs stage n L +
      scaleSquare * originalBulkVectorQuadraticJetSelectedCenterMismatchSquare
        hw0 hw1 s hs stage n L
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left scaleSquare _ _ h)
    (Q'.mul_add_eqv _ _ _)

/-- Explicit geometric payment for the scaled center-mismatch square. -/
theorem originalBulkVectorQuadraticJetScaledSelectedCenterMismatchSquare_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    originalBulkVectorQuadraticJetScaledSelectedCenterMismatchSquare
        hw0 hw1 s hs stage n L ≤
      let scale := globalCayleyVectorJetNorthWeightScale
      (scale * scale) *
        (originalBulkVectorQuadraticJetSelectedMeanError
            hw0 hw1 s hs n *
          originalBulkVectorQuadraticJetSelectedMeanError
            hw0 hw1 s hs n) := by
  let scaleSquare := globalCayleyVectorJetNorthWeightScale *
    globalCayleyVectorJetNorthWeightScale
  have hscale : (0 : Q') ≤ scaleSquare := by
    unfold scaleSquare globalCayleyVectorJetNorthWeightScale
    decide
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (originalBulkVectorQuadraticJetSelectedCenterMismatchSquare_le
      hw0 hw1 s hs stage n L) hscale

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance.originalBulkVectorQuadraticJetWindowPair_selectedCrossCovariance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance.originalBulkVectorQuadraticJetSelectedCenterMismatchSquare_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance.originalBulkVectorQuadraticJetScaledWindowPair_selectedCrossCovariance
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowSelectedCovariance.originalBulkVectorQuadraticJetScaledSelectedCenterMismatchSquare_le
