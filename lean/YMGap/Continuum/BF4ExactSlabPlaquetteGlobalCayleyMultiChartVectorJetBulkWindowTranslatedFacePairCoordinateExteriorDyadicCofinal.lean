/-
# Dyadic cofinal schedule for the coordinate exterior covariance comparison

The fixed-tolerance quadratic schedule is padded by its dyadic stage.  This
makes the spatial and temporal extents visibly cofinal without relying on the
stored rational representation of the denominator-bit precision.  At stage
`k` the actual canonical-full versus original-source covariance error is
bounded by `(1/2)^(k+1)`, and the resulting difference sequence converges to
zero.

This remains a finite fixed-nome comparison.  It does not prove target-volume
independence, a continuum measure, a Hamiltonian gap, or the Clay mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Positive dyadic tolerance used at a cofinal schedule stage. -/
def dyadicTolerance (stage : Nat) : Q' :=
  HalfPow.half ^ (stage + 1)

theorem dyadicTolerance_positive (stage : Nat) :
    (0 : Q') < dyadicTolerance stage := by
  exact HKPos.pow_pos (by decide : (0 : Q') < HalfPow.half) (stage + 1)

/-- The dyadic tolerance has the explicit convergence modulus `delta.den`. -/
theorem dyadicTolerance_eventually_le
    {delta : Q'} (hdelta : (0 : Q') < delta)
    {stage : Nat} (hstage : delta.den ≤ stage) :
    dyadicTolerance stage ≤ delta := by
  have hden : delta.den ≤ stage + 1 := Nat.le_trans hstage (Nat.le_succ stage)
  let offset := stage + 1 - delta.den
  have hexponent : delta.den + offset = stage + 1 := Nat.add_sub_of_le hden
  have hanti := ExpNeg.pow_half_antitone delta.den offset
  rw [hexponent] at hanti
  exact Q'.le_trans' _ _ _ hanti (HalfPow.pow_half_le delta hdelta)

/-- Stage-padded spatial side for the dyadic tolerance. -/
def dyadicScheduleSide
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) : Nat :=
  4 * (exteriorCollarSlope hd +
    exteriorCollarIntercept hw0 hd hs L (dyadicTolerance stage) + stage + 1)

/-- Temporal extent of the stage-padded schedule. -/
def dyadicScheduleTime
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) : Nat :=
  let side := dyadicScheduleSide hw0 hd hs L stage
  side * side

/-- Canonical target extent for the stage-padded schedule. -/
def dyadicScheduleTarget
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) : Nat :=
  let side := dyadicScheduleSide hw0 hd hs L stage
  originalBulkVectorQuadraticJetExtent side
    (dyadicScheduleTime hw0 hd hs L stage) L

/-- The spatial side is cofinal with the schedule stage. -/
theorem stage_le_dyadicScheduleSide
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) :
    stage ≤ dyadicScheduleSide hw0 hd hs L stage := by
  unfold dyadicScheduleSide
  omega

/-- The temporal extent is also cofinal with the schedule stage. -/
theorem stage_le_dyadicScheduleTime
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L stage : Nat) :
    stage ≤ dyadicScheduleTime hw0 hd hs L stage := by
  let side := dyadicScheduleSide hw0 hd hs L stage
  have hstage : stage ≤ side := stage_le_dyadicScheduleSide hw0 hd hs L stage
  have hside : 1 ≤ side := by
    dsimp only [side, dyadicScheduleSide]
    omega
  have hsquare : side ≤ side * side := by
    calc
      side = side * 1 := by omega
      _ ≤ side * side := Nat.mul_le_mul_left side hside
  exact Nat.le_trans hstage hsquare

private theorem affine_quadratic_room_with_padding
    (slope intercept padding : Nat) :
    let side := 4 * (slope + intercept + padding + 1)
    2 * (slope * side + intercept) + side ≤ side * side := by
  let total := slope + intercept + padding + 1
  let side := 4 * total
  have htotal : 0 < total := by
    dsimp only [total]
    omega
  have hslope : slope ≤ total := by
    dsimp only [total]
    omega
  have hintercept : intercept ≤ total := by
    dsimp only [total]
    omega
  have haffine : slope * side + intercept ≤ total * side + total :=
    Nat.add_le_add (Nat.mul_le_mul_right side hslope) hintercept
  have hself : total ≤ total * total := by
    calc
      total = total * 1 := by omega
      _ ≤ total * total := Nat.mul_le_mul_left total htotal
  have hscaled : 6 * total ≤ 8 * (total * total) := by
    have h6 := Nat.mul_le_mul_left 6 hself
    omega
  have hroom : 2 * (total * side + total) + side ≤ side * side := by
    dsimp only [side]
    have hlarge :
        2 * (total * (4 * total)) = 8 * (total * total) := by
      calc
        2 * (total * (4 * total)) = (2 * 4) * (total * total) := by
          ac_rfl
        _ = 8 * (total * total) := by rfl
    have hleft :
        2 * (total * (4 * total) + total) + 4 * total =
          8 * (total * total) + 6 * total := by
      rw [Nat.mul_add, hlarge]
      omega
    have hright :
        (4 * total) * (4 * total) = 16 * (total * total) := by
      calc
        (4 * total) * (4 * total) = (4 * 4) * (total * total) := by
          ac_rfl
        _ = 16 * (total * total) := by rfl
    rw [hleft, hright]
    omega
  exact Nat.le_trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 haffine) side)
    hroom

private theorem demand_le_min_collar {d side : Nat}
    (hroom : 2 * d + side ≤ side * side) :
    d ≤ Nat.min (side * side)
      (originalBulkVectorQuadraticJetSpatialCollar side) := by
  have hhalf : d ≤ (side * side - side) / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    omega
  have hcollar : d ≤ originalBulkVectorQuadraticJetSpatialCollar side := by
    unfold originalBulkVectorQuadraticJetSpatialCollar bulkSourceOffset
    omega
  exact Nat.le_min.mpr ⟨by omega, hcollar⟩

/-- The stage-padded schedule pays the complete collar at its dyadic
tolerance. -/
theorem dyadicSchedule_collar
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset stage : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage))
    (hrightFace : rightFace ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage)) :
    let side := dyadicScheduleSide hw0 hd hs L stage
    let time := dyadicScheduleTime hw0 hd hs L stage
    let target := dyadicScheduleTarget hw0 hd hs L stage
    5 * side + 3 * L + 5 + carrierRateBlock hd *
        coordinateExteriorCovarianceBlockCutoff hw0 hd hs side time leftOffset
          rightOffset L target (by exact Nat.le_refl _)
          leftFace rightFace (dyadicTolerance stage) ≤
      Nat.min time (originalBulkVectorQuadraticJetSpatialCollar side) := by
  let side := dyadicScheduleSide hw0 hd hs L stage
  let time := dyadicScheduleTime hw0 hd hs L stage
  let target := dyadicScheduleTarget hw0 hd hs L stage
  have htime : time = side * side := by rfl
  have htarget : originalBulkVectorQuadraticJetExtent side time L ≤ target := by
    exact Nat.le_refl _
  have hcutoff := coordinateExteriorCovarianceBlockCutoff_le_affine hw0 hd hs
    side time leftOffset rightOffset L target htarget leftFace rightFace
    hleftFace hrightFace hleftOffset hrightOffset
    (dyadicTolerance_positive stage)
  have hdemand :
      5 * side + 3 * L + 5 + carrierRateBlock hd *
          coordinateExteriorCovarianceBlockCutoff hw0 hd hs side time
            leftOffset rightOffset L target htarget leftFace rightFace
            (dyadicTolerance stage) ≤
        exteriorCollarSlope hd * side +
          exteriorCollarIntercept hw0 hd hs L (dyadicTolerance stage) := by
    exact Nat.le_trans
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left (carrierRateBlock hd) hcutoff)
        (5 * side + 3 * L + 5)) (by
        simp only [exteriorCollarSlope, exteriorCollarIntercept,
          Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
        omega)
  have hquadratic :
      2 * (exteriorCollarSlope hd * side +
          exteriorCollarIntercept hw0 hd hs L (dyadicTolerance stage)) + side ≤
        side * side := by
    simpa only [side, dyadicScheduleSide] using
      affine_quadratic_room_with_padding (exteriorCollarSlope hd)
        (exteriorCollarIntercept hw0 hd hs L (dyadicTolerance stage)) stage
  have hcap := demand_le_min_collar hquadratic
  dsimp only
  exact Nat.le_trans hdemand (by simpa only [htime] using hcap)

/-- At every dyadic stage, the actual canonical-full covariance is within the
dyadic tolerance of the actual original selected source covariance. -/
theorem canonicalFull_source_small_on_dyadicSchedule
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset stage : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage))
    (hrightFace : rightFace ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage)) :
    let side := dyadicScheduleSide hw0 hd hs L stage
    let time := dyadicScheduleTime hw0 hd hs L stage
    let target := dyadicScheduleTarget hw0 hd hs L stage
    leEv
      (CReal.abs (CReal.sub
        (canonicalFullFacePairCovariance hw0 hw1 side time L target
          (by exact Nat.le_refl _)
          leftOffset rightOffset leftFace rightFace)
        (originalSelectedFacePairCovariance hw0 hw1 side time L leftOffset
          rightOffset leftFace rightFace)))
      (ofQ' (dyadicTolerance stage)) := by
  let side := dyadicScheduleSide hw0 hd hs L stage
  let time := dyadicScheduleTime hw0 hd hs L stage
  let target := dyadicScheduleTarget hw0 hd hs L stage
  have htarget : originalBulkVectorQuadraticJetExtent side time L ≤ target := by
    exact Nat.le_refl _
  apply canonicalFull_source_small hw0 hw1 hsmall hd hs side time leftOffset
    rightOffset L target htarget leftFace rightFace hleftFace hrightFace
    hleftOffset hrightOffset (dyadicTolerance_positive stage)
  exact dyadicSchedule_collar hw0 hd hs L leftOffset rightOffset stage
    hleftOffset hrightOffset leftFace rightFace hleftFace hrightFace

/-- Difference between the scheduled canonical-full and original selected
source covariances. -/
def dyadicScheduledDifference
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset : Nat) (leftFace rightFace : Nat → Z4Plaq)
    (stage : Nat) : CReal :=
  let side := dyadicScheduleSide hw0 hd hs L stage
  let time := dyadicScheduleTime hw0 hd hs L stage
  let target := dyadicScheduleTarget hw0 hd hs L stage
  CReal.sub
    (canonicalFullFacePairCovariance hw0 hw1 side time L target
      (by exact Nat.le_refl _)
      leftOffset rightOffset (leftFace stage) (rightFace stage))
    (originalSelectedFacePairCovariance hw0 hw1 side time L leftOffset
      rightOffset (leftFace stage) (rightFace stage))

theorem dyadicScheduledDifference_small
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset stage : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Nat → Z4Plaq)
    (hleftFace : leftFace stage ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage))
    (hrightFace : rightFace stage ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage)) :
    leEv
      (CReal.abs (dyadicScheduledDifference hw0 hw1 hd hs L leftOffset
        rightOffset leftFace rightFace stage))
      (ofQ' (dyadicTolerance stage)) := by
  simpa only [dyadicScheduledDifference] using
    canonicalFull_source_small_on_dyadicSchedule hw0 hw1 hsmall hd hs L
      leftOffset rightOffset stage hleftOffset hrightOffset (leftFace stage)
      (rightFace stage) hleftFace hrightFace

/-- The actual scheduled covariance difference converges to zero.  Face
membership is supplied along the growing source windows; no target-volume or
continuum identification is inferred from this comparison limit. -/
theorem dyadicScheduledDifference_converges_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Nat → Z4Plaq)
    (hleftFace : ∀ stage, leftFace stage ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage))
    (hrightFace : ∀ stage, rightFace stage ∈
      bulkSourceFaces (dyadicScheduleSide hw0 hd hs L stage)) :
    CReal.ConvergesTo
      (fun stage => dyadicScheduledDifference hw0 hw1 hd hs L leftOffset
        rightOffset leftFace rightFace stage)
      CReal.czero := by
  intro delta hdelta
  let halfDelta := HalfPow.half * delta
  have hhalfDelta : (0 : Q') < halfDelta :=
    ExpNeg.half_mul_pos delta hdelta
  refine ⟨halfDelta.den, fun stage hstage => ?_⟩
  have htolerance : dyadicTolerance stage ≤ halfDelta :=
    dyadicTolerance_eventually_le hhalfDelta hstage
  have hsmallStage := dyadicScheduledDifference_small hw0 hw1 hsmall hd hs L
    leftOffset rightOffset stage hleftOffset hrightOffset leftFace rightFace
    (hleftFace stage) (hrightFace stage)
  have hhalfBound :
      leEv
        (CReal.abs (dyadicScheduledDifference hw0 hw1 hd hs L leftOffset
          rightOffset leftFace rightFace stage))
        (ofQ' halfDelta) :=
    leEv_trans hsmallStage
      (leEv_of_le (CReal.ofQ'_le_ofQ' htolerance))
  obtain ⟨approximationStage, happroximationStage⟩ :=
    hhalfBound halfDelta hhalfDelta
  refine ⟨approximationStage, fun approximation happroximation => ?_⟩
  let difference := dyadicScheduledDifference hw0 hw1 hd hs L leftOffset
    rightOffset leftFace rightFace stage
  have habsHalf :
      Q'.abs (difference.approx approximation) ≤ halfDelta + halfDelta := by
    exact happroximationStage approximation happroximation
  have habs : Q'.abs (difference.approx approximation) ≤ delta :=
    Q'.le_trans' _ _ _ habsHalf (Q'.le_of_eqv (ExpNeg.two_halves delta))
  constructor
  · show difference.approx approximation ≤ (0 : Q') + delta
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) (Q'.le_trans' _ _ _ habs
      (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' delta))))
  · show (0 : Q') ≤ difference.approx approximation + delta
    have hnegative : -delta ≤ difference.approx approximation := by
      have hnegAbs : -delta ≤ -(Q'.abs (difference.approx approximation)) :=
        Q'.neg_le_neg habs
      have habsLower : -(Q'.abs (difference.approx approximation)) ≤
          difference.approx approximation := by
        have hneg := Q'.neg_le_neg (Q'.neg_le_abs (difference.approx approximation))
        exact Q'.le_trans' _ _ _ hneg
          (Q'.le_of_eqv (Q'.neg_neg_eqv (difference.approx approximation)))
      exact Q'.le_trans' _ _ _ hnegAbs habsLower
    have hadd := Q'.add_le_add_right _ _ delta hnegative
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_add_self_eqv delta)) hadd

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal.dyadicTolerance_eventually_le
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal.stage_le_dyadicScheduleSide
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal.stage_le_dyadicScheduleTime
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal.dyadicSchedule_collar
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal.canonicalFull_source_small_on_dyadicSchedule
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal.dyadicScheduledDifference_converges_zero
