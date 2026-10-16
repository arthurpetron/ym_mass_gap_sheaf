/-
# Explicit cofinal schedule for the coordinate exterior covariance bound

The fixed-linear cutoff estimate is converted into an affine collar demand.
An explicit quadratic side length then pays that demand, with temporal extent
equal to the square of the side length.  The final theorem feeds the computed
collar directly into the actual canonical-full versus original-source law.

This is still a finite fixed-nome statement.  No target-volume limit,
continuum Hamiltonian, or Clay mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorOriginalLaw
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DyadicGeometricCutoff
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Block length of the carrier decay rate. -/
def carrierRateBlock {w : Q'} (hd : heatRemainderBound w < 1) : Nat :=
  blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4

/-- Block length after the four-dimensional shell rate is blocked to one half. -/
def shellRateBlock {w : Q'} (hd : heatRemainderBound w < 1) : Nat :=
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  blockLength (entropyRate 16 (rate ^ blockLength rate 4)) 0

/-- Closed denominator-bit cost of the requested tolerance against the fixed
local shell base. -/
def exteriorTolerancePrecision
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (epsilon : Q') : Nat :=
  denominatorBitPrecision
    (HKConv.divPos epsilon (1 + fixedCoordinateCovarianceShellBase hw0 hd hs))

/-- Coefficient of the source side in the affine cutoff bound. -/
def exteriorCutoffSlope {w : Q'} (hd : heatRemainderBound w < 1) : Nat :=
  shellRateBlock hd * (15 * 5)

/-- Source-side-independent part of the affine cutoff bound. -/
def exteriorCutoffIntercept
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L : Nat) (epsilon : Q') : Nat :=
  shellRateBlock hd * exteriorTolerancePrecision hw0 hd hs epsilon +
    (shellRateBlock hd * (15 * (3 * L)) +
      shellRateBlock hd * (15 * 5) +
      shellRateBlock hd * (4 * carrierRateBlock hd) +
      shellRateBlock hd * 26)

/-- Coefficient of the source side in the complete collar demand. -/
def exteriorCollarSlope {w : Q'} (hd : heatRemainderBound w < 1) : Nat :=
  5 + carrierRateBlock hd * exteriorCutoffSlope hd

/-- Source-side-independent part of the complete collar demand. -/
def exteriorCollarIntercept
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L : Nat) (epsilon : Q') : Nat :=
  3 * L + 5 + carrierRateBlock hd *
    exteriorCutoffIntercept hw0 hd hs L epsilon

/-- Explicit source side paying the affine collar demand. -/
def exteriorScheduleSide
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L : Nat) (epsilon : Q') : Nat :=
  4 * (exteriorCollarSlope hd +
    exteriorCollarIntercept hw0 hd hs L epsilon + 1)

/-- Temporal collar chosen to dominate the spatial collar. -/
def exteriorScheduleTime
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L : Nat) (epsilon : Q') : Nat :=
  let side := exteriorScheduleSide hw0 hd hs L epsilon
  side * side

/-- Canonical target extent for the scheduled source window. -/
def exteriorScheduleTarget
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L : Nat) (epsilon : Q') : Nat :=
  let side := exteriorScheduleSide hw0 hd hs L epsilon
  originalBulkVectorQuadraticJetExtent side
    (exteriorScheduleTime hw0 hd hs L epsilon) L

private theorem affine_quadratic_room (slope intercept : Nat) :
    let side := 4 * (slope + intercept + 1)
    2 * (slope * side + intercept) + side ≤ side * side := by
  let total := slope + intercept + 1
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

/-- The concrete exterior cutoff is bounded by the declared affine form. -/
theorem coordinateExteriorCovarianceBlockCutoff_le_affine
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s n leftOffset rightOffset L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon) :
    coordinateExteriorCovarianceBlockCutoff hw0 hd hs s n leftOffset
        rightOffset L target hroom leftFace rightFace epsilon ≤
      exteriorCutoffSlope hd * s +
        exteriorCutoffIntercept hw0 hd hs L epsilon := by
  have hlinear :=
    coordinateExteriorCovarianceBlockCutoff_le_fixedLinearScale hw0 hd hs
      s n leftOffset rightOffset L target hroom leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset hepsilon
  simpa only [exteriorCutoffSlope, exteriorCutoffIntercept,
    shellRateBlock, carrierRateBlock, exteriorTolerancePrecision,
    Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hlinear

/-- The scheduled side and time discharge the complete collar premise. -/
theorem exteriorSchedule_collar
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈
      bulkSourceFaces (exteriorScheduleSide hw0 hd hs L epsilon))
    (hrightFace : rightFace ∈
      bulkSourceFaces (exteriorScheduleSide hw0 hd hs L epsilon))
    (hepsilon : (0 : Q') < epsilon) :
    let side := exteriorScheduleSide hw0 hd hs L epsilon
    let time := exteriorScheduleTime hw0 hd hs L epsilon
    let target := exteriorScheduleTarget hw0 hd hs L epsilon
    5 * side + 3 * L + 5 + carrierRateBlock hd *
        coordinateExteriorCovarianceBlockCutoff hw0 hd hs side time leftOffset
          rightOffset L target (by exact Nat.le_refl _)
          leftFace rightFace epsilon ≤
      Nat.min time (originalBulkVectorQuadraticJetSpatialCollar side) := by
  let side := exteriorScheduleSide hw0 hd hs L epsilon
  let time := exteriorScheduleTime hw0 hd hs L epsilon
  let target := exteriorScheduleTarget hw0 hd hs L epsilon
  have htime : time = side * side := by rfl
  have htarget : originalBulkVectorQuadraticJetExtent side time L ≤ target := by
    exact Nat.le_refl _
  have hcutoff := coordinateExteriorCovarianceBlockCutoff_le_affine hw0 hd hs
    side time leftOffset rightOffset L target htarget leftFace rightFace
    hleftFace hrightFace hleftOffset hrightOffset hepsilon
  have hdemand :
      5 * side + 3 * L + 5 + carrierRateBlock hd *
          coordinateExteriorCovarianceBlockCutoff hw0 hd hs side time
            leftOffset rightOffset L target htarget leftFace rightFace epsilon ≤
        exteriorCollarSlope hd * side +
          exteriorCollarIntercept hw0 hd hs L epsilon := by
    exact Nat.le_trans
      (Nat.add_le_add_left
        (Nat.mul_le_mul_left (carrierRateBlock hd) hcutoff)
        (5 * side + 3 * L + 5)) (by
        simp only [exteriorCollarSlope, exteriorCollarIntercept,
          Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
        omega)
  have hquadratic :
      2 * (exteriorCollarSlope hd * side +
          exteriorCollarIntercept hw0 hd hs L epsilon) + side ≤
        side * side := by
    simpa only [side, exteriorScheduleSide] using
      affine_quadratic_room (exteriorCollarSlope hd)
        (exteriorCollarIntercept hw0 hd hs L epsilon)
  have hcap := demand_le_min_collar hquadratic
  dsimp only
  exact Nat.le_trans hdemand (by simpa only [htime] using hcap)

/-- Scheduled canonical-full covariance is within the requested tolerance of
the actual original selected source covariance, with no remaining collar
premise. -/
theorem canonicalFull_source_small_on_exteriorSchedule
    {w epsilon : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈
      bulkSourceFaces (exteriorScheduleSide hw0 hd hs L epsilon))
    (hrightFace : rightFace ∈
      bulkSourceFaces (exteriorScheduleSide hw0 hd hs L epsilon))
    (hepsilon : (0 : Q') < epsilon) :
    let side := exteriorScheduleSide hw0 hd hs L epsilon
    let time := exteriorScheduleTime hw0 hd hs L epsilon
    let target := exteriorScheduleTarget hw0 hd hs L epsilon
    leEv
      (CReal.abs (CReal.sub
        (canonicalFullFacePairCovariance hw0 hw1 side time L target
          (by exact Nat.le_refl _)
          leftOffset rightOffset leftFace rightFace)
        (originalSelectedFacePairCovariance hw0 hw1 side time L leftOffset
          rightOffset leftFace rightFace)))
      (ofQ' epsilon) := by
  let side := exteriorScheduleSide hw0 hd hs L epsilon
  let time := exteriorScheduleTime hw0 hd hs L epsilon
  let target := exteriorScheduleTarget hw0 hd hs L epsilon
  have htarget : originalBulkVectorQuadraticJetExtent side time L ≤ target := by
    exact Nat.le_refl _
  apply canonicalFull_source_small hw0 hw1 hsmall hd hs side time leftOffset
    rightOffset L target htarget leftFace rightFace hleftFace hrightFace
    hleftOffset hrightOffset hepsilon
  exact exteriorSchedule_collar hw0 hd hs L leftOffset rightOffset hleftOffset
    hrightOffset leftFace rightFace hleftFace hrightFace hepsilon

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule.exteriorScheduleSide
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule.coordinateExteriorCovarianceBlockCutoff_le_affine
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule.exteriorSchedule_collar
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule.canonicalFull_source_small_on_exteriorSchedule
