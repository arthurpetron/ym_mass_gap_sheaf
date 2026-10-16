/-
# A positive finite Heron stage for the central bulk-source witness

The central source face has an exact positive one-bond covariance and the
uniform coefficient floor `3^(-18)`.  This leaf applies the existing generic
Heron residual factorization and geometric modulus to that same face.  It
selects an explicit finite stage where the staged central mixed covariance
retains at least half of its exact value, then preserves its color-zero row as
a positive summand of the complete weighted source-time row trace.

The selected stage, exact covariance, and row norm remain side-dependent.
No cutoff-uniform covariance estimate, original-law comparison, continuum
limit, Hamiltonian gap, or Clay theorem is asserted.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
import YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalFreeHistoryQuadratic
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

private theorem finiteRowNorm2_nonnegative_local
    (N : Nat) (row : Nat → Q') :
    (0 : Q') ≤ finiteRowNorm2 N row := by
  unfold finiteRowNorm2
  rw [qListSum_map_eq_listQSum_local]
  apply listQSum_nonnegative_on
  intro coordinate _
  exact SumOfSquares.q_mul_self_nonneg (row coordinate)

/-- Stage-independent coefficient controlling the central one-bond Heron
mixed-covariance error. -/
def bulkSourceCentralHeronResidualCoefficient (m : Nat) : Q' :=
  let width := bulkSourceWidth (4 * m)
  let coordinateCount :=
    historyCoordinateCount 1 (combGaugeEdgeCount width)
  let data := combGaugeFreeHistoryCovariancePositiveLDL 1 width
  let faceIndex :=
    bulkSourceInternalFaceIndex (4 * m) (bulkSourceCentralFaceIndex m)
  physicalCovarianceBilinearResidualEnvelope coordinateCount
    (ldlFactorResidualCoefficient coordinateCount
      data.lower data.diagonal)
    (combGaugeFreeHistoryCurlRow width 0 faceIndex)
    (combGaugeFreeHistoryCurlRow width 1 faceIndex)

/-- Staged rational mixed covariance of the selected central bulk face. -/
def bulkSourceCentralHeronMixedCovariance
    (m stage : Nat) : Q' :=
  let width := bulkSourceWidth (4 * m)
  let coordinateCount :=
    historyCoordinateCount 1 (combGaugeEdgeCount width)
  let faceIndex :=
    bulkSourceInternalFaceIndex (4 * m) (bulkSourceCentralFaceIndex m)
  physicalCovarianceBilinear coordinateCount coordinateCount
    (combGaugeFreeHistoryHeronTransform 1 width stage)
    (combGaugeFreeHistoryCurlRow width 0 faceIndex)
    (combGaugeFreeHistoryCurlRow width 1 faceIndex)

theorem bulkSourceCentralHeronResidualEnvelope_eq
    (m stage : Nat) :
    combGaugeFreeHistoryHeronBilinearResidualEnvelope
        1 (bulkSourceWidth (4 * m)) stage
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m)))
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 1
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m))) ≈
      bulkSourceCentralHeronResidualCoefficient m *
        HalfPow.half ^ stage := by
  unfold combGaugeFreeHistoryHeronBilinearResidualEnvelope
    bulkSourceCentralHeronResidualCoefficient
  exact physicalResidualEnvelope_eq_coefficient_mul_half
    (historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))) stage
    (ldlFactorResidualEnvelope
      (historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m))))
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth (4 * m))).lower
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth (4 * m))).diagonal
      stage)
    (ldlFactorResidualCoefficient
      (historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m))))
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth (4 * m))).lower
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth (4 * m))).diagonal)
    _ _
    (fun left right =>
      ldlFactorResidualEnvelope_eq_coefficient_mul_half
        (historyCoordinateCount 1
          (combGaugeEdgeCount (bulkSourceWidth (4 * m))))
        (combGaugeFreeHistoryCovariancePositiveLDL
          1 (bulkSourceWidth (4 * m))).lower
        (combGaugeFreeHistoryCovariancePositiveLDL
          1 (bulkSourceWidth (4 * m))).diagonal
        stage left right)

theorem bulkSourceCentralHeronResidualCoefficient_nonnegative
    (m : Nat) :
    (0 : Q') ≤ bulkSourceCentralHeronResidualCoefficient m := by
  unfold bulkSourceCentralHeronResidualCoefficient
    physicalCovarianceBilinearResidualEnvelope
  simp only [qListSum_map_eq_listQSum_local]
  apply listQSum_nonnegative_on
  intro left hleft
  apply listQSum_nonnegative_on
  intro right hright
  apply Q'.mul_nonneg
  · exact Q'.abs_nonneg _
  · unfold ldlFactorResidualCoefficient
    apply listQSum_nonnegative_on
    intro k hk
    apply Q'.mul_nonneg
    · exact errAt_nonneg
        ((combGaugeFreeHistoryCovariancePositiveLDL
          1 (bulkSourceWidth (4 * m))).diagonal k)
        (finiteLDLPositiveDiagonalCheck_pos
          (combGaugeFreeHistoryCovariancePositiveLDL_diagonal_check
            1 (bulkSourceWidth (4 * m)))
          (List.mem_range.mp hk)) 0
    · exact Q'.abs_nonneg _

/-- Explicit side-dependent stage at which the central mixed covariance
retains half of its exact positive value. -/
def bulkSourceCentralPositiveHeronStage (m : Nat) : Nat :=
  geoOuterModulus
    (HalfPow.half * bulkSourceCentralHeronResidualCoefficient m)
    (HalfPow.half * bulkSourceCentralOneBondCovariance m)

theorem bulkSourceCentralHeronResidualEnvelope_le_half
    (m : Nat) (hm : 0 < m) :
    combGaugeFreeHistoryHeronBilinearResidualEnvelope
        1 (bulkSourceWidth (4 * m))
        (bulkSourceCentralPositiveHeronStage m)
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m)))
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 1
          (bulkSourceInternalFaceIndex (4 * m)
            (bulkSourceCentralFaceIndex m))) ≤
      HalfPow.half * bulkSourceCentralOneBondCovariance m := by
  let coefficient := bulkSourceCentralHeronResidualCoefficient m
  let exactMixed := bulkSourceCentralOneBondCovariance m
  let amplitude := HalfPow.half * coefficient
  let tolerance := HalfPow.half * exactMixed
  have hcoefficient : (0 : Q') ≤ coefficient :=
    bulkSourceCentralHeronResidualCoefficient_nonnegative m
  have hamplitude : (0 : Q') ≤ amplitude :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg hcoefficient
  have htolerance : (0 : Q') < tolerance :=
    ExpNeg.half_mul_pos exactMixed
      (bulkSourceCentralOneBondCovariance_pos m hm)
  have htail := geoTail_le_of_modulus amplitude hamplitude
    tolerance htolerance (bulkSourceCentralPositiveHeronStage m)
    (Nat.le_refl (bulkSourceCentralPositiveHeronStage m))
  have henvelope :
      combGaugeFreeHistoryHeronBilinearResidualEnvelope
          1 (bulkSourceWidth (4 * m))
          (bulkSourceCentralPositiveHeronStage m)
          (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
            (bulkSourceInternalFaceIndex (4 * m)
              (bulkSourceCentralFaceIndex m)))
          (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 1
            (bulkSourceInternalFaceIndex (4 * m)
              (bulkSourceCentralFaceIndex m))) ≈
        geoTail amplitude (bulkSourceCentralPositiveHeronStage m) := by
    refine Q'.eqv_trans _ _ _
      (bulkSourceCentralHeronResidualEnvelope_eq
        m (bulkSourceCentralPositiveHeronStage m)) ?_
    unfold amplitude coefficient geoTail
    have hamplitudeEq :
        (Q'.ofNat 2 *
            (HalfPow.half *
              bulkSourceCentralHeronResidualCoefficient m)) ≈
          bulkSourceCentralHeronResidualCoefficient m := by
      refine Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.const 2) (.mul (.var 0) (.var 1)))
          (.add (.mul (.var 0) (.var 1))
            (.mul (.var 0) (.var 1)))
          (by decide) (fun
            | 0 => HalfPow.half
            | _ => bulkSourceCentralHeronResidualCoefficient m)) ?_
      exact ExpNeg.two_halves
        (bulkSourceCentralHeronResidualCoefficient m)
    exact Q'.eqv_symm
      (Q'.mul_eqv_congr_right _ _
        (HalfPow.half ^ bulkSourceCentralPositiveHeronStage m) hamplitudeEq)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv henvelope) htail

theorem bulkSourceCentralHeronMixedCovariance_ge_half
    (m : Nat) (hm : 0 < m) :
    HalfPow.half * bulkSourceCentralOneBondCovariance m ≤
      bulkSourceCentralHeronMixedCovariance
        m (bulkSourceCentralPositiveHeronStage m) := by
  let envelope :=
    combGaugeFreeHistoryHeronBilinearResidualEnvelope
      1 (bulkSourceWidth (4 * m))
      (bulkSourceCentralPositiveHeronStage m)
      (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
        (bulkSourceInternalFaceIndex (4 * m)
          (bulkSourceCentralFaceIndex m)))
      (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 1
        (bulkSourceInternalFaceIndex (4 * m)
          (bulkSourceCentralFaceIndex m)))
  have herror := combGaugeFreeHistoryHeronBilinear_error
    1 (bulkSourceWidth (4 * m))
    (bulkSourceCentralPositiveHeronStage m)
    (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0
      (bulkSourceInternalFaceIndex (4 * m)
        (bulkSourceCentralFaceIndex m)))
    (combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 1
      (bulkSourceInternalFaceIndex (4 * m)
        (bulkSourceCentralFaceIndex m)))
  have henvelope :
      envelope ≤ HalfPow.half * bulkSourceCentralOneBondCovariance m :=
    bulkSourceCentralHeronResidualEnvelope_le_half m hm
  have hwindow :
      HalfPow.half * bulkSourceCentralOneBondCovariance m + envelope ≤
        bulkSourceCentralOneBondCovariance m := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left
        (HalfPow.half * bulkSourceCentralOneBondCovariance m) envelope
        (HalfPow.half * bulkSourceCentralOneBondCovariance m)
        henvelope) ?_
    exact Q'.le_of_eqv
      (ExpNeg.two_halves (bulkSourceCentralOneBondCovariance m))
  exact lower_of_abs_remainder_local herror hwindow

theorem bulkSourceCentralHeronMixedCovariance_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceCentralHeronMixedCovariance
      m (bulkSourceCentralPositiveHeronStage m) := by
  exact Q'.pos_of_lt_of_le
    (ExpNeg.half_mul_pos _
      (bulkSourceCentralOneBondCovariance_pos m hm))
    (bulkSourceCentralHeronMixedCovariance_ge_half m hm)

/-- The selected central color-zero row Gram is the staged central mixed
covariance. -/
theorem bulkSourceCentralHeronColorGram_eqv_mixed
    (m stage : Nat) :
    let coordinateCount :=
      historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
    let rowIndex := bulkSourceCentralFaceIndex m * 3
    finiteRowGram
        (coordinateCount + (coordinateCount + coordinateCount))
        (bulkSourceHeronColorCurlRow 1 (4 * m) stage 0 rowIndex)
        (bulkSourceHeronColorCurlRow 1 (4 * m) stage 1 rowIndex) ≈
      bulkSourceCentralHeronMixedCovariance m stage := by
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  let transform :=
    combGaugeFreeHistoryHeronTransform 1
      (bulkSourceWidth (4 * m)) stage
  let faceIndex :=
    bulkSourceInternalFaceIndex (4 * m) (bulkSourceCentralFaceIndex m)
  let lowerRow :=
    combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 0 faceIndex
  let upperRow :=
    combGaugeFreeHistoryCurlRow (bulkSourceWidth (4 * m)) 1 faceIndex
  have hcolor := finiteRowGram_threeColorRows coordinateCount 0 0
    (pulledRow coordinateCount transform lowerRow)
    (pulledRow coordinateCount transform upperRow)
    (by decide) (by decide)
  have hcolor' :
      finiteRowGram
          (coordinateCount + (coordinateCount + coordinateCount))
          (threeColorRows coordinateCount
            (pulledRow coordinateCount transform lowerRow) 0)
          (threeColorRows coordinateCount
            (pulledRow coordinateCount transform upperRow) 0) ≈
        finiteRowGram coordinateCount
          (pulledRow coordinateCount transform lowerRow)
          (pulledRow coordinateCount transform upperRow) := by
    simpa using hcolor
  have hpull := finiteRowGram_pulledRow
    coordinateCount coordinateCount transform lowerRow upperRow
  have hgram := Q'.eqv_trans _ _ _ hcolor' hpull
  have hdiv : bulkSourceCentralFaceIndex m * 3 / 3 =
      bulkSourceCentralFaceIndex m := by omega
  have hmod : bulkSourceCentralFaceIndex m * 3 % 3 = 0 := by omega
  have hlowerColor :
      bulkSourceHeronColorCurlRow 1 (4 * m) stage 0
          (bulkSourceCentralFaceIndex m * 3) =
        threeColorRows coordinateCount
          (pulledRow coordinateCount transform lowerRow) 0 := by
    funext coordinate
    unfold bulkSourceHeronColorCurlRow
      combGaugeFreeHistoryHeronColorCurlRow
    rw [hdiv, hmod]
  have hupperColor :
      bulkSourceHeronColorCurlRow 1 (4 * m) stage 1
          (bulkSourceCentralFaceIndex m * 3) =
        threeColorRows coordinateCount
          (pulledRow coordinateCount transform upperRow) 0 := by
    funext coordinate
    unfold bulkSourceHeronColorCurlRow
      combGaugeFreeHistoryHeronColorCurlRow
    rw [hdiv, hmod]
  dsimp only
  rw [hlowerColor, hupperColor]
  simpa [
    bulkSourceCentralHeronMixedCovariance,
    coordinateCount, transform, faceIndex, lowerRow, upperRow,
    hdiv, hmod] using hgram

/-- Complete weighted source-time row Gram trace at the central-positive
Heron stage. -/
def bulkSourceCentralPositiveHeronWeightedRowGramTrace
    (m : Nat) (hm : 0 < m) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  finiteWeightedRowGramTrace
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * (bulkSourceFaces (4 * m)).length)
    (fun rowIndex => bulkSourceIndexWeight (4 * m)
      (Nat.mul_pos (by decide) hm) (rowIndex / 3))
    (bulkSourceHeronColorCurlRow
      1 (4 * m) (bulkSourceCentralPositiveHeronStage m) 0)

/-- Explicit central contribution retained by the weighted source-time row
Gram trace. -/
def bulkSourceCentralPositiveHeronRowTraceFloor
    (m : Nat) (hm : 0 < m) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  let rowIndex := bulkSourceCentralFaceIndex m * 3
  bulkSourceIndexWeight (4 * m) (Nat.mul_pos (by decide) hm)
      (rowIndex / 3) *
    finiteRowNorm2
      (coordinateCount + (coordinateCount + coordinateCount))
      (bulkSourceHeronColorCurlRow
        1 (4 * m) (bulkSourceCentralPositiveHeronStage m) 0 rowIndex)

theorem bulkSourceCentralPositiveHeronRowTraceFloor_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceCentralPositiveHeronRowTraceFloor m hm := by
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  let rowIndex := bulkSourceCentralFaceIndex m * 3
  have hfaceIndex := bulkSourceCentralFaceIndex_lt m hm
  have hdiv : rowIndex / 3 = bulkSourceCentralFaceIndex m := by
    unfold rowIndex
    omega
  have hweight :
      (0 : Q') < bulkSourceIndexWeight (4 * m)
        (Nat.mul_pos (by decide) hm) (rowIndex / 3) := by
    rw [hdiv]
    exact bulkSourceIndexWeight_pos
      (Nat.mul_pos (by decide) hm) hfaceIndex
  have hgramEq := bulkSourceCentralHeronColorGram_eqv_mixed
    m (bulkSourceCentralPositiveHeronStage m)
  have hgram :
      (0 : Q') <
        finiteRowGram
          (coordinateCount + (coordinateCount + coordinateCount))
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 0 rowIndex)
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 1 rowIndex) :=
    Q'.pos_of_lt_of_le
      (bulkSourceCentralHeronMixedCovariance_pos m hm)
      (Q'.ge_of_eqv hgramEq)
  have hnorm :
      (0 : Q') <
        finiteRowNorm2
          (coordinateCount + (coordinateCount + coordinateCount))
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 0 rowIndex) :=
    finiteRowNorm2_pos_of_finiteRowGram_pos _ _ _ hgram
  unfold bulkSourceCentralPositiveHeronRowTraceFloor
  dsimp only
  exact Q'.mul_pos hweight hnorm

theorem bulkSourceCentralPositiveHeronRowTraceFloor_le
    (m : Nat) (hm : 0 < m) :
    bulkSourceCentralPositiveHeronRowTraceFloor m hm ≤
      bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm := by
  let rowIndex := bulkSourceCentralFaceIndex m * 3
  have hfaceIndex := bulkSourceCentralFaceIndex_lt m hm
  have hrowIndex : rowIndex < 3 * (bulkSourceFaces (4 * m)).length := by
    unfold rowIndex
    omega
  unfold bulkSourceCentralPositiveHeronRowTraceFloor
    bulkSourceCentralPositiveHeronWeightedRowGramTrace
  dsimp only
  apply finiteWeightedRowGramTrace_member_le
    (rowIndex := rowIndex)
  · exact List.mem_range.mpr hrowIndex
  · intro index hindex
    apply Q'.le_of_lt
    apply bulkSourceIndexWeight_pos (Nat.mul_pos (by decide) hm)
    have hindexBound := List.mem_range.mp hindex
    omega

/-- The central row floor retains the uniform `3^(-18)` coefficient factor;
the staged row norm is the remaining side-dependent quantity. -/
theorem bulkCoefficientFloor_mul_centralHeronRowNorm_le_floor
    (m : Nat) (hm : 0 < m) :
    let coordinateCount :=
      historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
    let rowIndex := bulkSourceCentralFaceIndex m * 3
    bulkCoefficientFloor *
        finiteRowNorm2
          (coordinateCount + (coordinateCount + coordinateCount))
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 0 rowIndex) ≤
      bulkSourceCentralPositiveHeronRowTraceFloor m hm := by
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  let rowIndex := bulkSourceCentralFaceIndex m * 3
  have hdiv : rowIndex / 3 = bulkSourceCentralFaceIndex m := by
    unfold rowIndex
    omega
  have hnorm :
      (0 : Q') ≤
        finiteRowNorm2
          (coordinateCount + (coordinateCount + coordinateCount))
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 0 rowIndex) :=
    finiteRowNorm2_nonnegative_local _ _
  unfold bulkSourceCentralPositiveHeronRowTraceFloor
  dsimp only
  rw [hdiv]
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (bulkSourceCentralIndexWeight_floor m hm) hnorm

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage.bulkSourceCentralHeronResidualCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage.bulkSourceCentralHeronResidualEnvelope_le_half
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage.bulkSourceCentralHeronMixedCovariance_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage.bulkSourceCentralHeronColorGram_eqv_mixed
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage.bulkSourceCentralPositiveHeronRowTraceFloor_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage.bulkSourceCentralPositiveHeronRowTraceFloor_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage.bulkCoefficientFloor_mul_centralHeronRowNorm_le_floor
