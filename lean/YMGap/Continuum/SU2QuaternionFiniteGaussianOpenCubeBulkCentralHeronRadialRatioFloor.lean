/-
# Central-stage finite radial ratio floor for the open-cube bulk source

The central-positive Heron stage supplies a positive color-zero cross Gram
for the selected central face.  This leaf retains its square in the complete
weighted cross-Gram trace, constructs the corresponding positive radial
denominator and normalized sixth-order ratio, and reuses the exact weighted
sixth-moment decomposition to bound that ratio below by twice the complete
source-time row trace.

The selected central row then gives an explicit positive ratio floor whose
source coefficient is uniformly bounded below by `3^(-18)`.  The remaining
staged row norm and exact covariance are side-dependent.  No cutoff-uniform
row-norm estimate, original-law comparison, continuum limit, Hamiltonian gap,
or Clay theorem is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage
import YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralCrossCovarianceFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-- The full weighted cross-Gram-square trace is positive at the selected
central Heron stage because it contains the positive central color-zero
square. -/
theorem bulkSourceCentralPositiveHeronCrossGramSquareTrace_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceHeronCrossGramSquareTrace
      1 (4 * m) (Nat.mul_pos (by decide) hm)
      (bulkSourceCentralPositiveHeronStage m) 0 1 := by
  let rowIndex := bulkSourceCentralFaceIndex m * 3
  have hfaceIndex := bulkSourceCentralFaceIndex_lt m hm
  have hrowIndex : rowIndex < 3 * (bulkSourceFaces (4 * m)).length := by
    unfold rowIndex
    omega
  have hweight := bulkSourceIndexWeight_pos
    (Nat.mul_pos (by decide) hm) hfaceIndex
  have hgramEq := bulkSourceCentralHeronColorGram_eqv_mixed
    m (bulkSourceCentralPositiveHeronStage m)
  have hgramPos :
      (0 : Q') <
        finiteRowGram
          (historyCoordinateCount 1
              (combGaugeEdgeCount (bulkSourceWidth (4 * m))) +
            (historyCoordinateCount 1
                (combGaugeEdgeCount (bulkSourceWidth (4 * m))) +
              historyCoordinateCount 1
                (combGaugeEdgeCount (bulkSourceWidth (4 * m)))))
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 0 rowIndex)
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 1 rowIndex) :=
    Q'.pos_of_lt_of_le
      (bulkSourceCentralHeronMixedCovariance_pos m hm)
      (Q'.ge_of_eqv hgramEq)
  have hsummand :
      (0 : Q') < bulkSourceHeronCrossGramSummand
        (4 * m) (Nat.mul_pos (by decide) hm)
        (bulkSourceCentralPositiveHeronStage m) rowIndex rowIndex := by
    have hdiv : bulkSourceCentralFaceIndex m * 3 / 3 =
        bulkSourceCentralFaceIndex m := by omega
    unfold bulkSourceHeronCrossGramSummand rowIndex
    rw [hdiv]
    exact Q'.mul_pos
      (Q'.mul_pos hweight hweight)
      (Q'.mul_pos hgramPos hgramPos)
  have hinner :
      bulkSourceHeronCrossGramSummand
          (4 * m) (Nat.mul_pos (by decide) hm)
          (bulkSourceCentralPositiveHeronStage m) rowIndex rowIndex ≤
        listQSum
          (fun directionRow =>
            bulkSourceHeronCrossGramSummand
              (4 * m) (Nat.mul_pos (by decide) hm)
              (bulkSourceCentralPositiveHeronStage m)
              rowIndex directionRow)
          (List.range (3 * (bulkSourceFaces (4 * m)).length)) := by
    apply listQSum_member_le_nonnegative_local
    · intro directionRow hdirection
      exact bulkSourceHeronCrossGramSummand_nonnegative
        (Nat.mul_pos (by decide) hm) hrowIndex
        (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hrowIndex
  have houter :
      listQSum
          (fun directionRow =>
            bulkSourceHeronCrossGramSummand
              (4 * m) (Nat.mul_pos (by decide) hm)
              (bulkSourceCentralPositiveHeronStage m)
              rowIndex directionRow)
          (List.range (3 * (bulkSourceFaces (4 * m)).length)) ≤
        listQSum
          (fun sourceRow =>
            listQSum
              (fun directionRow =>
                bulkSourceHeronCrossGramSummand
                  (4 * m) (Nat.mul_pos (by decide) hm)
                  (bulkSourceCentralPositiveHeronStage m)
                  sourceRow directionRow)
              (List.range (3 * (bulkSourceFaces (4 * m)).length)))
          (List.range (3 * (bulkSourceFaces (4 * m)).length)) := by
    apply listQSum_member_le_nonnegative_local
    · intro sourceRow hsource
      apply listQSum_nonnegative_on
      intro directionRow hdirection
      exact bulkSourceHeronCrossGramSummand_nonnegative
        (Nat.mul_pos (by decide) hm)
        (List.mem_range.mp hsource) (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hrowIndex
  have hsum :
      bulkSourceHeronCrossGramSummand
          (4 * m) (Nat.mul_pos (by decide) hm)
          (bulkSourceCentralPositiveHeronStage m) rowIndex rowIndex ≤
        listQSum
          (fun sourceRow =>
            listQSum
              (fun directionRow =>
                bulkSourceHeronCrossGramSummand
                  (4 * m) (Nat.mul_pos (by decide) hm)
                  (bulkSourceCentralPositiveHeronStage m)
                  sourceRow directionRow)
              (List.range (3 * (bulkSourceFaces (4 * m)).length)))
          (List.range (3 * (bulkSourceFaces (4 * m)).length)) :=
    Q'.le_trans' _ _ _ hinner houter
  have htrace := bulkSourceHeronCrossGramSquareTrace_eq_sum
    (4 * m) (Nat.mul_pos (by decide) hm)
    (bulkSourceCentralPositiveHeronStage m)
  exact Q'.pos_of_lt_of_le hsummand
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv htrace))

/-- Positive quadratic radial covariance at the central-positive stage. -/
theorem bulkSourceCentralPositiveHeronRadialPairCovariance_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceHeronRadialPairCovariance
      1 (4 * m) (Nat.mul_pos (by decide) hm)
      (bulkSourceCentralPositiveHeronStage m) 0 1 := by
  have htraceIdentity := bulkSourceHeronRadialPairCovariance_trace
    1 (4 * m) (Nat.mul_pos (by decide) hm)
    (bulkSourceCentralPositiveHeronStage m) 0 1
  change bulkSourceHeronRadialPairCovariance
      1 (4 * m) (Nat.mul_pos (by decide) hm)
        (bulkSourceCentralPositiveHeronStage m) 0 1 ≈
    2 * bulkSourceHeronCrossGramSquareTrace
      1 (4 * m) (Nat.mul_pos (by decide) hm)
        (bulkSourceCentralPositiveHeronStage m) 0 1 at htraceIdentity
  exact Q'.pos_of_lt_of_le
    (Q'.mul_pos (by decide)
      (bulkSourceCentralPositiveHeronCrossGramSquareTrace_pos m hm))
    (Q'.ge_of_eqv htraceIdentity)

/-- Sixth-order radial covariance numerator at the central-positive stage. -/
def bulkSourceCentralPositiveHeronRadialNumerator
    (m : Nat) (hm : 0 < m) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  let stage := bulkSourceCentralPositiveHeronStage m
  let source := bulkSourceHeronRadialSquare
    1 (4 * m) (Nat.mul_pos (by decide) hm) stage 0
  let direction := bulkSourceHeronRadialSquare
    1 (4 * m) (Nat.mul_pos (by decide) hm) stage 1
  finiteGaussianCovariance
    (coordinateCount + (coordinateCount + coordinateCount))
    (polyMul source source) direction

/-- Positive radial denominator at the same central-positive stage. -/
def bulkSourceCentralPositiveHeronRadialDenominator
    (m : Nat) (hm : 0 < m) : Q' :=
  bulkSourceHeronRadialPairCovariance
    1 (4 * m) (Nat.mul_pos (by decide) hm)
    (bulkSourceCentralPositiveHeronStage m) 0 1

theorem bulkSourceCentralPositiveHeronRadialDenominator_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceCentralPositiveHeronRadialDenominator m hm :=
  bulkSourceCentralPositiveHeronRadialPairCovariance_pos m hm

/-- Exact normalized finite rational ratio at the central-positive stage. -/
def bulkSourceCentralPositiveHeronRadialRatio
    (m : Nat) (hm : 0 < m) : Q' :=
  Q'.divPos
    (bulkSourceCentralPositiveHeronRadialNumerator m hm)
    (bulkSourceCentralPositiveHeronRadialDenominator m hm)
    (bulkSourceCentralPositiveHeronRadialDenominator_pos m hm)

theorem le_bulkSourceCentralPositiveHeronRadialRatio_of_mul_le
    (m : Nat) (hm : 0 < m) {lower : Q'}
    (hbound : lower * bulkSourceCentralPositiveHeronRadialDenominator m hm ≤
      bulkSourceCentralPositiveHeronRadialNumerator m hm) :
    lower ≤ bulkSourceCentralPositiveHeronRadialRatio m hm := by
  unfold bulkSourceCentralPositiveHeronRadialRatio
  exact Q'.le_divPos_of_mul_le _ _ _ hbound

/-- Weighted cross-Gram-square trace at the central-positive stage. -/
def bulkSourceCentralPositiveHeronWeightedCrossGramSquareTrace
    (m : Nat) (hm : 0 < m) : Q' :=
  bulkSourceHeronCrossGramSquareTrace
    1 (4 * m) (Nat.mul_pos (by decide) hm)
    (bulkSourceCentralPositiveHeronStage m) 0 1

/-- Weighted Gram-sandwich trace at the central-positive stage. -/
def bulkSourceCentralPositiveHeronWeightedGramSandwichTrace
    (m : Nat) (hm : 0 < m) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
  finiteWeightedGramSandwichTrace
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * (bulkSourceFaces (4 * m)).length)
    (3 * (bulkSourceFaces (4 * m)).length)
    (fun rowIndex => bulkSourceIndexWeight (4 * m)
      (Nat.mul_pos (by decide) hm) (rowIndex / 3))
    (fun rowIndex => bulkSourceIndexWeight (4 * m)
      (Nat.mul_pos (by decide) hm) (rowIndex / 3))
    (bulkSourceHeronColorCurlRow
      1 (4 * m) (bulkSourceCentralPositiveHeronStage m) 0)
    (bulkSourceHeronColorCurlRow
      1 (4 * m) (bulkSourceCentralPositiveHeronStage m) 1)

/-- Exact weighted trace decomposition of the central-stage numerator. -/
theorem bulkSourceCentralPositiveHeronRadialNumerator_trace
    (m : Nat) (hm : 0 < m) :
    bulkSourceCentralPositiveHeronRadialNumerator m hm ≈
      8 * bulkSourceCentralPositiveHeronWeightedGramSandwichTrace m hm +
        4 * bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm *
          bulkSourceCentralPositiveHeronWeightedCrossGramSquareTrace m hm := by
  unfold bulkSourceCentralPositiveHeronRadialNumerator
    bulkSourceHeronRadialSquare
    combGaugeFreeHistoryHeronWeightedCurlRadialSquare
    bulkSourceCentralPositiveHeronWeightedGramSandwichTrace
    bulkSourceCentralPositiveHeronWeightedRowGramTrace
    bulkSourceCentralPositiveHeronWeightedCrossGramSquareTrace
    bulkSourceHeronCrossGramSquareTrace
    bulkSourceHeronColorCurlRow
  exact finiteGaussianWeightedRadialCovariance_trace
    (historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m))) +
      (historyCoordinateCount 1
          (combGaugeEdgeCount (bulkSourceWidth (4 * m))) +
        historyCoordinateCount 1
          (combGaugeEdgeCount (bulkSourceWidth (4 * m)))))
    (3 * (bulkSourceFaces (4 * m)).length)
    (3 * (bulkSourceFaces (4 * m)).length)
    (fun rowIndex => bulkSourceIndexWeight (4 * m)
      (Nat.mul_pos (by decide) hm) (rowIndex / 3))
    (fun rowIndex => bulkSourceIndexWeight (4 * m)
      (Nat.mul_pos (by decide) hm) (rowIndex / 3))
    (combGaugeFreeHistoryHeronColorCurlRow
      1 (bulkSourceWidth (4 * m)) (bulkSourceCentralPositiveHeronStage m)
      (fun _ => 0) (bulkSourceInternalFaceIndex (4 * m)))
    (combGaugeFreeHistoryHeronColorCurlRow
      1 (bulkSourceWidth (4 * m)) (bulkSourceCentralPositiveHeronStage m)
      (fun _ => 1) (bulkSourceInternalFaceIndex (4 * m)))

/-- The central-stage positive denominator is exactly twice the specialized
weighted cross-Gram-square trace. -/
theorem bulkSourceCentralPositiveHeronRadialDenominator_trace
    (m : Nat) (hm : 0 < m) :
    bulkSourceCentralPositiveHeronRadialDenominator m hm ≈
      2 * bulkSourceCentralPositiveHeronWeightedCrossGramSquareTrace m hm := by
  unfold bulkSourceCentralPositiveHeronRadialDenominator
    bulkSourceCentralPositiveHeronWeightedCrossGramSquareTrace
  exact bulkSourceHeronRadialPairCovariance_trace
    1 (4 * m) (Nat.mul_pos (by decide) hm)
    (bulkSourceCentralPositiveHeronStage m) 0 1

/-- Exact cleared numerator identity at the central-positive stage. -/
theorem bulkSourceCentralPositiveHeronRadialNumerator_cleared
    (m : Nat) (hm : 0 < m) :
    bulkSourceCentralPositiveHeronRadialNumerator m hm ≈
      8 * bulkSourceCentralPositiveHeronWeightedGramSandwichTrace m hm +
        2 * bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm *
          bulkSourceCentralPositiveHeronRadialDenominator m hm := by
  have hnumerator := bulkSourceCentralPositiveHeronRadialNumerator_trace m hm
  have hdenominator :=
    bulkSourceCentralPositiveHeronRadialDenominator_trace m hm
  exact Q'.eqv_trans _ _ _ hnumerator
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 0)) (.var 1))
          (.mul (.mul (.const 2) (.var 0))
            (.mul (.const 2) (.var 1)))
          (by decide) (fun
            | 0 => bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm
            | _ =>
                bulkSourceCentralPositiveHeronWeightedCrossGramSquareTrace m hm))
        (Q'.mul_eqv_congr_left
          (2 * bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm)
          (2 * bulkSourceCentralPositiveHeronWeightedCrossGramSquareTrace m hm)
          (bulkSourceCentralPositiveHeronRadialDenominator m hm)
          (Q'.eqv_symm hdenominator))))

theorem bulkSourceCentralPositiveHeronWeightedRowGramTrace_nonnegative
    (m : Nat) (hm : 0 < m) :
    (0 : Q') ≤ bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm := by
  unfold bulkSourceCentralPositiveHeronWeightedRowGramTrace
  apply finiteWeightedRowGramTrace_nonnegative
  intro rowIndex hrow
  apply Q'.le_of_lt
  apply bulkSourceIndexWeight_pos (Nat.mul_pos (by decide) hm)
  have hrowBound := List.mem_range.mp hrow
  omega

theorem bulkSourceCentralPositiveHeronWeightedGramSandwichTrace_nonnegative
    (m : Nat) (hm : 0 < m) :
    (0 : Q') ≤
      bulkSourceCentralPositiveHeronWeightedGramSandwichTrace m hm := by
  unfold bulkSourceCentralPositiveHeronWeightedGramSandwichTrace
  apply finiteWeightedGramSandwichTrace_nonnegative
  intro rowIndex hrow
  apply Q'.le_of_lt
  apply bulkSourceIndexWeight_pos (Nat.mul_pos (by decide) hm)
  have hrowBound := List.mem_range.mp hrow
  omega

theorem bulkSourceCentralPositiveHeronRowTrace_mul_denominator_le_numerator
    (m : Nat) (hm : 0 < m) :
    (2 * bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm) *
        bulkSourceCentralPositiveHeronRadialDenominator m hm ≤
      bulkSourceCentralPositiveHeronRadialNumerator m hm := by
  let base :=
    (2 * bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm) *
      bulkSourceCentralPositiveHeronRadialDenominator m hm
  let residual :=
    8 * bulkSourceCentralPositiveHeronWeightedGramSandwichTrace m hm
  have hresidual : (0 : Q') ≤ residual := by
    unfold residual
    exact Q'.mul_nonneg _ _ (by decide)
      (bulkSourceCentralPositiveHeronWeightedGramSandwichTrace_nonnegative m hm)
  have hbase : base ≤ residual + base := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg base residual hresidual)
      (Q'.le_of_eqv (Q'.add_comm_eqv base residual))
  have hcleared := bulkSourceCentralPositiveHeronRadialNumerator_cleared m hm
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hcleared)

theorem two_mul_bulkSourceCentralPositiveHeronWeightedRowGramTrace_le_ratio
    (m : Nat) (hm : 0 < m) :
    2 * bulkSourceCentralPositiveHeronWeightedRowGramTrace m hm ≤
      bulkSourceCentralPositiveHeronRadialRatio m hm :=
  le_bulkSourceCentralPositiveHeronRadialRatio_of_mul_le m hm
    (bulkSourceCentralPositiveHeronRowTrace_mul_denominator_le_numerator m hm)

theorem two_mul_bulkSourceCentralPositiveHeronRowTraceFloor_le_ratio
    (m : Nat) (hm : 0 < m) :
    2 * bulkSourceCentralPositiveHeronRowTraceFloor m hm ≤
      bulkSourceCentralPositiveHeronRadialRatio m hm := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (bulkSourceCentralPositiveHeronRowTraceFloor_le m hm)
      (by decide))
    (two_mul_bulkSourceCentralPositiveHeronWeightedRowGramTrace_le_ratio m hm)

/-- The normalized central-stage ratio retains the uniform `3^(-18)` source
coefficient factor.  The displayed row norm is still side-dependent. -/
theorem two_mul_bulkCoefficientFloor_mul_centralHeronRowNorm_le_ratio
    (m : Nat) (hm : 0 < m) :
    let coordinateCount :=
      historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth (4 * m)))
    let rowIndex := bulkSourceCentralFaceIndex m * 3
    2 * (bulkCoefficientFloor *
        finiteRowNorm2
          (coordinateCount + (coordinateCount + coordinateCount))
          (bulkSourceHeronColorCurlRow 1 (4 * m)
            (bulkSourceCentralPositiveHeronStage m) 0 rowIndex)) ≤
      bulkSourceCentralPositiveHeronRadialRatio m hm := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (bulkCoefficientFloor_mul_centralHeronRowNorm_le_floor m hm)
      (by decide))
    (two_mul_bulkSourceCentralPositiveHeronRowTraceFloor_le_ratio m hm)

theorem bulkSourceCentralPositiveHeronRadialRatio_pos
    (m : Nat) (hm : 0 < m) :
    (0 : Q') < bulkSourceCentralPositiveHeronRadialRatio m hm :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (by decide)
      (bulkSourceCentralPositiveHeronRowTraceFloor_pos m hm))
    (two_mul_bulkSourceCentralPositiveHeronRowTraceFloor_le_ratio m hm)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor.bulkSourceCentralPositiveHeronCrossGramSquareTrace_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor.bulkSourceCentralPositiveHeronRadialDenominator_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor.bulkSourceCentralPositiveHeronRadialNumerator_cleared
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor.bulkSourceCentralPositiveHeronWeightedGramSandwichTrace_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor.two_mul_bulkSourceCentralPositiveHeronWeightedRowGramTrace_le_ratio
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor.two_mul_bulkCoefficientFloor_mul_centralHeronRowNorm_le_ratio
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCentralHeronRadialRatioFloor.bulkSourceCentralPositiveHeronRadialRatio_pos
