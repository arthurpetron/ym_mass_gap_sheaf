/-
# Exact trace decomposition of the positive-stage bulk radial numerator

This leaf specializes the rationally weighted finite Gaussian sixth-covariance
identity to the actual open-cube bulk-source rows at the explicit positive
Heron stage.  It then replaces the weighted cross-Gram-square trace by the
already checked positive quadratic covariance denominator.

The result is an exact cleared numerator identity.  A sign or quantitative
estimate for the remaining weighted Gram-sandwich trace is still required
before it yields a lower or upper bound on the normalized ratio.  No original
interacting law, continuum limit, Hamiltonian gap, or Clay-facing conclusion
is asserted.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialRatio
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianWeightedRadialCovariance

local infix:50 " ≈ " => Q'.eqv

/-- Weighted source-time row Gram trace at the explicit positive Heron stage. -/
def bulkSourcePositiveHeronWeightedRowGramTrace
    (s : Nat) (hs : 0 < s) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  finiteWeightedRowGramTrace
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * (bulkSourceFaces s).length)
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (bulkSourceHeronColorCurlRow
      1 s (bulkSourcePositiveHeronStage s) 0)

/-- Weighted source/direction cross-Gram-square trace at the explicit positive
Heron stage. -/
def bulkSourcePositiveHeronWeightedCrossGramSquareTrace
    (s : Nat) (hs : 0 < s) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  finiteWeightedCrossGramSquareTrace
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * (bulkSourceFaces s).length)
    (3 * (bulkSourceFaces s).length)
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (bulkSourceHeronColorCurlRow
      1 s (bulkSourcePositiveHeronStage s) 0)
    (bulkSourceHeronColorCurlRow
      1 s (bulkSourcePositiveHeronStage s) 1)

/-- Weighted three-row Gram-sandwich trace remaining in the exact sixth-order
numerator decomposition. -/
def bulkSourcePositiveHeronWeightedGramSandwichTrace
    (s : Nat) (hs : 0 < s) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  finiteWeightedGramSandwichTrace
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * (bulkSourceFaces s).length)
    (3 * (bulkSourceFaces s).length)
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (bulkSourceHeronColorCurlRow
      1 s (bulkSourcePositiveHeronStage s) 0)
    (bulkSourceHeronColorCurlRow
      1 s (bulkSourcePositiveHeronStage s) 1)

/-- Exact weighted trace decomposition of the literal sixth-order bulk radial
numerator. -/
theorem bulkSourcePositiveHeronRadialNumerator_trace
    (s : Nat) (hs : 0 < s) :
    bulkSourcePositiveHeronRadialNumerator s hs ≈
      8 * bulkSourcePositiveHeronWeightedGramSandwichTrace s hs +
        4 * bulkSourcePositiveHeronWeightedRowGramTrace s hs *
          bulkSourcePositiveHeronWeightedCrossGramSquareTrace s hs := by
  unfold bulkSourcePositiveHeronRadialNumerator
    bulkSourceHeronRadialSquare
    combGaugeFreeHistoryHeronWeightedCurlRadialSquare
    bulkSourcePositiveHeronWeightedGramSandwichTrace
    bulkSourcePositiveHeronWeightedRowGramTrace
    bulkSourcePositiveHeronWeightedCrossGramSquareTrace
    bulkSourceHeronColorCurlRow
  exact finiteGaussianWeightedRadialCovariance_trace
    (historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth s)) +
      (historyCoordinateCount 1
          (combGaugeEdgeCount (bulkSourceWidth s)) +
        historyCoordinateCount 1
          (combGaugeEdgeCount (bulkSourceWidth s))))
    (3 * (bulkSourceFaces s).length)
    (3 * (bulkSourceFaces s).length)
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (fun rowIndex => bulkSourceIndexWeight s hs (rowIndex / 3))
    (combGaugeFreeHistoryHeronColorCurlRow
      1 (bulkSourceWidth s) (bulkSourcePositiveHeronStage s)
      (fun _ => 0) (bulkSourceInternalFaceIndex s))
    (combGaugeFreeHistoryHeronColorCurlRow
      1 (bulkSourceWidth s) (bulkSourcePositiveHeronStage s)
      (fun _ => 1) (bulkSourceInternalFaceIndex s))

/-- The positive quadratic denominator is exactly twice the specialized
weighted cross-Gram-square trace. -/
theorem bulkSourcePositiveHeronRadialDenominator_trace
    (s : Nat) (hs : 0 < s) :
    bulkSourcePositiveHeronRadialDenominator s hs ≈
      2 * bulkSourcePositiveHeronWeightedCrossGramSquareTrace s hs := by
  unfold bulkSourcePositiveHeronRadialDenominator
    bulkSourcePositiveHeronWeightedCrossGramSquareTrace
    bulkSourceHeronRadialPairCovariance
    bulkSourceHeronColorCurlRow
  exact bulkSourceHeronRadialPairCovariance_trace
    1 s hs (bulkSourcePositiveHeronStage s) 0 1

/-- Exact cleared numerator identity using the actual strictly positive
denominator.  The weighted Gram-sandwich trace is the remaining term requiring
a sign or quantitative bound. -/
theorem bulkSourcePositiveHeronRadialNumerator_cleared
    (s : Nat) (hs : 0 < s) :
    bulkSourcePositiveHeronRadialNumerator s hs ≈
      8 * bulkSourcePositiveHeronWeightedGramSandwichTrace s hs +
        2 * bulkSourcePositiveHeronWeightedRowGramTrace s hs *
          bulkSourcePositiveHeronRadialDenominator s hs := by
  have hnumerator := bulkSourcePositiveHeronRadialNumerator_trace s hs
  have hdenominator := bulkSourcePositiveHeronRadialDenominator_trace s hs
  exact Q'.eqv_trans _ _ _ hnumerator
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 4) (.var 0)) (.var 1))
          (.mul (.mul (.const 2) (.var 0))
            (.mul (.const 2) (.var 1)))
          (by decide) (fun
            | 0 => bulkSourcePositiveHeronWeightedRowGramTrace s hs
            | _ => bulkSourcePositiveHeronWeightedCrossGramSquareTrace s hs))
        (Q'.mul_eqv_congr_left
          (2 * bulkSourcePositiveHeronWeightedRowGramTrace s hs)
          (2 * bulkSourcePositiveHeronWeightedCrossGramSquareTrace s hs)
          (bulkSourcePositiveHeronRadialDenominator s hs)
          (Q'.eqv_symm hdenominator))))

/-- The specialized weighted row Gram trace is nonnegative. -/
theorem bulkSourcePositiveHeronWeightedRowGramTrace_nonnegative
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ bulkSourcePositiveHeronWeightedRowGramTrace s hs := by
  unfold bulkSourcePositiveHeronWeightedRowGramTrace
  apply finiteWeightedRowGramTrace_nonnegative
  intro rowIndex hrow
  apply Q'.le_of_lt
  apply bulkSourceIndexWeight_pos hs
  have hrowBound := List.mem_range.mp hrow
  omega

/-- The remaining weighted Gram-sandwich trace is a constructive finite sum of
squares and is therefore nonnegative. -/
theorem bulkSourcePositiveHeronWeightedGramSandwichTrace_nonnegative
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ bulkSourcePositiveHeronWeightedGramSandwichTrace s hs := by
  unfold bulkSourcePositiveHeronWeightedGramSandwichTrace
  apply finiteWeightedGramSandwichTrace_nonnegative
  intro rowIndex hrow
  apply Q'.le_of_lt
  apply bulkSourceIndexWeight_pos hs
  have hrowBound := List.mem_range.mp hrow
  omega

/-- Explicit positive lower-face contribution retained by the weighted
source-time row Gram trace. -/
def bulkSourcePositiveHeronLowerFaceRowTraceFloor
    (s : Nat) (hs : 0 < s) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  let rowIndex := bulkSourceLowerFaceIndex s * 3
  bulkSourceIndexWeight s hs (rowIndex / 3) *
    finiteRowNorm2
      (coordinateCount + (coordinateCount + coordinateCount))
      (bulkSourceHeronColorCurlRow
        1 s (bulkSourcePositiveHeronStage s) 0 rowIndex)

theorem bulkSourcePositiveHeronLowerFaceRowTraceFloor_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourcePositiveHeronLowerFaceRowTraceFloor s hs := by
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  let rowIndex := bulkSourceLowerFaceIndex s * 3
  have hfaceIndex := bulkSourceLowerFaceIndex_lt s hs
  have hdiv : rowIndex / 3 = bulkSourceLowerFaceIndex s := by
    unfold rowIndex
    omega
  have hweight :
      (0 : Q') < bulkSourceIndexWeight s hs (rowIndex / 3) := by
    rw [hdiv]
    exact bulkSourceIndexWeight_pos hs hfaceIndex
  have hgramEq := bulkSourceLowerFaceHeronColorGram_eqv_mixed
    s (bulkSourcePositiveHeronStage s)
  have hgram :
      (0 : Q') <
        finiteRowGram
          (coordinateCount + (coordinateCount + coordinateCount))
          (bulkSourceHeronColorCurlRow 1 s
            (bulkSourcePositiveHeronStage s) 0 rowIndex)
          (bulkSourceHeronColorCurlRow 1 s
            (bulkSourcePositiveHeronStage s) 1 rowIndex) :=
    Q'.pos_of_lt_of_le
      (bulkSourceLowerFaceHeronMixedCovariance_pos s hs)
      (Q'.ge_of_eqv hgramEq)
  have hnorm :
      (0 : Q') <
        finiteRowNorm2
          (coordinateCount + (coordinateCount + coordinateCount))
          (bulkSourceHeronColorCurlRow 1 s
            (bulkSourcePositiveHeronStage s) 0 rowIndex) :=
    finiteRowNorm2_pos_of_finiteRowGram_pos _ _ _ hgram
  unfold bulkSourcePositiveHeronLowerFaceRowTraceFloor
  dsimp only
  exact Q'.mul_pos hweight hnorm

theorem bulkSourcePositiveHeronLowerFaceRowTraceFloor_le
    (s : Nat) (hs : 0 < s) :
    bulkSourcePositiveHeronLowerFaceRowTraceFloor s hs ≤
      bulkSourcePositiveHeronWeightedRowGramTrace s hs := by
  let rowIndex := bulkSourceLowerFaceIndex s * 3
  have hfaceIndex := bulkSourceLowerFaceIndex_lt s hs
  have hrowIndex : rowIndex < 3 * (bulkSourceFaces s).length := by
    unfold rowIndex
    omega
  unfold bulkSourcePositiveHeronLowerFaceRowTraceFloor
    bulkSourcePositiveHeronWeightedRowGramTrace
  dsimp only
  apply finiteWeightedRowGramTrace_member_le
    (rowIndex := rowIndex)
  · exact List.mem_range.mpr hrowIndex
  · intro index hindex
    apply Q'.le_of_lt
    apply bulkSourceIndexWeight_pos hs
    have hindexBound := List.mem_range.mp hindex
    omega

/-- The row-trace contribution times the actual positive denominator is a
cleared lower bound for the literal sixth-order numerator. -/
theorem bulkSourcePositiveHeronRowTrace_mul_denominator_le_numerator
    (s : Nat) (hs : 0 < s) :
    (2 * bulkSourcePositiveHeronWeightedRowGramTrace s hs) *
        bulkSourcePositiveHeronRadialDenominator s hs ≤
      bulkSourcePositiveHeronRadialNumerator s hs := by
  let base := (2 * bulkSourcePositiveHeronWeightedRowGramTrace s hs) *
    bulkSourcePositiveHeronRadialDenominator s hs
  let residual := 8 * bulkSourcePositiveHeronWeightedGramSandwichTrace s hs
  have hresidual : (0 : Q') ≤ residual := by
    unfold residual
    exact Q'.mul_nonneg _ _ (by decide)
      (bulkSourcePositiveHeronWeightedGramSandwichTrace_nonnegative s hs)
  have hbase : base ≤ residual + base := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg base residual hresidual)
      (Q'.le_of_eqv (Q'.add_comm_eqv base residual))
  have hcleared := bulkSourcePositiveHeronRadialNumerator_cleared s hs
  exact Q'.le_trans' _ _ _ hbase (Q'.ge_of_eqv hcleared)

/-- Exact positive-denominator transport gives a finite Gaussian ratio lower
bound by twice the weighted source-time row Gram trace. -/
theorem two_mul_bulkSourcePositiveHeronWeightedRowGramTrace_le_ratio
    (s : Nat) (hs : 0 < s) :
    2 * bulkSourcePositiveHeronWeightedRowGramTrace s hs ≤
      bulkSourcePositiveHeronRadialRatio s hs :=
  le_bulkSourcePositiveHeronRadialRatio_of_mul_le s hs
    (bulkSourcePositiveHeronRowTrace_mul_denominator_le_numerator s hs)

/-- The selected positive lower-face row gives an explicit side-dependent
strictly positive lower bound for the finite Gaussian radial ratio. -/
theorem two_mul_bulkSourcePositiveHeronLowerFaceRowTraceFloor_le_ratio
    (s : Nat) (hs : 0 < s) :
    2 * bulkSourcePositiveHeronLowerFaceRowTraceFloor s hs ≤
      bulkSourcePositiveHeronRadialRatio s hs := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (bulkSourcePositiveHeronLowerFaceRowTraceFloor_le s hs)
      (by decide))
    (two_mul_bulkSourcePositiveHeronWeightedRowGramTrace_le_ratio s hs)

theorem bulkSourcePositiveHeronRadialRatio_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourcePositiveHeronRadialRatio s hs :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (by decide)
      (bulkSourcePositiveHeronLowerFaceRowTraceFloor_pos s hs))
    (two_mul_bulkSourcePositiveHeronLowerFaceRowTraceFloor_le_ratio s hs)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronRadialNumerator_trace
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronRadialDenominator_trace
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronRadialNumerator_cleared
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronWeightedRowGramTrace_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronWeightedGramSandwichTrace_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronLowerFaceRowTraceFloor_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronLowerFaceRowTraceFloor_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronRowTrace_mul_denominator_le_numerator
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.two_mul_bulkSourcePositiveHeronWeightedRowGramTrace_le_ratio
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.two_mul_bulkSourcePositiveHeronLowerFaceRowTraceFloor_le_ratio
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronRadialNumeratorTrace.bulkSourcePositiveHeronRadialRatio_pos
