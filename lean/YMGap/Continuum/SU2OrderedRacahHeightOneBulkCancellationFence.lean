/-
# A closed strict-bulk height-one cancellation fence

The first closed physical block satisfying every strict hypothesis of the
final residual factorization has zero residual scalar and nonzero common
carrier.  This is an exact kernel computation over the derived rational
formula, not numerical sampling.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial

namespace YMGap.Continuum.SU2OrderedRacahHeightOneBulkCancellationFence

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahInnerContractionReduction
open YMGap.Continuum.SU2OrderedRacahOmegaExchangeBoundarySubstitution
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneExactResidualPolynomial

local infix:50 " ≈ " => Q'.eqv

/-- Lower channel of the first strict-bulk fence. -/
def heightOneBulkFenceLower : FixedRightCGChannel 8 8 8 6 where
  p := 4
  p_le := by decide
  r := 5
  r_le := by decide
  degree_eq := by decide

/-- Middle channel of the first strict-bulk fence. -/
def heightOneBulkFenceMiddle : FixedRightCGChannel 8 8 8 6 where
  p := 5
  p_le := by decide
  r := 4
  r_le := by decide
  degree_eq := by decide

/-- Upper channel of the first strict-bulk fence. -/
def heightOneBulkFenceUpper : FixedRightCGChannel 8 8 8 6 where
  p := 6
  p_le := by decide
  r := 3
  r_le := by decide
  degree_eq := by decide

/-- The fence genuinely meets the strict height-one bulk hypotheses. -/
theorem height_one_bulk_fence_physical_data :
    heightOneBulkFenceMiddle.p = heightOneBulkFenceLower.p + 1 ∧
    heightOneBulkFenceUpper.p = heightOneBulkFenceMiddle.p + 1 ∧
    0 < heightOneBulkFenceMiddle.p ∧
    3 + 3 = heightOneBulkFenceMiddle.p + 1 ∧
    heightOneBulkFenceMiddle.p + 2 ≤ 8 ∧
    4 ≤ heightOneBulkFenceMiddle.r ∧
    heightOneBulkFenceMiddle.r + 1 ≤ 5 ∧
    heightOneBulkFenceMiddle.r + 2 ≤
      heightOneBulkFenceMiddle.intermediate := by
  decide

/-- Exact all-formula residual cancellation in the fence block. -/
theorem height_one_bulk_fence_residual_scalar_zero :
    heightOneBulkResidualScalar heightOneBulkFenceMiddle 5 3 3 ≈ 0 := by
  decide

/-- The common carrier is nonzero, so the cancellation is not vacuous. -/
theorem height_one_bulk_fence_base_nonzero :
    ¬ (heightOneBulkResidualBase heightOneBulkFenceMiddle 5 3 3 ≈ 0) := by
  decide

/-- The complete correction defect cancels at the strict-bulk fence. -/
theorem height_one_bulk_fence_full_correction :
    omegaExchangeCorrection 8 8 8
          (fun u v w => rightShellFactorialCoefficient
            (reducePositiveInnerRightChannel heightOneBulkFenceMiddle
              (by decide)) u v w) 5 3 3 +
        -((omegaCorrectionLowerCoefficient 8 8 8 6
                heightOneBulkFenceMiddle.p *
              rightShellFactorialCoefficient heightOneBulkFenceLower 5 3 3 +
            omegaCorrectionDiagonalCoefficient 8 8 8 6
                heightOneBulkFenceMiddle.p *
              rightShellFactorialCoefficient heightOneBulkFenceMiddle 5 3 3) +
          omegaCorrectionUpperCoefficient 8 8 8 6
              heightOneBulkFenceMiddle.p *
            rightShellFactorialCoefficient heightOneBulkFenceUpper 5 3 3) ≈ 0 := by
  have hfactor := height_one_full_correction_exact_residual
    heightOneBulkFenceLower heightOneBulkFenceMiddle heightOneBulkFenceUpper
      (by decide) (by decide) (by decide) 5 3 3 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine Q'.eqv_trans _
    (heightOneBulkResidualBase heightOneBulkFenceMiddle 5 3 3 * 0) _
    (Q'.eqv_trans _
      (heightOneBulkResidualBase heightOneBulkFenceMiddle 5 3 3 *
        heightOneBulkResidualScalar heightOneBulkFenceMiddle 5 3 3) _
      hfactor
      (Q'.mul_eqv_congr_left _ _ _ height_one_bulk_fence_residual_scalar_zero))
    (Q'.mul_zero_eqv _)

end YMGap.Continuum.SU2OrderedRacahHeightOneBulkCancellationFence

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneBulkCancellationFence.height_one_bulk_fence_physical_data
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneBulkCancellationFence.height_one_bulk_fence_residual_scalar_zero
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneBulkCancellationFence.height_one_bulk_fence_base_nonzero
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneBulkCancellationFence.height_one_bulk_fence_full_correction
