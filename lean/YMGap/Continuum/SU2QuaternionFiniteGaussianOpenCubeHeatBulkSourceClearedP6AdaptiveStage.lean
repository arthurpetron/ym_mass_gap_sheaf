/-
# Adaptive stage for the denominator-cleared corrected P6 frontier

The exact cleared-comparison identity has two error terms: each complete
`P6` common-action approximation error is multiplied by the corrected `P4`
from the opposite response slot.  The stage-independent `P4` envelopes and
the two complete `P6` geometric tails therefore combine into one explicit
finite coefficient and one constructive fixed-cutoff adaptive stage.

This removes only the Heron common-action scaling error from the cleared
numerator.  It proves no sign for the residual-free frontier, no denominator
positivity, no ORIGINAL-law center identification, no higher-remainder
estimate, no continuum Hamiltonian, and no Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6AdaptiveStage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCayleyTraceOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatOwnOldResponse
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceNegativeQuadraticP6AdaptiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP6ResidualFreeDecomposition
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6Frontier
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceP4UniformEnvelope
open YMGap.Continuum.RegularLinearGeometricModulus

local infix:50 " ≈ " => Q'.eqv

private theorem add_nonnegative_local (left right : Q')
    (hleft : (0 : Q') ≤ left) (hright : (0 : Q') ≤ right) :
    (0 : Q') ≤ left + right :=
  Q'.le_trans' _ _ _ hleft
    (Q'.add_le_self_of_nonneg left right hright)

/-- Aggregate coefficient for the two `P4`-weighted complete `P6`
common-action approximation errors in the cleared comparison. -/
def bulkSourceHeatP6ClearedApproximationCoefficient
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) : Q' :=
  bulkSourceHeatP4UniformEnvelope
      timeBonds side sidePositive secondLeftTime secondRightTime oldCenter *
    bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
      timeBonds side sidePositive firstLeftTime firstRightTime oldCenter +
  bulkSourceHeatP4UniformEnvelope
      timeBonds side sidePositive firstLeftTime firstRightTime oldCenter *
    bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
      timeBonds side sidePositive secondLeftTime secondRightTime oldCenter

theorem bulkSourceHeatP6ClearedApproximationCoefficient_nonnegative
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    (0 : Q') ≤ bulkSourceHeatP6ClearedApproximationCoefficient
      timeBonds side sidePositive
      firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter := by
  unfold bulkSourceHeatP6ClearedApproximationCoefficient
  exact add_nonnegative_local _ _
    (Q'.mul_nonneg _ _
      (bulkSourceHeatP4UniformEnvelope_nonnegative
        timeBonds side sidePositive secondLeftTime secondRightTime oldCenter)
      (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient_nonnegative
        timeBonds side sidePositive firstLeftTime firstRightTime oldCenter))
    (Q'.mul_nonneg _ _
      (bulkSourceHeatP4UniformEnvelope_nonnegative
        timeBonds side sidePositive firstLeftTime firstRightTime oldCenter)
      (bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient_nonnegative
        timeBonds side sidePositive secondLeftTime secondRightTime oldCenter))

/-- One constructive stage for removing the two complete common-action
approximation errors from the fixed-cutoff cleared comparison. -/
def bulkSourceHeatP6ClearedAdaptiveStage
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) (epsilon : Q') : Nat :=
  geoOuterModulus
    (bulkSourceHeatP6ClearedApproximationCoefficient
      timeBonds side sidePositive
      firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter)
    epsilon

private theorem weightedGeoTailTwo_eqv
    (secondP4Envelope firstCoefficient firstP4Envelope secondCoefficient : Q')
    (stage : Nat) :
    secondP4Envelope * geoTail firstCoefficient stage +
        firstP4Envelope * geoTail secondCoefficient stage ≈
      geoTail
        (secondP4Envelope * firstCoefficient +
          firstP4Envelope * secondCoefficient)
        stage := by
  unfold geoTail
  exact poly_identity_of_normal_eq
    (.add
      (.mul (.var 0)
        (.mul (.mul (.const 2) (.var 1)) (.var 4)))
      (.mul (.var 2)
        (.mul (.mul (.const 2) (.var 3)) (.var 4))))
    (.mul
      (.mul (.const 2)
        (.add (.mul (.var 0) (.var 1))
          (.mul (.var 2) (.var 3))))
      (.var 4))
    (by decide) (fun
      | 0 => secondP4Envelope
      | 1 => firstCoefficient
      | 2 => firstP4Envelope
      | 3 => secondCoefficient
      | _ => HalfPow.half ^ stage)

/-- The actual cleared comparison differs from its residual-free signed
frontier by one aggregate geometric tail at every Heron stage. -/
theorem openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_abs_le_geoTail
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter) :
    Q'.abs
        (openCubeHeatCayleyTraceP6ClearedComparison
            timeBonds side sidePositive stage
            firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter -
          openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
            timeBonds side sidePositive stage
            firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter) ≤
      geoTail
        (bulkSourceHeatP6ClearedApproximationCoefficient
          timeBonds side sidePositive
          firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter)
        stage := by
  let firstP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
  let secondP4 := openCubeHeatCayleyTraceP4
    timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
  let firstError :=
    openCubeHeatCayleyTraceP6
        timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter -
      openCubeHeatCayleyTraceP6ResidualFreeValue
        timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
  let secondError :=
    openCubeHeatCayleyTraceP6
        timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter -
      openCubeHeatCayleyTraceP6ResidualFreeValue
        timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
  let firstP4Envelope := bulkSourceHeatP4UniformEnvelope
    timeBonds side sidePositive firstLeftTime firstRightTime oldCenter
  let secondP4Envelope := bulkSourceHeatP4UniformEnvelope
    timeBonds side sidePositive secondLeftTime secondRightTime oldCenter
  let firstCoefficient :=
    bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
      timeBonds side sidePositive firstLeftTime firstRightTime oldCenter
  let secondCoefficient :=
    bulkSourceHeatNegativeQuadraticP6ApproximationCoefficient
      timeBonds side sidePositive secondLeftTime secondRightTime oldCenter
  have hfirstP4 : Q'.abs firstP4 ≤ firstP4Envelope :=
    openCubeHeatCayleyTraceP4_abs_le_uniformEnvelope
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
  have hsecondP4 : Q'.abs secondP4 ≤ secondP4Envelope :=
    openCubeHeatCayleyTraceP4_abs_le_uniformEnvelope
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
  have hfirstError : Q'.abs firstError ≤ geoTail firstCoefficient stage :=
    openCubeHeatCayleyTraceP6_sub_residualFree_abs_le_geoTail
      timeBonds side sidePositive stage firstLeftTime firstRightTime oldCenter
  have hsecondError : Q'.abs secondError ≤ geoTail secondCoefficient stage :=
    openCubeHeatCayleyTraceP6_sub_residualFree_abs_le_geoTail
      timeBonds side sidePositive stage secondLeftTime secondRightTime oldCenter
  have hfirstProduct : Q'.abs (secondP4 * firstError) ≤
      secondP4Envelope * geoTail firstCoefficient stage := by
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le secondP4 firstError) ?_
    exact Q'.mul_le_mul_of_nonneg
      hsecondP4 hfirstError
      (bulkSourceHeatP4UniformEnvelope_nonnegative
        timeBonds side sidePositive secondLeftTime secondRightTime oldCenter)
      (Q'.abs_nonneg firstError)
  have hsecondProduct : Q'.abs (firstP4 * secondError) ≤
      firstP4Envelope * geoTail secondCoefficient stage := by
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le firstP4 secondError) ?_
    exact Q'.mul_le_mul_of_nonneg
      hfirstP4 hsecondError
      (bulkSourceHeatP4UniformEnvelope_nonnegative
        timeBonds side sidePositive firstLeftTime firstRightTime oldCenter)
      (Q'.abs_nonneg secondError)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_eqv
          timeBonds side sidePositive stage
          firstLeftTime firstRightTime secondLeftTime secondRightTime
          oldCenter))) ?_
  change Q'.abs (secondP4 * firstError + -(firstP4 * secondError)) ≤ _
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le' (secondP4 * firstError) (-(firstP4 * secondError))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add hfirstProduct
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.abs_neg' (firstP4 * secondError)))
        hsecondProduct)) ?_
  unfold bulkSourceHeatP6ClearedApproximationCoefficient
  exact Q'.le_of_eqv
    (weightedGeoTailTwo_eqv secondP4Envelope firstCoefficient
      firstP4Envelope secondCoefficient stage)

/-- Every later stage selected by the aggregate modulus places the actual
cleared comparison within the supplied positive rational tolerance of the
residual-free signed frontier. -/
theorem openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_abs_le_epsilon
    (timeBonds side : Nat) (sidePositive : 0 < side)
    (stage firstLeftTime firstRightTime secondLeftTime secondRightTime : Nat)
    (oldCenter : CayleyTraceOldCenter)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatP6ClearedAdaptiveStage
        timeBonds side sidePositive
        firstLeftTime firstRightTime secondLeftTime secondRightTime
        oldCenter epsilon ≤ stage) :
    Q'.abs
        (openCubeHeatCayleyTraceP6ClearedComparison
            timeBonds side sidePositive stage
            firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter -
          openCubeHeatCayleyTraceP6ResidualFreeClearedComparison
            timeBonds side sidePositive stage
            firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter) ≤
      epsilon := by
  refine Q'.le_trans' _ _ _
    (openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_abs_le_geoTail
      timeBonds side sidePositive stage
      firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter) ?_
  exact geoTail_le_of_modulus
    (bulkSourceHeatP6ClearedApproximationCoefficient
      timeBonds side sidePositive
      firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter)
    (bulkSourceHeatP6ClearedApproximationCoefficient_nonnegative
      timeBonds side sidePositive
      firstLeftTime firstRightTime secondLeftTime secondRightTime oldCenter)
    epsilon hepsilon stage hstage

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6AdaptiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6AdaptiveStage.bulkSourceHeatP6ClearedApproximationCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6AdaptiveStage.openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_abs_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceClearedP6AdaptiveStage.openCubeHeatCayleyTraceP6ClearedComparison_sub_residualFree_abs_le_epsilon
