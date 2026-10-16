/-
# Adaptive Heron stage for the actual bulk-source scaling kernel

The first- and second-order heat action-scaling coefficients are finite and
explicit for every cutoff, even when no cutoff-uniform coefficient bound has
yet been proved.  A constructive geometric modulus may therefore choose the
Heron stage after the cutoff and source-row pair are fixed.  At every later
stage the actual matching-color source scaling kernel is below any supplied
positive rational tolerance; distinct colors remain exactly zero.

This removes the finite rational Heron approximation as a pairwise
obstruction.  It does not provide a cutoff-independent stage, sum the whole
weighted source carrier, prove a neighboring-time sign, compare the ORIGINAL
law, construct a continuum Hamiltonian, or prove the Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceFirstOrderYoungEnergy
import YMGap.Continuum.RegularLinearGeometricModulus

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionWick
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCommonActionResidualContraction
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelResidualRightEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope

local infix:50 " ≈ " => Q'.eqv

private theorem qListSum_map_eq_listQSum_local {Index : Type}
    (value : Index → Q') : ∀ items : List Index,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _item :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

private theorem ldlFactorResidualCoefficient_nonnegative
    (n : Nat) (factor : Nat → Nat → Q') (diagonal : Nat → Q')
    (hpositive : finiteLDLPositiveDiagonalCheck n diagonal = true)
    (left right : Nat) :
    (0 : Q') ≤
      ldlFactorResidualCoefficient n factor diagonal left right := by
  unfold ldlFactorResidualCoefficient
  apply listQSum_nonnegative_on
  intro channel hchannel
  apply Q'.mul_nonneg
  · exact CReal.errAt_nonneg (diagonal channel)
      (finiteLDLPositiveDiagonalCheck_pos hpositive
        (List.mem_range.mp hchannel)) 0
  · exact Q'.abs_nonneg _

private theorem physicalResidualEnvelope_nonnegative
    (n : Nat) (entry : Nat → Nat → Q')
    (hentry : ∀ left right, (0 : Q') ≤ entry left right)
    (leftRow rightRow : Nat → Q') :
    (0 : Q') ≤
      physicalCovarianceBilinearResidualEnvelope
        n entry leftRow rightRow := by
  unfold physicalCovarianceBilinearResidualEnvelope
  simp only [qListSum_map_eq_listQSum_local]
  apply listQSum_nonnegative_on
  intro left _
  apply listQSum_nonnegative_on
  intro right _
  exact Q'.mul_nonneg _ _ (Q'.abs_nonneg _) (hentry left right)

theorem bulkSourceHeatActionScalingFirstOrderCoefficient_nonnegative
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) :
    (0 : Q') ≤
      bulkSourceHeatActionScalingFirstOrderCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex := by
  unfold bulkSourceHeatActionScalingFirstOrderCoefficient
    combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
  let n := historyCoordinateCount timeBonds
    (combGaugeEdgeCount (bulkSourceWidth side))
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL
    timeBonds (bulkSourceWidth side)
  exact physicalResidualEnvelope_nonnegative n
    (ldlFactorResidualCoefficient n data.lower data.diagonal)
    (ldlFactorResidualCoefficient_nonnegative n data.lower data.diagonal
      (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
        timeBonds (bulkSourceWidth side)))
    (bulkSourcePhysicalColorCurlRow side leftTime leftRowIndex)
    (bulkSourcePhysicalColorCurlRow side rightTime rightRowIndex)

private theorem residualRightCoefficient_nonnegative
    (timeBonds width coordinate : Nat) (rightRow : Nat → Q') :
    (0 : Q') ≤
      combGaugeHeatFreeHistoryPrecisionStageResidualRightCoefficient
        timeBonds width coordinate rightRow := by
  unfold combGaugeHeatFreeHistoryPrecisionStageResidualRightCoefficient
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let data := combGaugeHeatFreeHistoryCovariancePositiveLDL timeBonds width
  exact physicalResidualEnvelope_nonnegative n
    (ldlFactorResidualCoefficient n data.lower data.diagonal)
    (ldlFactorResidualCoefficient_nonnegative n data.lower data.diagonal
      (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
        timeBonds width))
    (combGaugeHeatFreeHistoryPrecisionRow timeBonds width coordinate)
    rightRow

theorem bulkSourceHeatActionScalingQuadraticCoefficient_nonnegative
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) :
    (0 : Q') ≤
      bulkSourceHeatActionScalingQuadraticCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex := by
  unfold bulkSourceHeatActionScalingQuadraticCoefficient
    combGaugeHeatFreeHistoryActionScalingQuadraticCoefficient
  apply listQSum_nonnegative_on
  intro left _
  apply listQSum_nonnegative_on
  intro right _
  apply Q'.mul_nonneg
  · exact Q'.mul_nonneg _ _ (Q'.abs_nonneg _)
      (residualRightCoefficient_nonnegative
        timeBonds (bulkSourceWidth side) right
        (bulkSourcePhysicalColorCurlRow
          side rightTime rightRowIndex))
  · exact ldlFactorResidualCoefficient_nonnegative
      (historyCoordinateCount timeBonds
        (combGaugeEdgeCount (bulkSourceWidth side)))
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds (bulkSourceWidth side)).lower
      (combGaugeHeatFreeHistoryCovariancePositiveLDL
        timeBonds (bulkSourceWidth side)).diagonal
      (combGaugeHeatFreeHistoryCovariancePositiveLDL_diagonal_check
        timeBonds (bulkSourceWidth side)) left right

/-- Sum of the first- and second-order coefficients controlling one actual
source-row pair. -/
def bulkSourceHeatActionScalingTotalCoefficient
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) : Q' :=
  bulkSourceHeatActionScalingFirstOrderCoefficient
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex +
    bulkSourceHeatActionScalingQuadraticCoefficient
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex

theorem bulkSourceHeatActionScalingTotalCoefficient_nonnegative
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) :
    (0 : Q') ≤
      bulkSourceHeatActionScalingTotalCoefficient
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex := by
  unfold bulkSourceHeatActionScalingTotalCoefficient
  exact Q'.zero_le_add _ _
    (bulkSourceHeatActionScalingFirstOrderCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex)
    (bulkSourceHeatActionScalingQuadraticCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex)

/-- Constructive stage selected after fixing one finite cutoff, source-row
pair, and positive rational tolerance. -/
def bulkSourceHeatActionScalingAdaptiveStage
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat)
    (epsilon : Q') : Nat :=
  geoOuterModulus
    (bulkSourceHeatActionScalingTotalCoefficient
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex)
    epsilon

private theorem half_pow_le_one : ∀ stage : Nat,
    HalfPow.half ^ stage ≤ (1 : Q')
  | 0 => Q'.le_refl' 1
  | stage + 1 => by
      have hproduct := Q'.mul_le_mul_of_nonneg
        (show HalfPow.half ≤ (1 : Q') by decide)
        (half_pow_le_one stage) Q'.zero_le_one
        (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg stage)
      exact Q'.le_trans' _ _ _ hproduct
        (Q'.le_of_eqv (Q'.one_mul_eqv 1))

/-- A nonnegative first-order plus quadratic half-power envelope is bounded
by the geometric tail with their summed coefficient. -/
theorem twoOrderEnvelope_le_geoTail
    (first quadratic : Q')
    (hfirst : (0 : Q') ≤ first)
    (hquadratic : (0 : Q') ≤ quadratic)
    (stage : Nat) :
    first * HalfPow.half ^ stage +
        (quadratic * HalfPow.half ^ stage) *
          HalfPow.half ^ stage ≤
      geoTail (first + quadratic) stage := by
  let power := HalfPow.half ^ stage
  have hpower : (0 : Q') ≤ power :=
    Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg stage
  have hpowerOne : power ≤ (1 : Q') := half_pow_le_one stage
  have hquadraticPower : (0 : Q') ≤ quadratic * power :=
    Q'.mul_nonneg _ _ hquadratic hpower
  have hquadraticTerm :
      (quadratic * power) * power ≤ quadratic * power := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _
        (quadratic * power) hpowerOne hquadraticPower) ?_
    exact Q'.le_of_eqv (Q'.mul_one_eqv (quadratic * power))
  have hfirstStep :
      first * power + (quadratic * power) * power ≤
        first * power + quadratic * power :=
    Q'.add_le_add_left _ _ _ hquadraticTerm
  have hcombine :
      first * power + quadratic * power ≈
        (first + quadratic) * power :=
    Q'.eqv_symm (Q'.add_mul_eqv first quadratic power)
  have hcoefficient : (0 : Q') ≤ first + quadratic :=
    Q'.zero_le_add _ _ hfirst hquadratic
  have hcombinedNonnegative :
      (0 : Q') ≤ (first + quadratic) * power :=
    Q'.mul_nonneg _ _ hcoefficient hpower
  refine Q'.le_trans' _ _ _ hfirstStep
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcombine) ?_)
  unfold geoTail
  refine Q'.le_trans' _
    ((first + quadratic) * power +
      (first + quadratic) * power) _
    (Q'.add_le_self_of_nonneg _ _ hcombinedNonnegative) ?_
  exact Q'.le_of_eqv
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1))
        (.mul (.var 0) (.var 1)))
      (.mul (.mul (.const 2) (.var 0)) (.var 1))
      (by decide) (fun
        | 0 => first + quadratic
        | _ => power))

/-- At every stage beyond the adaptive modulus, the actual source action
scaling kernel is below the supplied tolerance for matching colors and remains
exactly zero for distinct colors. -/
theorem bulkSourceHeatActionScalingKernel_abs_le_epsilon
    (timeBonds side stage leftTime rightTime leftRowIndex rightRowIndex : Nat)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (hstage : bulkSourceHeatActionScalingAdaptiveStage
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex epsilon ≤
      stage) :
    Q'.abs
        (finiteGaussianWeightedActionScalingKernel
          (combGaugePlaquetteNoiseCount timeBonds (bulkSourceWidth side))
          (completeOpenCubeHeatGaussianActionRowSquares
            timeBonds (bulkSourceWidth side) stage)
          (bulkSourceHeatHeronColorCurlRow
            timeBonds side stage leftTime leftRowIndex)
          (bulkSourceHeatHeronColorCurlRow
            timeBonds side stage rightTime rightRowIndex)) ≤
      if leftRowIndex % 3 = rightRowIndex % 3 then epsilon else 0 := by
  let first := bulkSourceHeatActionScalingFirstOrderCoefficient
    timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  let quadratic := bulkSourceHeatActionScalingQuadraticCoefficient
    timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  let total := bulkSourceHeatActionScalingTotalCoefficient
    timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  have hfirst : (0 : Q') ≤ first :=
    bulkSourceHeatActionScalingFirstOrderCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  have hquadratic : (0 : Q') ≤ quadratic :=
    bulkSourceHeatActionScalingQuadraticCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  have htotal : (0 : Q') ≤ total :=
    bulkSourceHeatActionScalingTotalCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex
  have htail : geoTail total stage ≤ epsilon := by
    exact geoTail_le_of_modulus total htotal epsilon hepsilon stage hstage
  have hkernel := bulkSourceHeatActionScalingKernel_abs_le_two_order
    timeBonds side stage leftTime rightTime leftRowIndex rightRowIndex
  by_cases hcomponent : leftRowIndex % 3 = rightRowIndex % 3
  · simp only [if_pos hcomponent] at hkernel ⊢
    refine Q'.le_trans' _ _ _ hkernel
      (Q'.le_trans' _ _ _ ?_ htail)
    change first * HalfPow.half ^ stage +
        (quadratic * HalfPow.half ^ stage) *
          HalfPow.half ^ stage ≤ geoTail total stage
    unfold total bulkSourceHeatActionScalingTotalCoefficient
    exact twoOrderEnvelope_le_geoTail
      first quadratic hfirst hquadratic stage
  · simp only [if_neg hcomponent] at hkernel ⊢
    exact hkernel

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage.bulkSourceHeatActionScalingTotalCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage.twoOrderEnvelope_le_geoTail
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage.bulkSourceHeatActionScalingKernel_abs_le_epsilon
