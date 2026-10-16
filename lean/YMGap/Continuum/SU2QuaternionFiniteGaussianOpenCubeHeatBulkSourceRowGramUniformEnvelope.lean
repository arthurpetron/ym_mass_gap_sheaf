/-
# Stage-uniform Gram envelope for actual heat bulk-source rows

The connected common-action scaling contraction contains an extra source-row
Gram factor.  This file bounds that Gram uniformly over every Heron stage by
the absolute exact physical covariance plus the already explicit first-order
covariance-error coefficient.  Distinct color blocks remain exactly
orthogonal.

The envelope is finite and stage-independent after fixing the finite cutoff
and row pair.  It is not cutoff-uniform and does not yet sum the connected
carrier, prove a neighboring-time sign, compare the ORIGINAL law, construct a
continuum Hamiltonian, or prove the Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceMeanScalingAdaptiveStage

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope

set_option autoImplicit false
set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombHeatFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubePlaquetteRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatCovarianceScalingResidual
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatNormalizedRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionRowPullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatActionScalingKernelTwoOrderEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingEnvelope
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceScalingAdaptiveStage

local infix:50 " ≈ " => Q'.eqv

/-- The checked entrywise Heron covariance estimate gives the corresponding
physical bilinear covariance-error estimate for arbitrary finite rows. -/
theorem combGaugeHeatFreeHistoryCovarianceErrorBilinear_abs_le_geometric
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    let covarianceError := finiteMatrixSub
      (combGaugeHeatFreeHistoryStageCovariance timeBonds width stage)
      (combGaugeHeatFreeHistoryCovariance timeBonds width)
    Q'.abs (finiteMatrixBilinear n covarianceError leftRow rightRow) ≤
      combGaugeHeatFreeHistoryActionScalingFirstOrderCoefficient
          timeBonds width leftRow rightRow *
        HalfPow.half ^ stage := by
  dsimp only
  let n := historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  let transform :=
    combGaugeHeatFreeHistoryHeronTransform timeBonds width stage
  let stageCovariance :=
    combGaugeHeatFreeHistoryStageCovariance timeBonds width stage
  let exactCovariance :=
    combGaugeHeatFreeHistoryCovariance timeBonds width
  let entryEnvelope := ldlFactorResidualEnvelope n
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal
    stage
  let entryCoefficient := ldlFactorResidualCoefficient n
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).lower
    (combGaugeHeatFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal
  have herror := physicalCovarianceBilinear_error
    n n transform exactCovariance entryEnvelope leftRow rightRow
    (fun left right hleft hright =>
      (combGaugeHeatFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)
  change Q'.abs
      (finiteMatrixBilinear n stageCovariance leftRow rightRow +
        -finiteMatrixBilinear n exactCovariance leftRow rightRow) ≤
    physicalCovarianceBilinearResidualEnvelope n
      entryEnvelope leftRow rightRow at herror
  have hsub := finiteMatrixBilinear_sub_local n
    stageCovariance exactCovariance leftRow rightRow
  have henvelope := physicalResidualEnvelope_eq_coefficient_mul_half
    n stage entryEnvelope entryCoefficient leftRow rightRow
    (fun left right =>
      ldlFactorResidualEnvelope_eq_coefficient_mul_half
        n
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeHeatFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        stage left right)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hsub))
    (Q'.le_trans' _ _ _ herror (Q'.le_of_eqv henvelope))

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

/-- Stage-independent bound for the matching-color Gram of two actual source
rows: exact checked physical covariance plus the first-order Heron residual
coefficient. -/
def bulkSourceHeatRowGramUniformEnvelope
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) : Q' :=
  Q'.abs
      (finiteMatrixBilinear
        (historyCoordinateCount timeBonds
          (combGaugeEdgeCount (bulkSourceWidth side)))
        (combGaugeHeatFreeHistoryCovariance
          timeBonds (bulkSourceWidth side))
        (bulkSourcePhysicalColorCurlRow side leftTime leftRowIndex)
        (bulkSourcePhysicalColorCurlRow side rightTime rightRowIndex)) +
    bulkSourceHeatActionScalingFirstOrderCoefficient
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex

theorem bulkSourceHeatRowGramUniformEnvelope_nonnegative
    (timeBonds side leftTime rightTime leftRowIndex rightRowIndex : Nat) :
    (0 : Q') ≤ bulkSourceHeatRowGramUniformEnvelope
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex := by
  unfold bulkSourceHeatRowGramUniformEnvelope
  exact Q'.zero_le_add _ _ (Q'.abs_nonneg _)
    (bulkSourceHeatActionScalingFirstOrderCoefficient_nonnegative
      timeBonds side leftTime rightTime leftRowIndex rightRowIndex)

/-- Every matching-color source-row Gram is bounded by the same explicit
stage-independent envelope; distinct colors are exactly orthogonal. -/
theorem bulkSourceHeatHeronColorCurlRow_gram_abs_le_uniformEnvelope
    (timeBonds side stage leftTime rightTime leftRowIndex rightRowIndex : Nat) :
    Q'.abs
        (finiteRowGram
          (combGaugePlaquetteNoiseCount
            timeBonds (bulkSourceWidth side))
          (bulkSourceHeatHeronColorCurlRow
            timeBonds side stage leftTime leftRowIndex)
          (bulkSourceHeatHeronColorCurlRow
            timeBonds side stage rightTime rightRowIndex)) ≤
      if leftRowIndex % 3 = rightRowIndex % 3 then
        bulkSourceHeatRowGramUniformEnvelope
          timeBonds side leftTime rightTime leftRowIndex rightRowIndex
      else 0 := by
  let n := historyCoordinateCount timeBonds
    (combGaugeEdgeCount (bulkSourceWidth side))
  let transform := combGaugeHeatFreeHistoryHeronTransform
    timeBonds (bulkSourceWidth side) stage
  let stageCovariance := combGaugeHeatFreeHistoryStageCovariance
    timeBonds (bulkSourceWidth side) stage
  let exactCovariance := combGaugeHeatFreeHistoryCovariance
    timeBonds (bulkSourceWidth side)
  let leftPhysical := bulkSourcePhysicalColorCurlRow
    side leftTime leftRowIndex
  let rightPhysical := bulkSourcePhysicalColorCurlRow
    side rightTime rightRowIndex
  have hleftComponent : leftRowIndex % 3 < 3 :=
    Nat.mod_lt _ (by decide)
  have hrightComponent : rightRowIndex % 3 < 3 :=
    Nat.mod_lt _ (by decide)
  rw [bulkSourceHeatHeronColorCurlRow_eq_heatColorPulledRow,
    bulkSourceHeatHeronColorCurlRow_eq_heatColorPulledRow]
  have hgram := finiteRowGram_heatColorPulledRow
    n transform leftPhysical rightPhysical
    (leftRowIndex % 3) (rightRowIndex % 3)
    hleftComponent hrightComponent
  by_cases hcomponent : leftRowIndex % 3 = rightRowIndex % 3
  · rw [if_pos hcomponent]
    rw [if_pos hcomponent] at hgram
    have herror :=
      combGaugeHeatFreeHistoryCovarianceErrorBilinear_abs_le_geometric
        timeBonds (bulkSourceWidth side) stage leftPhysical rightPhysical
    have hfirst : (0 : Q') ≤
        bulkSourceHeatActionScalingFirstOrderCoefficient
          timeBonds side leftTime rightTime leftRowIndex rightRowIndex :=
      bulkSourceHeatActionScalingFirstOrderCoefficient_nonnegative
        timeBonds side leftTime rightTime leftRowIndex rightRowIndex
    have hscaled :
        bulkSourceHeatActionScalingFirstOrderCoefficient
              timeBonds side leftTime rightTime leftRowIndex rightRowIndex *
            HalfPow.half ^ stage ≤
          bulkSourceHeatActionScalingFirstOrderCoefficient
            timeBonds side leftTime rightTime leftRowIndex rightRowIndex := by
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _
          (half_pow_le_one stage) hfirst) ?_
      exact Q'.le_of_eqv
        (Q'.mul_one_eqv
          (bulkSourceHeatActionScalingFirstOrderCoefficient
            timeBonds side leftTime rightTime leftRowIndex rightRowIndex))
    have hsub := finiteMatrixBilinear_sub_local n
      stageCovariance exactCovariance leftPhysical rightPhysical
    have hsum :
        finiteMatrixBilinear n exactCovariance leftPhysical rightPhysical +
            finiteMatrixBilinear n
              (finiteMatrixSub stageCovariance exactCovariance)
              leftPhysical rightPhysical ≈
          finiteMatrixBilinear n stageCovariance
            leftPhysical rightPhysical := by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hsub)
        (poly_identity_of_normal_eq
          (.add (.var 0) (.add (.var 1) (.neg (.var 0))))
          (.var 1) (by decide) (fun
            | 0 => finiteMatrixBilinear n exactCovariance
                leftPhysical rightPhysical
            | _ => finiteMatrixBilinear n stageCovariance
                leftPhysical rightPhysical))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr
          (Q'.eqv_trans _ _ _ hgram (Q'.eqv_symm hsum)))) ?_
    unfold bulkSourceHeatRowGramUniformEnvelope
    refine Q'.le_trans' _ _ _
      (Q'.abs_add_le'
        (finiteMatrixBilinear n exactCovariance leftPhysical rightPhysical)
        (finiteMatrixBilinear n
          (finiteMatrixSub stageCovariance exactCovariance)
          leftPhysical rightPhysical)) ?_
    exact Q'.add_le_add_left _ _ _
      (Q'.le_trans' _ _ _ herror hscaled)
  · rw [if_neg hcomponent]
    rw [if_neg hcomponent] at hgram
    exact Q'.le_of_eqv (Q'.abs_eqv_congr hgram)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope.combGaugeHeatFreeHistoryCovarianceErrorBilinear_abs_le_geometric
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope.bulkSourceHeatRowGramUniformEnvelope_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeHeatBulkSourceRowGramUniformEnvelope.bulkSourceHeatHeronColorCurlRow_gram_abs_le_uniformEnvelope
