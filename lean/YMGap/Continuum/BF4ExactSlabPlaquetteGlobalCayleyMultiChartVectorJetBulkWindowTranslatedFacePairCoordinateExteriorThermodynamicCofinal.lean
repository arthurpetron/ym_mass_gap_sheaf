/-
# Cofinal thermodynamic convergence of the original selected lower-face law

The thermodynamic exterior cutoff has the same geometry-independent shell
base and linear carrier-size bound as the zero-placement cutoff.  The existing
dyadic side schedule therefore pays the explicit thermodynamic exterior
margin, making the full-action versus selected-source difference converge to
zero.  The full thermodynamic action is an exact cofinal subsequence of the
ordinary lower covariance sequence, so the original selected lower-face law
converges to the already-constructed lower covariance limit.

This remains a fixed-nome, fixed-local-half thermodynamic statement.  It does
not vary lattice spacing, reconstruct a continuum measure, construct the
OS/GNS Hamiltonian, or prove the Clay mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicLowerFace
import YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale
import YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabCovarianceAmplitudeDyadicScale
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorCofinalSchedule
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicCofinal
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicLowerFace
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorDyadicScale
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicAction
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicMargin
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicPlacement
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicTail
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinatePath
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairGuardedResponse
open YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairPathCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerCovariance
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DyadicGeometricCutoff
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.PolynomialGeometricDecay
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4LinfGeometricSum

/-- Shell base for the thermodynamic coordinate carrier before eliminating
its geometric parameters. -/
def thermodynamicCoordinateCovarianceShellBase
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) : Q' :=
  let placement := thermodynamicPlacement s L
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  let shellRate := entropyRate 16 (rate ^ blockLength rate 4)
  covarianceShellBase
    (left := translatedOriginalBulkVectorQuadraticJetFacePairLinks
      placement (s * s) leftOffset rightOffset leftFace rightFace)
    w hd hs
    (translatedOriginalBulkVectorQuadraticJetFacePairCap
      (s * s) leftOffset rightOffset leftFace rightFace)
    shellRate
    (block_rate_lt_one (exteriorCoordinateRate_nonnegative hw0 hd) hs)

/-- Translation changes no link count or local cap, so the thermodynamic
shell base is the same fixed local coefficient. -/
theorem thermodynamicCoordinateCovarianceShellBase_eq_fixed
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq) :
    thermodynamicCoordinateCovarianceShellBase hw0 hd hs s L leftOffset
        rightOffset leftFace rightFace =
      fixedCoordinateCovarianceShellBase hw0 hd hs := by
  unfold thermodynamicCoordinateCovarianceShellBase
    fixedCoordinateCovarianceShellBase
    fixedCoordinateCovarianceAmplitudeBase
    fixedCoordinateInsertionAmplitudeBase covarianceShellBase
    covarianceAmplitudeBase insertionAmplitudeBase
    translatedOriginalBulkVectorQuadraticJetFacePairCap
    translatedOriginalBulkVectorQuadraticJetFacePairLinks
  simp only [List.length_append, edgesOf, List.length_cons, List.length_nil,
    originalBulkVectorQuadraticJetFaceCap_eq_localCap]

/-- The thermodynamic cutoff has only linear carrier-size cost outside its
fixed denominator precision. -/
theorem thermodynamicExteriorCovarianceBlockCutoff_le_fixedLinearScale
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon) :
    thermodynamicExteriorCovarianceBlockCutoff hw0 hd hs s L leftOffset
        rightOffset leftFace rightFace epsilon ≤
      blockLength
          (entropyRate 16
            ((entropyRate 625 (adjustedCoreRate w hd)) ^
              blockLength (entropyRate 625 (adjustedCoreRate w hd)) 4)) 0 *
        (denominatorBitPrecision
            (HKConv.divPos epsilon
              (1 + fixedCoordinateCovarianceShellBase hw0 hd hs)) +
          (15 * (5 * s + 3 * L + 5) +
            4 * blockLength
              (entropyRate 625 (adjustedCoreRate w hd)) 4 + 26)) := by
  let placement := thermodynamicPlacement s L
  let carrier :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier
      placement (s * s) leftOffset rightOffset leftFace rightFace
  let cap := translatedOriginalBulkVectorQuadraticJetFacePairCap
    (s * s) leftOffset rightOffset leftFace rightFace
  let rate := entropyRate 625 (adjustedCoreRate w hd)
  have hrate : (0 : Q') ≤ rate :=
    exteriorCoordinateRate_nonnegative hw0 hd
  have hcap : (0 : Q') ≤ cap := by
    exact (translatedOriginalBulkVectorQuadraticJetFacePair_left_interval
      placement s (s * s) leftOffset rightOffset L leftFace rightFace rfl
      hleftFace hrightFace hleftOffset hrightOffset).nonnegative
  have hsupport : carrier.animal.support.length ≤ 5 * s + 3 * L + 5 :=
    translatedOriginalBulkVectorQuadraticJetFacePairCoordinateCarrier_support_length_le
      placement s (s * s) leftOffset rightOffset L leftFace rightFace
      hleftFace hrightFace hleftOffset hrightOffset
  have hcutoff := dyadicBlockCutoff_le_supportUpperBound carrier hw0 hd hs
    hrate hs hcap hepsilon (5 * s + 3 * L + 5) hsupport
  simpa only [thermodynamicExteriorCovarianceBlockCutoff,
    thermodynamicCoordinateCovarianceShellBase,
    thermodynamicCoordinateCovarianceShellBase_eq_fixed,
    placement, carrier, cap, rate] using hcutoff

/-- Affine form used by the existing dyadic side schedule. -/
theorem thermodynamicExteriorCovarianceBlockCutoff_le_affine
    {w epsilon : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s L leftOffset rightOffset : Nat)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (hepsilon : (0 : Q') < epsilon) :
    thermodynamicExteriorCovarianceBlockCutoff hw0 hd hs s L leftOffset
        rightOffset leftFace rightFace epsilon ≤
      exteriorCutoffSlope hd * s +
        exteriorCutoffIntercept hw0 hd hs L epsilon := by
  have hlinear :=
    thermodynamicExteriorCovarianceBlockCutoff_le_fixedLinearScale
      hw0 hd hs s L leftOffset rightOffset leftFace rightFace hleftFace
      hrightFace hleftOffset hrightOffset hepsilon
  simpa only [exteriorCutoffSlope, exteriorCutoffIntercept,
    shellRateBlock, carrierRateBlock, exteriorTolerancePrecision,
    Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hlinear

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

private theorem demand_le_thermodynamicExteriorMargin
    {d side : Nat} (hroom : 2 * d + side ≤ side * side) :
    d ≤ thermodynamicExteriorMargin side := by
  have hhalf : d ≤ (side * side - side) / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    omega
  have hoffset : d ≤ bulkSourceOffset side := by
    simpa only [bulkSourceOffset] using hhalf
  have hcollar :
      d ≤ originalBulkVectorQuadraticJetSpatialCollar side := by
    unfold originalBulkVectorQuadraticJetSpatialCollar bulkSourceOffset
    omega
  unfold thermodynamicExteriorMargin
  apply Nat.le_min.mpr
  exact ⟨by omega, Nat.le_min.mpr ⟨hoffset, hcollar⟩⟩

/-- The existing stage-padded side schedule pays the complete thermodynamic
tail margin for the concrete lower face. -/
theorem thermodynamicDyadicSchedule_collar
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset stage : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    let side := dyadicScheduleSide hw0 hd hs L stage
    5 * side + 3 * L + 5 + carrierRateBlock hd *
        thermodynamicExteriorCovarianceBlockCutoff hw0 hd hs side L
          leftOffset rightOffset (bulkSourceLowerFace side)
          (bulkSourceLowerFace side) (dyadicTolerance stage) ≤
      thermodynamicExteriorMargin side := by
  let side := dyadicScheduleSide hw0 hd hs L stage
  have hside : 0 < side :=
    dyadicScheduleSide_positive hw0 hd hs L stage
  have hface : bulkSourceLowerFace side ∈ bulkSourceFaces side :=
    bulkSourceLowerFace_mem side hside
  have hcutoff := thermodynamicExteriorCovarianceBlockCutoff_le_affine
    hw0 hd hs side L leftOffset rightOffset (bulkSourceLowerFace side)
    (bulkSourceLowerFace side) hface hface hleftOffset hrightOffset
    (dyadicTolerance_positive stage)
  have hdemand :
      5 * side + 3 * L + 5 + carrierRateBlock hd *
          thermodynamicExteriorCovarianceBlockCutoff hw0 hd hs side L
            leftOffset rightOffset (bulkSourceLowerFace side)
            (bulkSourceLowerFace side) (dyadicTolerance stage) ≤
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
          exteriorCollarIntercept hw0 hd hs L (dyadicTolerance stage)) +
          side ≤ side * side := by
    simpa only [side, dyadicScheduleSide] using
      affine_quadratic_room_with_padding (exteriorCollarSlope hd)
        (exteriorCollarIntercept hw0 hd hs L (dyadicTolerance stage)) stage
  exact Nat.le_trans hdemand
    (demand_le_thermodynamicExteriorMargin hquadratic)

/-- The thermodynamic exterior tail is bounded by the dyadic stage tolerance
along the concrete lower-face schedule. -/
theorem thermodynamicExteriorTail_small_on_dyadicSchedule
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (L leftOffset rightOffset stage : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    let side := dyadicScheduleSide hw0 hd hs L stage
    thermodynamicExteriorCovarianceTailBudget hw0 hd hs side L leftOffset
        rightOffset (bulkSourceLowerFace side) (bulkSourceLowerFace side) ≤
      dyadicTolerance stage := by
  let side := dyadicScheduleSide hw0 hd hs L stage
  have hside : 0 < side :=
    dyadicScheduleSide_positive hw0 hd hs L stage
  have hface : bulkSourceLowerFace side ∈ bulkSourceFaces side :=
    bulkSourceLowerFace_mem side hside
  apply thermodynamicExteriorCovarianceTailBudget_small hw0 hd hs side L
    leftOffset rightOffset (bulkSourceLowerFace side)
    (bulkSourceLowerFace side) hface hface hleftOffset hrightOffset
    (dyadicTolerance_positive stage)
  simpa only [carrierRateBlock] using
    thermodynamicDyadicSchedule_collar hw0 hd hs L leftOffset rightOffset
      stage hleftOffset hrightOffset

private theorem nomeDelta : heatRemainderBound nome < 1 :=
  BF4ExactSlabSmallNomeHaarComparison.existingNome_guards.2

private theorem nomeEntropy :
    entropyRate 625 (adjustedCoreRate nome nomeDelta) < 1 :=
  BF4ExactSlabSummableCoreRate.existingNome_entropyRate.2

/-- Fixed-nome side used by the concrete selected lower-face trajectory. -/
def thermodynamicDyadicSide (L stage : Nat) : Nat :=
  dyadicScheduleSide nome_pos nomeDelta nomeEntropy L stage

/-- Full thermodynamic covariance along the cofinal side schedule. -/
def thermodynamicDyadicFullCovariance
    (L leftOffset rightOffset stage : Nat) : CReal :=
  thermodynamicPlacedFullCovariance (thermodynamicDyadicSide L stage) L
    leftOffset rightOffset

/-- Original selected lower-face covariance along the same side schedule. -/
def thermodynamicDyadicSelectedCovariance
    (L leftOffset rightOffset stage : Nat) : CReal :=
  thermodynamicOriginalSelectedLowerCovariance
    (thermodynamicDyadicSide L stage) L leftOffset rightOffset

/-- Selected minus full covariance; this orientation feeds the constructive
null-difference limit transfer directly. -/
def thermodynamicDyadicSelectedMinusFull
    (L leftOffset rightOffset stage : Nat) : CReal :=
  CReal.sub
    (thermodynamicDyadicSelectedCovariance L leftOffset rightOffset stage)
    (thermodynamicDyadicFullCovariance L leftOffset rightOffset stage)

private theorem leEv_abs_sub_comm
    {left right bound : CReal}
    (h : leEv (CReal.abs (CReal.sub left right)) bound) :
    leEv (CReal.abs (CReal.sub right left)) bound := by
  have hcomm :
      Equiv (CReal.abs (CReal.sub right left))
        (CReal.abs (CReal.sub left right)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun approximation =>
      ExpNeg.abs_sub_comm
        (right.approx approximation) (left.approx approximation))
  apply leEv_trans (leEv_of_equiv hcomm)
  exact h

theorem thermodynamicDyadicSelectedMinusFull_small
    (L leftOffset rightOffset stage : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    leEv
      (CReal.abs
        (thermodynamicDyadicSelectedMinusFull
          L leftOffset rightOffset stage))
      (ofQ' (dyadicTolerance stage)) := by
  let side := thermodynamicDyadicSide L stage
  have hside : 0 < side := by
    exact dyadicScheduleSide_positive nome_pos nomeDelta nomeEntropy L stage
  have htail := thermodynamicPlacedFullCovariance_source_tail_bound
    side L leftOffset rightOffset hside hleftOffset hrightOffset
  change leEv
    (CReal.abs (CReal.sub
      (thermodynamicOriginalSelectedLowerCovariance
        side L leftOffset rightOffset)
      (thermodynamicPlacedFullCovariance side L leftOffset rightOffset)))
    (ofQ' (dyadicTolerance stage))
  apply leEv_trans (leEv_abs_sub_comm htail)
  apply leEv_of_le
  apply CReal.ofQ'_le_ofQ'
  simpa only [side, thermodynamicDyadicSide] using
    (thermodynamicExteriorTail_small_on_dyadicSchedule
      nome_pos nomeDelta nomeEntropy L leftOffset rightOffset stage
      hleftOffset hrightOffset)

private theorem convergesTo_zero_of_dyadic_abs_bound
    (sequence : Nat → CReal)
    (hsmall : ∀ stage,
      leEv (CReal.abs (sequence stage)) (ofQ' (dyadicTolerance stage))) :
    ConvergesTo sequence CReal.czero := by
  intro delta hdelta
  let halfDelta := HalfPow.half * delta
  have hhalfDelta : (0 : Q') < halfDelta :=
    ExpNeg.half_mul_pos delta hdelta
  refine ⟨halfDelta.den, fun stage hstage => ?_⟩
  have htolerance : dyadicTolerance stage ≤ halfDelta :=
    dyadicTolerance_eventually_le hhalfDelta hstage
  have hhalfBound :
      leEv (CReal.abs (sequence stage)) (ofQ' halfDelta) :=
    leEv_trans (hsmall stage)
      (leEv_of_le (CReal.ofQ'_le_ofQ' htolerance))
  obtain ⟨approximationStage, happroximationStage⟩ :=
    hhalfBound halfDelta hhalfDelta
  refine ⟨approximationStage, fun approximation happroximation => ?_⟩
  let difference := sequence stage
  have habsHalf :
      Q'.abs (difference.approx approximation) ≤ halfDelta + halfDelta :=
    happroximationStage approximation happroximation
  have habs : Q'.abs (difference.approx approximation) ≤ delta :=
    Q'.le_trans' _ _ _ habsHalf
      (Q'.le_of_eqv (ExpNeg.two_halves delta))
  constructor
  · show difference.approx approximation ≤ (0 : Q') + delta
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (Q'.le_trans' _ _ _ habs
        (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' delta))))
  · show (0 : Q') ≤ difference.approx approximation + delta
    have hnegative : -delta ≤ difference.approx approximation := by
      have hnegAbs : -delta ≤ -(Q'.abs (difference.approx approximation)) :=
        Q'.neg_le_neg habs
      have habsLower : -(Q'.abs (difference.approx approximation)) ≤
          difference.approx approximation := by
        have hneg := Q'.neg_le_neg
          (Q'.neg_le_abs (difference.approx approximation))
        exact Q'.le_trans' _ _ _ hneg
          (Q'.le_of_eqv
            (Q'.neg_neg_eqv (difference.approx approximation)))
      exact Q'.le_trans' _ _ _ hnegAbs habsLower
    have hadd := Q'.add_le_add_right _ _ delta hnegative
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.neg_add_self_eqv delta)) hadd

/-- The selected-minus-full difference converges to zero along the explicit
cofinal side schedule. -/
theorem thermodynamicDyadicSelectedMinusFull_converges_zero
    (L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    ConvergesTo
      (thermodynamicDyadicSelectedMinusFull L leftOffset rightOffset)
      CReal.czero := by
  apply convergesTo_zero_of_dyadic_abs_bound
  intro stage
  exact thermodynamicDyadicSelectedMinusFull_small
    L leftOffset rightOffset stage hleftOffset hrightOffset

/-- The full thermodynamic presentation is a cofinal subsequence of the
ordinary lower covariance sequence. -/
theorem thermodynamicDyadicFullCovariance_converges
    (L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    ConvergesTo
      (thermodynamicDyadicFullCovariance L leftOffset rightOffset)
      (lowerCovarianceLimit
        (vectorJetLowerExpression L leftOffset hleftOffset)
        (vectorJetLowerExpression L rightOffset hrightOffset)) := by
  let leftExpression :=
    vectorJetLowerExpression L leftOffset hleftOffset
  let rightExpression :=
    vectorJetLowerExpression L rightOffset hrightOffset
  have hreindexed :=
    BF4PhysicalDenseStageDiagonalComparison.convergesTo_cofinalReindex
      (lowerCovariance_converges leftExpression rightExpression)
      (fun stage => thermodynamicMargin (thermodynamicDyadicSide L stage))
      (fun threshold => threshold) (by
        intro threshold stage hstage
        have hstageSide : stage ≤ thermodynamicDyadicSide L stage := by
          exact stage_le_dyadicScheduleSide nome_pos nomeDelta nomeEntropy
            L stage
        have hside : 0 < thermodynamicDyadicSide L stage := by
          exact dyadicScheduleSide_positive nome_pos nomeDelta nomeEntropy
            L stage
        have hsideSquare :
            thermodynamicDyadicSide L stage ≤
              thermodynamicDyadicSide L stage *
                thermodynamicDyadicSide L stage := by
          calc
            thermodynamicDyadicSide L stage =
                thermodynamicDyadicSide L stage * 1 := by omega
            _ ≤ thermodynamicDyadicSide L stage *
                thermodynamicDyadicSide L stage :=
              Nat.mul_le_mul_left _ hside
        have hmargin :
            thermodynamicDyadicSide L stage *
                thermodynamicDyadicSide L stage ≤
              thermodynamicMargin (thermodynamicDyadicSide L stage) := by
          unfold thermodynamicMargin
          omega
        exact Nat.le_trans hstage
          (Nat.le_trans hstageSide (Nat.le_trans hsideSquare hmargin)))
  apply TrigAddCReal.convergesTo_congr_seq
    (s := fun stage => lowerCovarianceSequence leftExpression rightExpression
      (thermodynamicMargin (thermodynamicDyadicSide L stage)))
  · intro stage
    exact (thermodynamicPlacedFullCovariance_sequence_pin
      (thermodynamicDyadicSide L stage) L leftOffset rightOffset
      hleftOffset hrightOffset).symm
  · exact hreindexed

/-- The actual original selected lower-face covariance converges to the
constructed ordinary lower covariance limit. -/
theorem thermodynamicDyadicSelectedCovariance_converges
    (L leftOffset rightOffset : Nat)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L) :
    ConvergesTo
      (thermodynamicDyadicSelectedCovariance L leftOffset rightOffset)
      (lowerCovarianceLimit
        (vectorJetLowerExpression L leftOffset hleftOffset)
        (vectorJetLowerExpression L rightOffset hrightOffset)) := by
  exact CReal.convergesTo_of_sub_null
    (thermodynamicDyadicSelectedMinusFull_converges_zero
      L leftOffset rightOffset hleftOffset hrightOffset)
    (thermodynamicDyadicFullCovariance_converges
      L leftOffset rightOffset hleftOffset hrightOffset)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal.thermodynamicCoordinateCovarianceShellBase_eq_fixed
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal.thermodynamicExteriorCovarianceBlockCutoff_le_fixedLinearScale
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal.thermodynamicDyadicSchedule_collar
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal.thermodynamicExteriorTail_small_on_dyadicSchedule
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal.thermodynamicDyadicSelectedMinusFull_converges_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal.thermodynamicDyadicFullCovariance_converges
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePairCoordinateExteriorThermodynamicCofinal.thermodynamicDyadicSelectedCovariance_converges
