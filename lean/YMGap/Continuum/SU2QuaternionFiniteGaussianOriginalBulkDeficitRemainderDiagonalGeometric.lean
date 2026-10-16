/-
# Complete geometric diagonal budgets for the original bulk remainder

The selected covariance convolution and the endpoint mean-mismatch squares
are inserted into the two exact covariance-plus-mismatch diagonal identities.
Both literal remainder diagonals therefore share one explicit geometric
budget.  The three existing SAME-ORIGINAL Cauchy bounds are then specialized:
the remainder--remainder term is paid completely, while the two mixed terms
retain only their genuine vector-jet diagonal factors.

This is still a finite selected-action result.  It does not compare the
vector jet with the FREE Gaussian law, prove the strict neighboring margin,
remove the cutoff, construct a Hamiltonian, or prove the Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate (adjustedCoreRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval (probeCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
  (windowRatio_square_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)
open YMGap.Continuum.QuaternionHaarCharacterInterval
  (heatRatio heatRemainderBound)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4LinfGeometricSum (tailCap_nonnegative)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- The complete covariance part of either remainder diagonal. -/
def originalBulkScalarSquareRemainderCovarianceGeometricBudget
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) : Q' :=
  originalBulkScalarSquareRemainderPairAmplitude w hd hsRate *
    (originalBulkScalarSquareRemainderGeometricRowCap hw0 hd hsRate *
          originalBulkScalarSquareRemainderFaceWeightSquareMass s hs +
      originalBulkScalarSquareRemainderGeometricRowCap hw0 hd hsRate *
          originalBulkScalarSquareRemainderFaceWeightSquareMass s hs)

/-- Covariance budget plus the actual scheduled endpoint mismatch square. -/
def originalBulkScalarSquareRemainderDiagonalGeometricBudget
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  originalBulkScalarSquareRemainderCovarianceGeometricBudget
      hw0 hd hsRate s hs +
    originalBulkScalarSquareRemainderSelectedMeanError
        hw0 hw1 s hs n *
      originalBulkScalarSquareRemainderSelectedMeanError
        hw0 hw1 s hs n

private theorem supported_mono_local {small large : Nat} {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks small polynomial)
    (hsize : small ≤ large) : SupportedQuaternionBlocks large polynomial := by
  intro term hterm
  exact Nat.le_trans (hsupport term hterm) (Nat.mul_le_mul_left 4 hsize)

theorem originalBulkScalarSquareRemainderFaceWeightSquareMass_nonnegative
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderFaceWeightSquareMass s hs := by
  unfold originalBulkScalarSquareRemainderFaceWeightSquareMass
  apply listQSum_nonnegative_on
  intro face _
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
    (originalBulkScalarSquareRemainderFaceWeight s hs face)

theorem originalBulkScalarSquareRemainderGeometricRowCap_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1) :
    (0 : Q') ≤
      originalBulkScalarSquareRemainderGeometricRowCap hw0 hd hsRate := by
  unfold originalBulkScalarSquareRemainderGeometricRowCap
  exact tailCap_nonnegative
    (originalBulkScalarSquareRemainderGeometricRate_nonnegative hw0 hd)
    hsRate 1 0

theorem originalBulkScalarSquareRemainderCovarianceGeometricBudget_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderCovarianceGeometricBudget
      hw0 hd hsRate s hs := by
  unfold originalBulkScalarSquareRemainderCovarianceGeometricBudget
  exact Q'.mul_nonneg _ _
    (originalBulkScalarSquareRemainderPairAmplitude_nonnegative w hd hsRate)
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (originalBulkScalarSquareRemainderGeometricRowCap_nonnegative
          hw0 hd hsRate)
        (originalBulkScalarSquareRemainderFaceWeightSquareMass_nonnegative
          s hs))
      (Q'.mul_nonneg _ _
        (originalBulkScalarSquareRemainderGeometricRowCap_nonnegative
          hw0 hd hsRate)
        (originalBulkScalarSquareRemainderFaceWeightSquareMass_nonnegative
          s hs)))

theorem originalBulkScalarSquareRemainderSelectedMeanError_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderSelectedMeanError
      hw0 hw1 s hs n := by
  unfold originalBulkScalarSquareRemainderSelectedMeanError
  exact Q'.mul_nonneg _ _
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 (s * s)) n)
    (Q'.zero_le_add _ _
      (originalBulkScalarSquareRemainderCap_nonnegative s hs)
      (originalBulkScalarSquareRemainderCap_nonnegative s hs))

theorem originalBulkScalarSquareRemainderDiagonalGeometricBudget_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n := by
  unfold originalBulkScalarSquareRemainderDiagonalGeometricBudget
  exact Q'.zero_le_add _ _
    (originalBulkScalarSquareRemainderCovarianceGeometricBudget_nonnegative
      hw0 hd hsRate s hs)
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (originalBulkScalarSquareRemainderSelectedMeanError
        hw0 hw1 s hs n))

/-- Complete lower remainder diagonal bound. -/
theorem originalBulkScalarSquareRemainder_leftDiagonal_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul remainder remainder) ≤
      originalBulkScalarSquareRemainderDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n := by
  dsimp only [originalBulkScalarSquareRemainderOwnShifted]
  let covariance := originalBulkScalarSquareRemainderSelectedCovariance
    hw0 hw1 s hs stage n L 0
  let mismatch := originalBulkScalarSquareRemainderSelectedMean
      hw0 hw1 s hs stage n L 0 +
    -originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let error := originalBulkScalarSquareRemainderSelectedMeanError
    hw0 hw1 s hs n
  let covarianceBudget :=
    originalBulkScalarSquareRemainderCovarianceGeometricBudget
      hw0 hd hsRate s hs
  have hsplit :
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n
          (polyMul
            (shifted (originalBulkScalarSquareRemainder s hs)
              (originalBulkScalarSquareRemainderOwnMean
                hw0 hw1 s hs stage n))
            (shifted (originalBulkScalarSquareRemainder s hs)
              (originalBulkScalarSquareRemainderOwnMean
                hw0 hw1 s hs stage n))) ≈
        covariance + mismatch * mismatch := by
    simpa only [covariance, mismatch] using
      (originalBulkScalarSquareRemainder_leftDiagonal_covariance
        hw0 hw1 s hs stage n L)
  have hcovariance : covariance ≤ covarianceBudget :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self covariance)
      (originalBulkScalarSquareRemainderSelectedCovariance_geometric_le
        hw0 hw1 hsmall hd hsRate s hs stage n L 0 (Nat.zero_le _))
  have hmismatch : mismatch * mismatch ≤ error * error := by
    simpa only [mismatch, error] using
      (originalBulkScalarSquareRemainderSelectedMean_zero_mismatch_square_le
        hw0 hw1 s hs stage n L)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.add_le_add hcovariance hmismatch)

/-- Complete chronologically lifted upper remainder diagonal bound. -/
theorem originalBulkScalarSquareRemainder_rightDiagonal_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    let lifted := liftBoundary (L * N (s * s)) remainder
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≤
      originalBulkScalarSquareRemainderDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n := by
  dsimp only [originalBulkScalarSquareRemainderOwnShifted]
  let covariance := originalBulkScalarSquareRemainderSelectedCovariance
    hw0 hw1 s hs stage n L L
  let mismatch := originalBulkScalarSquareRemainderSelectedMean
      hw0 hw1 s hs stage n L L +
    -originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let error := originalBulkScalarSquareRemainderSelectedMeanError
    hw0 hw1 s hs n
  let covarianceBudget :=
    originalBulkScalarSquareRemainderCovarianceGeometricBudget
      hw0 hd hsRate s hs
  have hsplit :
      let remainder := originalBulkScalarSquareRemainder s hs
      let center := originalBulkScalarSquareRemainderOwnMean
        hw0 hw1 s hs stage n
      let lifted := liftBoundary (L * N (s * s)) (shifted remainder center)
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≈
        covariance + mismatch * mismatch := by
    simpa only [covariance, mismatch] using
      (originalBulkScalarSquareRemainder_rightDiagonal_covariance
        hw0 hw1 s hs stage n L)
  have hcovariance : covariance ≤ covarianceBudget :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self covariance)
      (originalBulkScalarSquareRemainderSelectedCovariance_geometric_le
        hw0 hw1 hsmall hd hsRate s hs stage n L L (Nat.le_refl _))
  have hmismatch : mismatch * mismatch ≤ error * error := by
    simpa only [mismatch, error] using
      (originalBulkScalarSquareRemainderSelectedMean_L_mismatch_square_le
        hw0 hw1 s hs stage n L)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.add_le_add hcovariance hmismatch)

/-- The remainder--remainder Cauchy consumer is paid completely by the
common geometric diagonal budget. -/
theorem originalBulkRemainderPair_cauchySchwarz_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    let budget := originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder remainder *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L remainder remainder ≤
      budget * budget := by
  dsimp only
  let remainder := originalBulkScalarSquareRemainderOwnShifted
    hw0 hw1 s hs stage n
  let budget := originalBulkScalarSquareRemainderDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  have hcauchy := originalBulkRemainderPair_cauchySchwarz
    hw0 hw1 s hs stage n L
  change laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L remainder remainder *
      laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder remainder ≤ _ at hcauchy
  have hleft := originalBulkScalarSquareRemainder_leftDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  have hright := originalBulkScalarSquareRemainder_rightDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul remainder remainder) ≤ budget at hleft
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary (L * N (s * s)) remainder)
        (liftBoundary (L * N (s * s)) remainder)) ≤ budget at hright
  have hsize : (L + 1) * N (s * s) = N (s * s) + L * N (s * s) := by
    rw [Nat.succ_mul]
    omega
  have hrightSupported : SupportedQuaternionBlocks ((L + 1) * N (s * s))
      (liftBoundary (L * N (s * s)) remainder) := by
    rw [hsize]
    exact lift_supported
      (originalBulkScalarSquareRemainderOwnShifted_supported
        hw0 hw1 s hs stage n)
      (L * N (s * s))
  have hrightNonnegative : (0 : Q') ≤
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (liftBoundary (L * N (s * s)) remainder)
          (liftBoundary (L * N (s * s)) remainder)) :=
    windowRatio_square_nonnegative hw0 hw1
      (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
      n L n hrightSupported
  exact Q'.le_trans' _ _ _ hcauchy
    (Q'.mul_le_mul_of_nonneg hleft hright
      (originalBulkScalarSquareRemainderDiagonalGeometricBudget_nonnegative
        hw0 hw1 hd hsRate s hs n)
      hrightNonnegative)

/-- The jet--remainder mixed Cauchy consumer now retains only the left
vector-jet diagonal; the remainder diagonal is paid by the common budget. -/
theorem originalBulkJetRemainderPair_cauchySchwarz_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted
      hw0 hw1 s hs stage n
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    let budget := originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L jet remainder *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L jet remainder ≤
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul jet jet) * budget := by
  dsimp only
  let jet := originalBulkVectorQuadraticJetOwnShifted
    hw0 hw1 s hs stage n
  let remainder := originalBulkScalarSquareRemainderOwnShifted
    hw0 hw1 s hs stage n
  let budget := originalBulkScalarSquareRemainderDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  have hcauchy := originalBulkJetRemainderPair_cauchySchwarz
    hw0 hw1 s hs stage n L
  have hright := originalBulkScalarSquareRemainder_rightDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary (L * N (s * s)) remainder)
        (liftBoundary (L * N (s * s)) remainder)) ≤ budget at hright
  have hsize : N (s * s) ≤ (L + 1) * N (s * s) := by
    rw [Nat.succ_mul]
    omega
  have hjetSupported : SupportedQuaternionBlocks ((L + 1) * N (s * s)) jet :=
    supported_mono_local
      (originalBulkVectorQuadraticJetOwnShifted_supported
        hw0 hw1 s hs stage n) hsize
  have hjetNonnegative : (0 : Q') ≤
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul jet jet) :=
    windowRatio_square_nonnegative hw0 hw1
      (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
      n L n hjetSupported
  exact Q'.le_trans' _ _ _ hcauchy
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hright hjetNonnegative)

/-- The remainder--jet mixed Cauchy consumer now retains only the lifted
right vector-jet diagonal. -/
theorem originalBulkRemainderJetPair_cauchySchwarz_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted
      hw0 hw1 s hs stage n
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    let budget := originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder jet *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L remainder jet ≤
      budget *
        windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n
          (polyMul (liftBoundary (L * N (s * s)) jet)
            (liftBoundary (L * N (s * s)) jet)) := by
  dsimp only
  let jet := originalBulkVectorQuadraticJetOwnShifted
    hw0 hw1 s hs stage n
  let remainder := originalBulkScalarSquareRemainderOwnShifted
    hw0 hw1 s hs stage n
  let budget := originalBulkScalarSquareRemainderDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  have hcauchy := originalBulkRemainderJetPair_cauchySchwarz
    hw0 hw1 s hs stage n L
  have hleft := originalBulkScalarSquareRemainder_leftDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul remainder remainder) ≤ budget at hleft
  have hsize : (L + 1) * N (s * s) = N (s * s) + L * N (s * s) := by
    rw [Nat.succ_mul]
    omega
  have hjetRightSupported : SupportedQuaternionBlocks ((L + 1) * N (s * s))
      (liftBoundary (L * N (s * s)) jet) := by
    rw [hsize]
    exact lift_supported
      (originalBulkVectorQuadraticJetOwnShifted_supported
        hw0 hw1 s hs stage n)
      (L * N (s * s))
  have hjetRightNonnegative : (0 : Q') ≤
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (liftBoundary (L * N (s * s)) jet)
          (liftBoundary (L * N (s * s)) jet)) :=
    windowRatio_square_nonnegative hw0 hw1
      (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
      n L n hjetRightSupported
  exact Q'.le_trans' _ _ _ hcauchy
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hjetRightNonnegative)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainderCovarianceGeometricBudget
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainderDiagonalGeometricBudget
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainderFaceWeightSquareMass_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainderGeometricRowCap_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainderCovarianceGeometricBudget_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainderSelectedMeanError_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainderDiagonalGeometricBudget_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainder_leftDiagonal_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkScalarSquareRemainder_rightDiagonal_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkRemainderPair_cauchySchwarz_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkJetRemainderPair_cauchySchwarz_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric.originalBulkRemainderJetPair_cauchySchwarz_geometric_le
