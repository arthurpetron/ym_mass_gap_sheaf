/-
# Complete geometric diagonal budgets for the original vector jet

The selected vector covariance convolution and the two endpoint mismatch
squares are inserted into the exact covariance-plus-mismatch diagonal
identities.  Both vector diagonals therefore share one explicit finite
geometric budget.  The two mixed SAME-ORIGINAL Cauchy bounds can then be paid
entirely by the vector and scalar-remainder budgets.

This does not compare the pure lagged vector response with the FREE Gaussian
law, prove the neighboring strict margin, remove a cutoff, construct a
Hamiltonian, or prove the Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.QuaternionHaarCharacterInterval
  (heatRatio heatRemainderBound)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4LinfGeometricSum (tailCap_nonnegative)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- The complete covariance part of either vector-jet diagonal. -/
def originalBulkVectorQuadraticJetCovarianceGeometricBudget
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) : Q' :=
  originalBulkVectorQuadraticJetPairAmplitude w hd hsRate *
    (originalBulkVectorQuadraticJetGeometricRowCap hw0 hd hsRate *
          originalBulkVectorQuadraticJetFaceWeightSquareMass s hs +
      originalBulkVectorQuadraticJetGeometricRowCap hw0 hd hsRate *
          originalBulkVectorQuadraticJetFaceWeightSquareMass s hs)

/-- Covariance budget plus the actual vector endpoint mismatch square. -/
def originalBulkVectorQuadraticJetDiagonalGeometricBudget
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  originalBulkVectorQuadraticJetCovarianceGeometricBudget
      hw0 hd hsRate s hs +
    originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n *
      originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n

theorem originalBulkVectorQuadraticJetFaceWeightSquareMass_nonnegative
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetFaceWeightSquareMass s hs := by
  unfold originalBulkVectorQuadraticJetFaceWeightSquareMass
  apply listQSum_nonnegative_on
  intro face _
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
    (originalBulkVectorQuadraticJetFaceWeight s hs face)

theorem originalBulkVectorQuadraticJetGeometricRowCap_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetGeometricRowCap
      hw0 hd hsRate := by
  unfold originalBulkVectorQuadraticJetGeometricRowCap
  exact tailCap_nonnegative
    (originalBulkVectorQuadraticJetGeometricRate_nonnegative hw0 hd)
    hsRate 1 0

theorem originalBulkVectorQuadraticJetCovarianceGeometricBudget_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetCovarianceGeometricBudget
      hw0 hd hsRate s hs := by
  unfold originalBulkVectorQuadraticJetCovarianceGeometricBudget
  exact Q'.mul_nonneg _ _
    (originalBulkVectorQuadraticJetPairAmplitude_nonnegative w hd hsRate)
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (originalBulkVectorQuadraticJetGeometricRowCap_nonnegative
          hw0 hd hsRate)
        (originalBulkVectorQuadraticJetFaceWeightSquareMass_nonnegative s hs))
      (Q'.mul_nonneg _ _
        (originalBulkVectorQuadraticJetGeometricRowCap_nonnegative
          hw0 hd hsRate)
        (originalBulkVectorQuadraticJetFaceWeightSquareMass_nonnegative s hs)))

theorem originalBulkVectorQuadraticJetCap_nonnegative
    (s : Nat) (hs : 0 < s) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetCap s hs := by
  unfold originalBulkVectorQuadraticJetCap originalBulkCoefficientSum
  apply listQSum_nonnegative_on
  intro face hface
  exact Q'.le_of_lt (bulkSourceCoefficient_pos hs hface)

theorem originalBulkVectorQuadraticJetSelectedMeanError_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetSelectedMeanError
      hw0 hw1 s hs n := by
  unfold originalBulkVectorQuadraticJetSelectedMeanError
  exact Q'.mul_nonneg _ _
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 (s * s)) n)
    (Q'.zero_le_add _ _
      (originalBulkVectorQuadraticJetCap_nonnegative s hs)
      (originalBulkVectorQuadraticJetCap_nonnegative s hs))

theorem originalBulkVectorQuadraticJetDiagonalGeometricBudget_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n := by
  unfold originalBulkVectorQuadraticJetDiagonalGeometricBudget
  exact Q'.zero_le_add _ _
    (originalBulkVectorQuadraticJetCovarianceGeometricBudget_nonnegative
      hw0 hd hsRate s hs)
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n))

/-- Complete lower vector-jet diagonal bound. -/
theorem originalBulkVectorQuadraticJet_leftDiagonal_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted
      hw0 hw1 s hs stage n
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul jet jet) ≤
      originalBulkVectorQuadraticJetDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n := by
  dsimp only [originalBulkVectorQuadraticJetOwnShifted]
  let covariance := originalBulkVectorQuadraticJetSelectedCovariance
    hw0 hw1 s hs stage n L 0
  let mismatch := originalBulkVectorQuadraticJetSelectedMean
      hw0 hw1 s hs stage n L 0 +
    -originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  let error := originalBulkVectorQuadraticJetSelectedMeanError
    hw0 hw1 s hs n
  let covarianceBudget :=
    originalBulkVectorQuadraticJetCovarianceGeometricBudget
      hw0 hd hsRate s hs
  have hsplit :
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n
          (polyMul
            (shifted (originalBulkVectorQuadraticJet s hs)
              (originalBulkVectorQuadraticJetOwnMean
                hw0 hw1 s hs stage n))
            (shifted (originalBulkVectorQuadraticJet s hs)
              (originalBulkVectorQuadraticJetOwnMean
                hw0 hw1 s hs stage n))) ≈
        covariance + mismatch * mismatch := by
    simpa only [covariance, mismatch] using
      (originalBulkVectorQuadraticJet_leftDiagonal_covariance
        hw0 hw1 s hs stage n L)
  have hcovariance : covariance ≤ covarianceBudget :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self covariance)
      (originalBulkVectorQuadraticJetSelectedCovariance_geometric_le
        hw0 hw1 hsmall hd hsRate s hs stage n L 0 (Nat.zero_le _))
  have hmismatch : mismatch * mismatch ≤ error * error := by
    simpa only [mismatch, error] using
      (originalBulkVectorQuadraticJetSelectedMean_zero_mismatch_square_le
        hw0 hw1 s hs stage n L)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.add_le_add hcovariance hmismatch)

/-- Complete chronologically lifted upper vector-jet diagonal bound. -/
theorem originalBulkVectorQuadraticJet_rightDiagonal_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted
      hw0 hw1 s hs stage n
    let lifted := liftBoundary (L * N (s * s)) jet
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≤
      originalBulkVectorQuadraticJetDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n := by
  dsimp only [originalBulkVectorQuadraticJetOwnShifted]
  let covariance := originalBulkVectorQuadraticJetSelectedCovariance
    hw0 hw1 s hs stage n L L
  let mismatch := originalBulkVectorQuadraticJetSelectedMean
      hw0 hw1 s hs stage n L L +
    -originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  let error := originalBulkVectorQuadraticJetSelectedMeanError
    hw0 hw1 s hs n
  let covarianceBudget :=
    originalBulkVectorQuadraticJetCovarianceGeometricBudget
      hw0 hd hsRate s hs
  have hsplit :
      let jet := originalBulkVectorQuadraticJet s hs
      let center := originalBulkVectorQuadraticJetOwnMean
        hw0 hw1 s hs stage n
      let lifted := liftBoundary (L * N (s * s)) (shifted jet center)
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L n (polyMul lifted lifted) ≈
        covariance + mismatch * mismatch := by
    simpa only [covariance, mismatch] using
      (originalBulkVectorQuadraticJet_rightDiagonal_covariance
        hw0 hw1 s hs stage n L)
  have hcovariance : covariance ≤ covarianceBudget :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self covariance)
      (originalBulkVectorQuadraticJetSelectedCovariance_geometric_le
        hw0 hw1 hsmall hd hsRate s hs stage n L L (Nat.le_refl _))
  have hmismatch : mismatch * mismatch ≤ error * error := by
    simpa only [mismatch, error] using
      (originalBulkVectorQuadraticJetSelectedMean_L_mismatch_square_le
        hw0 hw1 s hs stage n L)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.add_le_add hcovariance hmismatch)

/-- The jet--remainder mixed Cauchy square is paid completely by the two
explicit SAME-ORIGINAL diagonal budgets. -/
theorem originalBulkJetRemainderPair_cauchySchwarz_fully_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted
      hw0 hw1 s hs stage n
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    let vectorBudget := originalBulkVectorQuadraticJetDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
    let remainderBudget :=
      originalBulkScalarSquareRemainderDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L jet remainder *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L jet remainder ≤
      vectorBudget * remainderBudget := by
  dsimp only
  let jet := originalBulkVectorQuadraticJetOwnShifted
    hw0 hw1 s hs stage n
  let remainder := originalBulkScalarSquareRemainderOwnShifted
    hw0 hw1 s hs stage n
  let vectorBudget := originalBulkVectorQuadraticJetDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  let remainderBudget :=
    originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
  have hmixed := originalBulkJetRemainderPair_cauchySchwarz_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L jet remainder *
      laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L jet remainder ≤
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul jet jet) *
        remainderBudget at hmixed
  have hjet := originalBulkVectorQuadraticJet_leftDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul jet jet) ≤ vectorBudget at hjet
  exact Q'.le_trans' _ _ _ hmixed
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hjet
      (originalBulkScalarSquareRemainderDiagonalGeometricBudget_nonnegative
        hw0 hw1 hd hsRate s hs n))

/-- The remainder--jet mixed Cauchy square has the same complete payment. -/
theorem originalBulkRemainderJetPair_cauchySchwarz_fully_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted
      hw0 hw1 s hs stage n
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    let vectorBudget := originalBulkVectorQuadraticJetDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
    let remainderBudget :=
      originalBulkScalarSquareRemainderDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n
    laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder jet *
        laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L remainder jet ≤
      remainderBudget * vectorBudget := by
  dsimp only
  let jet := originalBulkVectorQuadraticJetOwnShifted
    hw0 hw1 s hs stage n
  let remainder := originalBulkScalarSquareRemainderOwnShifted
    hw0 hw1 s hs stage n
  let vectorBudget := originalBulkVectorQuadraticJetDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  let remainderBudget :=
    originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
  have hmixed := originalBulkRemainderJetPair_cauchySchwarz_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L remainder jet *
      laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder jet ≤
    remainderBudget *
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (liftBoundary (L * N (s * s)) jet)
          (liftBoundary (L * N (s * s)) jet)) at hmixed
  have hjet := originalBulkVectorQuadraticJet_rightDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary (L * N (s * s)) jet)
        (liftBoundary (L * N (s * s)) jet)) ≤ vectorBudget at hjet
  exact Q'.le_trans' _ _ _ hmixed
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hjet
      (originalBulkScalarSquareRemainderDiagonalGeometricBudget_nonnegative
        hw0 hw1 hd hsRate s hs n))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetCovarianceGeometricBudget
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetDiagonalGeometricBudget
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetFaceWeightSquareMass_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetGeometricRowCap_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetCovarianceGeometricBudget_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetCap_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetSelectedMeanError_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJetDiagonalGeometricBudget_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJet_leftDiagonal_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkVectorQuadraticJet_rightDiagonal_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkJetRemainderPair_cauchySchwarz_fully_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric.originalBulkRemainderJetPair_cauchySchwarz_fully_geometric_le
