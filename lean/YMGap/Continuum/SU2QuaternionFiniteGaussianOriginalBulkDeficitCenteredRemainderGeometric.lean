/-
# Absolute geometric budget for the centered ORIGINAL bulk-deficit remainder

The exact centered deficit pair is the pure vector-jet pair plus two mixed
terms and one remainder--remainder term.  The square-root-free Young bound for
the SAME ORIGINAL window state converts each non-jet term into the sum of its
two actual diagonal norms.  The geometric diagonal budgets then give one
explicit absolute error:

  |centered deficit pair - pure vector-jet pair|
    <= vector diagonal budget + 2 * remainder diagonal budget.

This isolates the pure vector-jet response quantitatively inside the finite
ORIGINAL law.  It does not compare that response with the FREE Gaussian law,
prove the neighboring strict margin, remove a cutoff, construct a continuum
Hamiltonian, or prove the Clay mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
  (centeredPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.OSReconstructionProgress (q_cancel_left)
open YMGap.Continuum.QuaternionHaarCharacterInterval
  (heatRatio heatRemainderBound)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonalGeometric
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetDiagonalGeometric
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- The total non-jet absolute budget after paying both mixed terms and the
remainder--remainder term. -/
def originalBulkCenteredRemainderGeometricBudget
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  originalBulkVectorQuadraticJetDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n +
    2 * originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n

theorem originalBulkCenteredRemainderGeometricBudget_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (n : Nat) :
    (0 : Q') ≤ originalBulkCenteredRemainderGeometricBudget
      hw0 hw1 hd hsRate s hs n := by
  unfold originalBulkCenteredRemainderGeometricBudget
  exact Q'.zero_le_add _ _
    (originalBulkVectorQuadraticJetDiagonalGeometricBudget_nonnegative
      hw0 hw1 hd hsRate s hs n)
    (Q'.mul_nonneg _ _ (by decide)
      (originalBulkScalarSquareRemainderDiagonalGeometricBudget_nonnegative
        hw0 hw1 hd hsRate s hs n))

/-- The jet--remainder term is paid additively by the vector and remainder
diagonal budgets, without extracting square roots. -/
theorem originalBulkJetRemainderPair_two_abs_geometric_le
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
    2 * Q'.abs
        (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L jet remainder) ≤
      vectorBudget + remainderBudget := by
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
  have hYoung := laggedWindowPair_two_abs_le_diagonal_sum
    hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
    n L jet remainder
    (originalBulkVectorQuadraticJetOwnShifted_supported
      hw0 hw1 s hs stage n)
    (originalBulkScalarSquareRemainderOwnShifted_supported
      hw0 hw1 s hs stage n)
  change 2 * Q'.abs
      (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L jet remainder) ≤
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul jet jet) +
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (liftBoundary (L * N (s * s)) remainder)
          (liftBoundary (L * N (s * s)) remainder)) at hYoung
  have hleft := originalBulkVectorQuadraticJet_leftDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  have hright := originalBulkScalarSquareRemainder_rightDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul jet jet) ≤ vectorBudget at hleft
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary (L * N (s * s)) remainder)
        (liftBoundary (L * N (s * s)) remainder)) ≤
    remainderBudget at hright
  exact Q'.le_trans' _ _ _ hYoung (Q'.add_le_add hleft hright)

/-- The remainder--jet term has the symmetric additive payment. -/
theorem originalBulkRemainderJetPair_two_abs_geometric_le
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
    2 * Q'.abs
        (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L remainder jet) ≤
      remainderBudget + vectorBudget := by
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
  have hYoung := laggedWindowPair_two_abs_le_diagonal_sum
    hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
    n L remainder jet
    (originalBulkScalarSquareRemainderOwnShifted_supported
      hw0 hw1 s hs stage n)
    (originalBulkVectorQuadraticJetOwnShifted_supported
      hw0 hw1 s hs stage n)
  change 2 * Q'.abs
      (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder jet) ≤
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul remainder remainder) +
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (liftBoundary (L * N (s * s)) jet)
          (liftBoundary (L * N (s * s)) jet)) at hYoung
  have hleft := originalBulkScalarSquareRemainder_leftDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  have hright := originalBulkVectorQuadraticJet_rightDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul remainder remainder) ≤
    remainderBudget at hleft
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary (L * N (s * s)) jet)
        (liftBoundary (L * N (s * s)) jet)) ≤ vectorBudget at hright
  exact Q'.le_trans' _ _ _ hYoung (Q'.add_le_add hleft hright)

/-- The remainder--remainder term costs two copies of the remainder diagonal
budget in its doubled absolute-value form. -/
theorem originalBulkRemainderPair_two_abs_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let remainder := originalBulkScalarSquareRemainderOwnShifted
      hw0 hw1 s hs stage n
    let remainderBudget :=
      originalBulkScalarSquareRemainderDiagonalGeometricBudget
        hw0 hw1 hd hsRate s hs n
    2 * Q'.abs
        (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
          (Nat.le_add_right _ _) n L remainder remainder) ≤
      remainderBudget + remainderBudget := by
  dsimp only
  let remainder := originalBulkScalarSquareRemainderOwnShifted
    hw0 hw1 s hs stage n
  let remainderBudget :=
    originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
  have hYoung := laggedWindowPair_two_abs_le_diagonal_sum
    hw0 hw1 (headCutoff w + stage) (s * s) (Nat.le_add_right _ _)
    n L remainder remainder
    (originalBulkScalarSquareRemainderOwnShifted_supported
      hw0 hw1 s hs stage n)
    (originalBulkScalarSquareRemainderOwnShifted_supported
      hw0 hw1 s hs stage n)
  change 2 * Q'.abs
      (laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L remainder remainder) ≤
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n (polyMul remainder remainder) +
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (polyMul (liftBoundary (L * N (s * s)) remainder)
          (liftBoundary (L * N (s * s)) remainder)) at hYoung
  have hleft := originalBulkScalarSquareRemainder_leftDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  have hright := originalBulkScalarSquareRemainder_rightDiagonal_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n (polyMul remainder remainder) ≤
    remainderBudget at hleft
  change windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n
      (polyMul (liftBoundary (L * N (s * s)) remainder)
        (liftBoundary (L * N (s * s)) remainder)) ≤
    remainderBudget at hright
  exact Q'.le_trans' _ _ _ hYoung (Q'.add_le_add hleft hright)

/-- Quantitative isolation of the pure centered vector-jet lagged response
inside the exact finite ORIGINAL centered deficit pair. -/
theorem originalBulkDeficitOwn_centeredPair_sub_jet_absolute_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let jet := originalBulkVectorQuadraticJetOwnShifted
      hw0 hw1 s hs stage n
    let total := centeredPair hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L
      (sourcePolynomial (originalBulkDeficitExpression s hs))
      (originalBulkDeficitOwnMean hw0 hw1 s hs stage n)
    let jetPair := laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L jet jet
    Q'.abs (total + (-jetPair)) ≤
      originalBulkCenteredRemainderGeometricBudget
        hw0 hw1 hd hsRate s hs n := by
  dsimp only
  let jet := originalBulkVectorQuadraticJetOwnShifted
    hw0 hw1 s hs stage n
  let remainder := originalBulkScalarSquareRemainderOwnShifted
    hw0 hw1 s hs stage n
  let total := centeredPair hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right (headCutoff w) stage) n L
    (sourcePolynomial (originalBulkDeficitExpression s hs))
    (originalBulkDeficitOwnMean hw0 hw1 s hs stage n)
  let jetPair := laggedWindowPair hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right (headCutoff w) stage) n L jet jet
  let jetRemainder := laggedWindowPair hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right (headCutoff w) stage)
    n L jet remainder
  let remainderJet := laggedWindowPair hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right (headCutoff w) stage)
    n L remainder jet
  let remainderPair := laggedWindowPair hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right (headCutoff w) stage)
    n L remainder remainder
  let vectorBudget := originalBulkVectorQuadraticJetDiagonalGeometricBudget
    hw0 hw1 hd hsRate s hs n
  let remainderBudget :=
    originalBulkScalarSquareRemainderDiagonalGeometricBudget
      hw0 hw1 hd hsRate s hs n
  have hsplit := originalBulkDeficitOwn_centeredPair_jet_remainder
    hw0 hw1 s hs stage n L
  change total ≈ jetPair + (jetRemainder + (remainderJet + remainderPair)) at hsplit
  have hdiff : total + (-jetPair) ≈
      jetRemainder + (remainderJet + remainderPair) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hsplit (Q'.eqv_refl (-jetPair)))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
        (.var 1) (by decide)
        (fun | 0 => jetPair | _ => jetRemainder + (remainderJet + remainderPair)))
  have htriangle : Q'.abs (total + (-jetPair)) ≤
      Q'.abs jetRemainder +
        (Q'.abs remainderJet + Q'.abs remainderPair) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hdiff))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.add_le_add_left _ _ _ (ExpNeg.abs_add_le _ _)))
  have htwiceTriangle : 2 * Q'.abs (total + (-jetPair)) ≤
      2 * (Q'.abs jetRemainder +
        (Q'.abs remainderJet + Q'.abs remainderPair)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ 2 htriangle (by decide)
  have hjetRemainder := originalBulkJetRemainderPair_two_abs_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change 2 * Q'.abs jetRemainder ≤ vectorBudget + remainderBudget
    at hjetRemainder
  have hremainderJet := originalBulkRemainderJetPair_two_abs_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change 2 * Q'.abs remainderJet ≤ remainderBudget + vectorBudget
    at hremainderJet
  have hremainderPair := originalBulkRemainderPair_two_abs_geometric_le
    hw0 hw1 hsmall hd hsRate s hs stage n L
  change 2 * Q'.abs remainderPair ≤ remainderBudget + remainderBudget
    at hremainderPair
  have habsDistribute :
      2 * (Q'.abs jetRemainder +
          (Q'.abs remainderJet + Q'.abs remainderPair)) ≈
        2 * Q'.abs jetRemainder +
          (2 * Q'.abs remainderJet + 2 * Q'.abs remainderPair) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.var 0) (.add (.var 1) (.var 2))))
      (.add (.mul (.const 2) (.var 0))
        (.add (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 2))))
      (by decide)
      (fun index =>
        if index = 0 then Q'.abs jetRemainder
        else if index = 1 then Q'.abs remainderJet
        else Q'.abs remainderPair)
  have hsum :
      2 * Q'.abs jetRemainder +
          (2 * Q'.abs remainderJet + 2 * Q'.abs remainderPair) ≤
        (vectorBudget + remainderBudget) +
          ((remainderBudget + vectorBudget) +
            (remainderBudget + remainderBudget)) :=
    Q'.add_le_add hjetRemainder
      (Q'.add_le_add hremainderJet hremainderPair)
  have htwice : 2 * Q'.abs (total + (-jetPair)) ≤
      (vectorBudget + remainderBudget) +
        ((remainderBudget + vectorBudget) +
          (remainderBudget + remainderBudget)) :=
    Q'.le_trans' _ _ _ htwiceTriangle
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv habsDistribute) hsum)
  have hbudgetRegroup :
      (vectorBudget + remainderBudget) +
          ((remainderBudget + vectorBudget) +
            (remainderBudget + remainderBudget)) ≈
        2 * (vectorBudget + 2 * remainderBudget) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.add (.add (.var 1) (.var 0)) (.add (.var 1) (.var 1))))
      (.mul (.const 2) (.add (.var 0) (.mul (.const 2) (.var 1))))
      (by decide) (fun | 0 => vectorBudget | _ => remainderBudget)
  have htwiceBudget : 2 * Q'.abs (total + (-jetPair)) ≤
      2 * (vectorBudget + 2 * remainderBudget) :=
    Q'.le_trans' _ _ _ htwice (Q'.le_of_eqv hbudgetRegroup)
  change Q'.abs (total + (-jetPair)) ≤
    originalBulkCenteredRemainderGeometricBudget
      hw0 hw1 hd hsRate s hs n
  unfold originalBulkCenteredRemainderGeometricBudget
  exact q_cancel_left (c := (2 : Q')) (by decide) htwiceBudget

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric.originalBulkCenteredRemainderGeometricBudget
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric.originalBulkCenteredRemainderGeometricBudget_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric.originalBulkJetRemainderPair_two_abs_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric.originalBulkRemainderJetPair_two_abs_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric.originalBulkRemainderPair_two_abs_geometric_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainderGeometric.originalBulkDeficitOwn_centeredPair_sub_jet_absolute_geometric_le
