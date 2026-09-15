/-
# ORIGINAL crossing tails, uniformly in the bulk spin cutoff

Recode the original bulk dressing inside Haar as the product of the lower
and upper heat polynomials, then apply their cutoff-independent coefficient
bounds. A computed crossing cutoff controls every later crossing prefix
for EVERY bulk cutoff, with the original shared links and observables.

The two nomes may differ. Uniformity is only in the bulk spin cutoff and
later crossing cutoff, at fixed nomes, extent and observable. No uniformity
in volume, beta or spacing is asserted. No completed norm reconstruction,
transfer range density, full-space zero-time continuity or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabMixedInterfacePin
import YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit

namespace YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabMixedInterfacePin
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

/-- Independently written ORIGINAL bulk product; not an L1 transport. -/
def bulkInsertion (b : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) : RatPoly :=
  polyMul (polyMul (lower e) (upper e))
    (polyMul (lowerHeatProduct b B half) (upperHeatProduct b B half))

theorem mixedInsertion_eq_bulkInsertion (b : Q') (B : Nat) {half : Nat}
    (e : PlaquetteExpression half) :
    RatPolyCoeffEqv (mixedInsertion b B e) (bulkInsertion b B e) :=
  (((lowerObservable_one b B half).mul_left (lower e)).mul
    ((upperObservable_one b B half).mul_left (upper e))).trans
      (RatPolyCoeffEqv.mul_four_swap (lower e) (lowerHeatProduct b B half)
        (upper e) (upperHeatProduct b B half))

theorem mixedQuadratic_eq_bulkHaar (b v : Q') (B K : Nat) {half : Nat}
    (e : PlaquetteExpression half) :
    mixedQuadratic b v B K e ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (polyMul (bulkInsertion b B e) (interfaceHeatProduct v K half)) :=
  haar_of_coeff_eqv _ ((mixedInsertion_eq_bulkInsertion b B e).mul
    (interfaceHeatInsertion_eq_product v K half))

/-- No bulk or crossing cutoff occurs in this bound. -/
def bulkCap (b : Q') {half : Nat} (e : PlaquetteExpression half) : Q' :=
  polynomialCoefficientL1 (polyMul (lower e) (upper e)) *
    (heatProductBound b (centralExtent half) (centralLowerFaceIds half) *
      heatProductBound b (centralExtent half) (centralUpperFaceIds half))

theorem bulkCap_nonnegative {b : Q'} (hb : (0 : Q') ≤ b) {half : Nat}
    (e : PlaquetteExpression half) : (0 : Q') ≤ bulkCap b e :=
  Q'.mul_nonneg _ _ (polynomialCoefficientL1_nonnegative _)
    (Q'.mul_nonneg _ _ (heatProductBound_nonnegative hb _ _) (heatProductBound_nonnegative hb _ _))

theorem bulkInsertion_l1_bound {b : Q'} (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (B : Nat) {half : Nat} (e : PlaquetteExpression half) :
    polynomialCoefficientL1 (bulkInsertion b B e) ≤ bulkCap b e := by
  have hbulk : polynomialCoefficientL1 (polyMul (lowerHeatProduct b B half) (upperHeatProduct b B half)) ≤
      heatProductBound b (centralExtent half) (centralLowerFaceIds half) *
        heatProductBound b (centralExtent half) (centralUpperFaceIds half) :=
    Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (lowerHeatProduct_bound hb0 hb1 B half)
          (polynomialCoefficientL1_nonnegative _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (upperHeatProduct_bound hb0 hb1 B half)
          (heatProductBound_nonnegative (Q'.le_of_lt hb0) _ _)))
  exact Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hbulk (polynomialCoefficientL1_nonnegative _))

def tailTolerance (b : Q') {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Q' :=
  HKConv.divPos epsilon (bulkCap b e + 1)

theorem tailTolerance_pos (b : Q') {half : Nat} (e : PlaquetteExpression half)
    {epsilon : Q'} (he : (0 : Q') < epsilon) : (0 : Q') < tailTolerance b e epsilon :=
  HKConv.divPos_pos (CReal.num_pos_of_pos he)

theorem tailTolerance_budget {b : Q'} (hb : (0 : Q') ≤ b) {half : Nat}
    (e : PlaquetteExpression half) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    bulkCap b e * tailTolerance b e epsilon ≤ epsilon := by
  have hpos : (0 : Q') < bulkCap b e + 1 :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (bulkCap_nonnegative hb e))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (tailTolerance_pos b e he)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hpos))))

/-- A Type-level threshold independent of the bulk cutoff B. -/
def crossingCutoff (b v : Q') {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') : Nat :=
  heatProductCutoff v (centralExtent half) (centralFixedFaceIds half) (tailTolerance b e epsilon)

theorem crossingRemainder_bound {b v : Q'} (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (B N L : Nat)
    (hN : crossingCutoff b v e epsilon ≤ N) :
    Q'.abs (quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (polyMul (bulkInsertion b B e)
        (heatProductRemainder v (centralExtent half) N L (centralFixedFaceIds half)))) ≤ epsilon :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (bulkInsertion_l1_bound hb0 hb1 B e)
          (polynomialCoefficientL1_nonnegative _))
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_left _ _ _
            (heatProductRemainder_small hv0 hv1 _ _ _ (tailTolerance_pos b e he) N L hN)
            (bulkCap_nonnegative (Q'.le_of_lt hb0) e))
          (tailTolerance_budget (Q'.le_of_lt hb0) e he))))

private theorem transport_close {a b a' b' epsilon : Q'} (ha : a ≈ a') (hb : b ≈ b')
    (h : a' ≤ b' + epsilon ∧ b' ≤ a' + epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon :=
  ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv ha)
    (Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ epsilon (Q'.ge_of_eqv hb))),
   Q'.le_trans' _ _ _ (Q'.le_of_eqv hb)
    (Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ epsilon (Q'.ge_of_eqv ha)))⟩

theorem mixed_increment {b v : Q'} (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (B N L : Nat)
    (hN : crossingCutoff b v e epsilon ≤ N) :
    mixedQuadratic b v B (N + L) e ≤ mixedQuadratic b v B N e + epsilon ∧
    mixedQuadratic b v B N e ≤ mixedQuadratic b v B (N + L) e + epsilon :=
  transport_close (mixedQuadratic_eq_bulkHaar b v B (N + L) e) (mixedQuadratic_eq_bulkHaar b v B N e)
    (close_of_add_remainder
      (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv _
        (((heatProduct_cutoff_append v (centralExtent half) N L (centralFixedFaceIds half)).mul_left
          (bulkInsertion b B e)).trans (RatPolyCoeffEqv.mul_add_right _ _ _)))
        (quaternionHaar_append _ _ _))
      (crossingRemainder_bound hb0 hb1 hv0 hv1 e epsilon he B N L hN))

/-- SAME bulk dressing on both sides, for an arbitrary bulk cutoff. -/
theorem mixed_later {b v : Q'} (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) (B N K : Nat)
    (hN : crossingCutoff b v e epsilon ≤ N) (hK : N ≤ K) :
    mixedQuadratic b v B K e ≤ mixedQuadratic b v B N e + epsilon ∧
    mixedQuadratic b v B N e ≤ mixedQuadratic b v B K e + epsilon := by
  have h := mixed_increment hb0 hb1 hv0 hv1 e epsilon he B N (K - N) hN
  rw [Nat.add_sub_of_le hK] at h
  exact h

/-- The full ORIGINAL numerator is close to a fixed crossing packet even
as its bulk cutoff grows. This is not a norm reconstruction theorem. -/
theorem original_diagonal_close {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (e : PlaquetteExpression half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (N K : Nat) (hN : crossingCutoff w w e epsilon ≤ N) (hK : N ≤ K) :
    originalQuadratic w K e ≤ mixedQuadratic w w K N e + epsilon ∧
    mixedQuadratic w w K N e ≤ originalQuadratic w K e + epsilon :=
  transport_close (Q'.eqv_symm (mixed_original_diagonal w (Q'.le_of_lt hw0) K e)) (Q'.eqv_refl _)
    (mixed_later hw0 hw1 hw0 hw1 e epsilon he K N K hN hK)

/-- Computed witness first, then the ALL-bulk/all-later crossing estimate. -/
def bulkUniformCrossingCertificate (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) {half : Nat} (e : PlaquetteExpression half)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' N : Nat, ∀ B K : Nat, N ≤ K →
      (mixedQuadratic b v B K e ≤ mixedQuadratic b v B N e + epsilon ∧
       mixedQuadratic b v B N e ≤ mixedQuadratic b v B K e + epsilon) :=
  ⟨crossingCutoff b v e epsilon, fun B K hK =>
    mixed_later hb0 hb1 hv0 hv1 e epsilon he B _ K (Nat.le_refl _) hK⟩

end YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail

#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.bulkInsertion
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.mixedInsertion_eq_bulkInsertion
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.mixedQuadratic_eq_bulkHaar
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.bulkCap
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.bulkCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.bulkInsertion_l1_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.tailTolerance
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.tailTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.tailTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.crossingCutoff
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.crossingRemainder_bound
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.mixed_increment
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.mixed_later
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.original_diagonal_close
#print axioms YMGap.Continuum.BF4ExactSlabBulkUniformCrossingTail.bulkUniformCrossingCertificate
