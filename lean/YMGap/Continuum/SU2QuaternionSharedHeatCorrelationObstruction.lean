/-
# A sharp test for shared-heat-only conditional correlation bounds

For the actual two-endpoint SU(2) heat packet, both fundamental coordinates
are centered, have variance 1/4, and have covariance w^3/4. Every cutoff
spin is retained. Thus a coefficient in the symmetric correlation bound
must be at least w^3. At w=7/8 it cannot satisfy a degree-times-coefficient
budget below one for any degree at least two.

This rules out a universal shared-factor-only estimate with that budget.
It is NOT an original full-slab estimate: additional one-sided action
factors, collective signed geometry, physical scaling and OS remain separate.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatContraction
import YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
import YMGap.Continuum.R1CornerAtoms

namespace YMGap.Continuum.SU2QuaternionSharedHeatCorrelationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarCoordinateAngularInterval
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

def leftCoordinate : RatPoly := polyVar 0
def rightCoordinate : RatPoly := liftHead leftCoordinate
def quarter : Q' := Q'.mkPos 1 4 (by decide)

private theorem coordinate_supported : SupportedQuaternionBlocks 1 leftCoordinate :=
  (coordinateInterval (by decide : 0 < 4*1)).support

/-- The exact packet has unit mass, even before imposing positivity guards. -/
theorem heat_mass (w : Q') (K : Nat) : quaternionHaar 2 (relativeHeat w K) ≈ 1 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_one _).symm)
    (Q'.eqv_trans _ _ _ (relativeHeat_lower_marginal w K polyOne (supported_one 1))
      (by decide))

theorem left_mean (w : Q') (K : Nat) :
    quaternionHaar 2 (polyMul (relativeHeat w K) leftCoordinate) ≈ 0 :=
  Q'.eqv_trans _ _ _ (relativeHeat_lower_marginal w K _ coordinate_supported) (by decide)

theorem right_mean (w : Q') (K : Nat) :
    quaternionHaar 2 (polyMul (relativeHeat w K) rightCoordinate) ≈ 0 :=
  Q'.eqv_trans _ _ _ (relativeHeat_upper_marginal w K _ coordinate_supported) (by decide)

theorem left_variance (w : Q') (K : Nat) :
    weightedPair 2 (relativeHeat w K) leftCoordinate leftCoordinate ≈ quarter :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ (relativeHeat_lower_marginal w K _
      (supported_polyMul coordinate_supported coordinate_supported)) (by decide))

theorem right_variance (w : Q') (K : Nat) :
    weightedPair 2 (relativeHeat w K) rightCoordinate rightCoordinate ≈ quarter := by
  have h := relativeHeat_upper_marginal w K (polyMul leftCoordinate leftCoordinate)
    (supported_polyMul coordinate_supported coordinate_supported)
  change quaternionHaar 2 (polyMul (relativeHeat w K)
    (liftHead (polyMul leftCoordinate leftCoordinate))) ≈ _ at h
  rw [liftHead_mul] at h
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
    (Q'.eqv_trans _ _ _ h (by decide))

/-- Exact covariance of centered tests; no norm/window upper bound is used. -/
theorem coordinate_covariance (w : Q') (K : Nat) (hK : 1 ≤ K) :
    weightedPair 2 (relativeHeat w K) leftCoordinate rightCoordinate ≈
      qpow w 3 * quarter := by
  have h := coordinate_transmission 1 (by decide) w K hK (0 : Fin 4) leftCoordinate
  exact Q'.eqv_trans _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.mul_comm _ _).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm))
    (Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left _ _ _ (by decide)))

/-- Any proposed symmetric covariance coefficient must already pay w^3 on
these two supported, centered, nonzero tests of the SAME heat law. -/
theorem coefficient_lower_bound (w : Q') (K : Nat) (hK : 1 ≤ K) {rho : Q'}
    (hbound : (2 : Q') * weightedPair 2 (relativeHeat w K) leftCoordinate rightCoordinate ≤
      rho * (weightedPair 2 (relativeHeat w K) leftCoordinate leftCoordinate +
        weightedPair 2 (relativeHeat w K) rightCoordinate rightCoordinate)) :
    qpow w 3 ≤ rho := by
  have hl : (2 : Q') * weightedPair 2 (relativeHeat w K) leftCoordinate rightCoordinate ≈
      HalfPow.half * qpow w 3 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coordinate_covariance w K hK))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
          (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
              (by decide : (2 : Q') * quarter ≈ HalfPow.half)) (Q'.mul_comm_eqv _ _)))))
  have hr : rho * (weightedPair 2 (relativeHeat w K) leftCoordinate leftCoordinate +
      weightedPair 2 (relativeHeat w K) rightCoordinate rightCoordinate) ≈ HalfPow.half * rho :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (left_variance w K) (right_variance w K))
        (by decide : quarter + quarter ≈ HalfPow.half))) (Q'.mul_comm_eqv _ _)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hr))) (by decide : (0 : Q') < HalfPow.half)

/-- The coefficient's deficit below one is at most this explicit quantity.
This statement does not claim that a fixed dimensionless gap is
necessary for the physical mass target. -/
theorem coefficient_deficit_le {w rho : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hrho : qpow w 3 ≤ rho) :
    (1 : Q') + -rho ≤ 3*((1 : Q') + -w) :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hrho))
    (R1CornerAtoms.oneSub_qpow_le hw0 hw1 3)

def testNome : Q' := Q'.mkPos 7 8 (by decide)
def testCutoff : Nat := headCutoff testNome + 1

/-- Positivity is actually supplied at an explicit late cutoff; the test is
not an indefinite truncated kernel or an uninhabited late-cutoff condition. -/
def testWeightCertificate : Certificate 2 (relativeHeat testNome testCutoff) :=
  relativeHeat_certificate (w := testNome) (by decide) (by decide) testCutoff (by
    unfold testCutoff
    omega)

theorem test_covariance :
    weightedPair 2 (relativeHeat testNome testCutoff) leftCoordinate rightCoordinate ≈
      Q'.mkPos 343 2048 (by decide) :=
  Q'.eqv_trans _ _ _ (coordinate_covariance testNome testCutoff (by
    unfold testCutoff; omega)) (by decide)

/-- This excludes the degree budget for a universal shared-heat-only
coefficient. It does NOT exclude a bound using the full slab's other factors. -/
theorem test_degree_budget_obstruction (degree rho : Q') (hd : (2 : Q') ≤ degree)
    (hbound : (2 : Q') * weightedPair 2 (relativeHeat testNome testCutoff) leftCoordinate rightCoordinate ≤
      rho * (weightedPair 2 (relativeHeat testNome testCutoff) leftCoordinate leftCoordinate +
        weightedPair 2 (relativeHeat testNome testCutoff) rightCoordinate rightCoordinate)) :
    ¬ degree * rho < 1 := by
  have hlo := coefficient_lower_bound testNome testCutoff (by unfold testCutoff; omega) hbound
  have hrho : (0 : Q') ≤ rho := Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ qpow testNome 3) hlo
  have hpay : (2 : Q') * qpow testNome 3 ≤ degree * rho :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ 2 hlo (by decide))
      (Q'.mul_le_mul_of_nonneg_right _ _ rho hd hrho)
  intro h
  have hbad : (1 : Q') < 1 := Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (2 : Q') * qpow testNome 3) hpay) h
  exact (by decide : ¬ ((1 : Q') < 1)) hbad

#print axioms heat_mass
#print axioms left_mean
#print axioms right_mean
#print axioms left_variance
#print axioms right_variance
#print axioms coordinate_covariance
#print axioms coefficient_lower_bound
#print axioms coefficient_deficit_le
#print axioms testWeightCertificate
#print axioms test_covariance
#print axioms test_degree_budget_obstruction

end YMGap.Continuum.SU2QuaternionSharedHeatCorrelationObstruction
