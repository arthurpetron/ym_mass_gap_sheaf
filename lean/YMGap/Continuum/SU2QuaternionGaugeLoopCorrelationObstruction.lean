/-
# Closing the tests into Wilson loops does not repair the factor-only budget

The same two endpoint gauges act on all three path holonomies C,A,B.
The literal tests scalar(C A^-1), scalar(C B^-1) are invariant closed loops.
Their covariance in the complete A/B heat packet is w^3/4 and their
variances are 1/4. Hence any symmetric correlation coefficient pays w^3.

The positive example w=7/8 excludes degree*rho<1 for degree>=2 even with
these invariant tests. This does NOT assert that the original full-slab
one-sided action factors are absent or harmless, and is not a YM no-go.
-/

import YMGap.Continuum.SU2QuaternionSharedHeatLoopMoments
import YMGap.Continuum.SU2QuaternionParallelLoopGauge
import YMGap.Continuum.QuaternionHaarWordLift

namespace YMGap.Continuum.SU2QuaternionGaugeLoopCorrelationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionParallelLoopGauge
open YMGap.Continuum.SU2QuaternionSharedHeatLoopMoments
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarWordLift
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local prefix:80 "bar " => PolyQuaternion.conj
local infixl:70 " *q " => PolyQuaternion.mul

/-- The packet used in every moment is the A/B closed-loop packet. Padding
only accounts for the fresh common path in the constant character term. -/
theorem weight_pair_pin (blocks : Nat) (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv blocks (weight w K) (heatAt 1 2 w K) := by
  have hs : liftBoundary 1 relativeScalar = scalarAt 1 2 := by
    change (liftQuaternion 1 (PolyQuaternion.coordinateVariable 0 *q
      bar (PolyQuaternion.coordinateVariable 1))).scalar = _
    rw [liftQuaternion_mul, liftQuaternion_conj,
      liftQuaternion_coordinateVariable, liftQuaternion_coordinateVariable]
    rfl
  unfold weight relativeHeat heatAt
  change PaddedPolynomialCoeffEqv blocks (liftBoundary 1 _) _
  induction List.range (K+1) with
  | nil => exact .refl _ _
  | cons spin spins ih =>
      change PaddedPolynomialCoeffEqv blocks (liftBoundary 1 (polyAdd _ _)) (polyAdd _ _)
      rw [lift_add, lift_smul]
      have hc := lift_character blocks 1 relativeScalar spin
      rw [hs] at hc
      exact (hc.smul _).add ih

/-- The padded packet pin is valid beneath every supported insertion on
the actual three-path Haar carrier; both support premises are supplied. -/
theorem weight_pair_haar (w : Q') (K : Nat) :
    SupportedHaarEqv 3 (weight w K) (heatAt 1 2 w K) :=
  SupportedHaarEqv.of_padded (weight_pair_pin 3 w K)
    (lift_supported (SU2QuaternionRelativeHeatMarkovData.relativeHeat_supported w K) 1)
    (heat_supported (by decide : 1 < 3) (by decide : 2 < 3) w K)

/-- Both loops use the SAME endpoints and the SAME common path C. -/
theorem loops_gauge_invariant {blocks : Nat} (start finish : PolyQuaternion)
    (hs : HaarCarrierEqv blocks (polyQuaternionNorm start) polyOne)
    (ht : HaarCarrierEqv blocks (polyQuaternionNorm finish) polyOne) :
    HaarCarrierEqv blocks
      (gaugeLink start (PolyQuaternion.coordinateVariable 0) finish *q
        bar (gaugeLink start (PolyQuaternion.coordinateVariable 1) finish)).scalar leftLoop ∧
    HaarCarrierEqv blocks
      (gaugeLink start (PolyQuaternion.coordinateVariable 0) finish *q
        bar (gaugeLink start (PolyQuaternion.coordinateVariable 2) finish)).scalar rightLoop :=
  ⟨parallel_loop_gauge_scalar start finish _ _ hs ht,
    parallel_loop_gauge_scalar start finish _ _ hs ht⟩

/-- Every heat-packet character uses the same endpoint invariance too. -/
theorem heat_character_gauge_invariant {blocks : Nat} (start finish : PolyQuaternion)
    (hs : HaarCarrierEqv blocks (polyQuaternionNorm start) polyOne)
    (ht : HaarCarrierEqv blocks (polyQuaternionNorm finish) polyOne) (spin : Nat) :
    HaarCarrierEqv blocks
      (characterPolynomial
        (gaugeLink start (PolyQuaternion.coordinateVariable 1) finish *q
          bar (gaugeLink start (PolyQuaternion.coordinateVariable 2) finish)).scalar spin)
      (characterPolynomial
        (PolyQuaternion.coordinateVariable 1 *q bar (PolyQuaternion.coordinateVariable 2)).scalar spin) :=
  parallel_loop_gauge_character start finish _ _ hs ht spin

private theorem coordinate_bound_of_loop_bound (w : Q') (K : Nat) (hK : 1 ≤ K) (rho : Q')
    (h : (2 : Q') * weightedPair 3 (weight w K) leftLoop rightLoop ≤
      rho * (weightedPair 3 (weight w K) leftLoop leftLoop +
        weightedPair 3 (weight w K) rightLoop rightLoop)) :
    (2 : Q') * weightedPair 2 (relativeHeat w K)
      SU2QuaternionSharedHeatCorrelationObstruction.leftCoordinate
      SU2QuaternionSharedHeatCorrelationObstruction.rightCoordinate ≤
    rho * (weightedPair 2 (relativeHeat w K)
      SU2QuaternionSharedHeatCorrelationObstruction.leftCoordinate
      SU2QuaternionSharedHeatCorrelationObstruction.leftCoordinate +
      weightedPair 2 (relativeHeat w K)
        SU2QuaternionSharedHeatCorrelationObstruction.rightCoordinate
        SU2QuaternionSharedHeatCorrelationObstruction.rightCoordinate) := by
  have hc := Q'.eqv_trans _ _ _
    (SU2QuaternionSharedHeatCorrelationObstruction.coordinate_covariance w K hK)
    (Q'.eqv_symm (covariance w K hK))
  have hl := Q'.eqv_trans _ _ _ (left_variance w K)
    (Q'.eqv_symm (SU2QuaternionSharedHeatCorrelationObstruction.left_variance w K))
  have hr := Q'.eqv_trans _ _ _ (right_variance w K)
    (Q'.eqv_symm (SU2QuaternionSharedHeatCorrelationObstruction.right_variance w K))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hc))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' hl hr))))

/-- The normalized closed-loop correlation is still exactly w^3. -/
theorem coefficient_lower_bound (w : Q') (K : Nat) (hK : 1 ≤ K) (rho : Q')
    (h : (2 : Q') * weightedPair 3 (weight w K) leftLoop rightLoop ≤
      rho * (weightedPair 3 (weight w K) leftLoop leftLoop +
        weightedPair 3 (weight w K) rightLoop rightLoop)) : qpow w 3 ≤ rho :=
  SU2QuaternionSharedHeatCorrelationObstruction.coefficient_lower_bound w K hK
    (coordinate_bound_of_loop_bound w K hK rho h)

local notation "wTest" => SU2QuaternionSharedHeatCorrelationObstruction.testNome
local notation "kTest" => SU2QuaternionSharedHeatCorrelationObstruction.testCutoff

def testWeightCertificate : Certificate 3 (weight wTest kTest) :=
  weightCertificate (by decide) (by decide) kTest (by
    unfold SU2QuaternionSharedHeatCorrelationObstruction.testCutoff
    omega)

/-- A positive full-cutoff packet and invariant closed-loop tests exclude
the shared-factor-only degree budget. No original full-action bound is refuted. -/
theorem test_degree_budget_obstruction (degree rho : Q') (hd : (2 : Q') ≤ degree)
    (h : (2 : Q') * weightedPair 3 (weight wTest kTest) leftLoop rightLoop ≤
      rho * (weightedPair 3 (weight wTest kTest) leftLoop leftLoop +
        weightedPair 3 (weight wTest kTest) rightLoop rightLoop)) : ¬ degree * rho < 1 :=
  SU2QuaternionSharedHeatCorrelationObstruction.test_degree_budget_obstruction degree rho hd
    (coordinate_bound_of_loop_bound wTest kTest (by
      unfold SU2QuaternionSharedHeatCorrelationObstruction.testCutoff
      omega) rho h)

#print axioms loops_gauge_invariant
#print axioms weight_pair_pin
#print axioms weight_pair_haar
#print axioms heat_character_gauge_invariant
#print axioms coefficient_lower_bound
#print axioms testWeightCertificate
#print axioms test_degree_budget_obstruction

end YMGap.Continuum.SU2QuaternionGaugeLoopCorrelationObstruction
