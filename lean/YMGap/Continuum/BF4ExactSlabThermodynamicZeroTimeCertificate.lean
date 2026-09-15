/-
# Finite ORIGINAL moment certificates for a time-zero continuity tolerance

For supplied original state data X, the test reads a rational sample of
the EXISTING mixed moment m_X(0,2n), with its EXISTING QCauchy modulus.
Acceptance bounds ||D^n X||^2 by epsilon/16. The exact finite preimage
identity and contraction then turn the known T2-range continuity radius
into a radius for X itself at tolerance epsilon. All output data are
computed; no successful unbounded search or range-density premise occurs.

Conversely a supplied moment bound epsilon/32 computes an accepted test.
The preceding energy theorem instantiates these certificates on actual
T2 outputs for every positive tolerance. Successful certificates at all
tolerances for EVERY original dense observable remain unproved. This
finite format is not an additional analytic frontier or a new state space.
Fixed SU(2) nome/spacing; full-space time-zero continuity, physical
Hamiltonian identification, continuum and Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy
import YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner (completedInner)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit (dist_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer timeCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicRangeDefectEnergy
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealSemigroup (realTimeAction_distance_contraction)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRealLocalContinuity (localRadius localRadius_positive)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveRangeZeroContinuity
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
  (completedDist_two_segment completedDist_three_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

private theorem rational_order {a b : Q'} (h : leEv (ofQ' a) (ofQ' b)) : a ≤ b := by
  apply Q'.le_of_forall_pos_add
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact hN N (Nat.le_refl N)

def sample (X : seminorm.Cauchy) (degree index : Nat) : Q' :=
  (momentRepresentative X 0 (degree+degree)).approx index

/-- Numerical enclosure without unfolding a large physical representative. -/
theorem cauchy_sample_interval (r : CReal) (cr : QCauchy r.approx) (delta : Q')
    (hd : (0 : Q') < delta) (index : Nat) (hi : cr.M delta ≤ index) :
    leEv (ofQ' (r.approx index)) (CReal.add r (ofQ' delta)) ∧
    leEv r (ofQ' (r.approx index + delta)) := by
  constructor
  · intro epsilon he
    refine ⟨cr.M delta, fun n hn => ?_⟩
    change r.approx index ≤ (r.approx n + delta) + epsilon
    exact Q'.le_trans' _ _ _ (cr.bound delta hd index n hi hn).1
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))
  · intro epsilon he
    refine ⟨cr.M delta, fun n hn => ?_⟩
    change r.approx n ≤ (r.approx index + delta) + epsilon
    exact Q'.le_trans' _ _ _ (cr.bound delta hd index n hi hn).2
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))

/-- A single, explicitly modulus-controlled sample encloses the original moment. -/
theorem sample_interval (X : seminorm.Cauchy) (degree : Nat) (delta : Q')
    (hd : (0 : Q') < delta) (index : Nat)
    (hi : (momentCauchy X 0 (degree+degree)).M delta ≤ index) :
    RCle (rat (sample X degree index))
      (RCadd (mixedMoment (point X) 0 (degree+degree)) (rat delta)) ∧
    RCle (mixedMoment (point X) 0 (degree+degree))
      (rat (sample X degree index + delta)) := by
  rw [moment_pin]
  exact cauchy_sample_interval (momentRepresentative X 0 (degree+degree))
    (momentCauchy X 0 (degree+degree)) delta hd index hi

/-- Only finite rational/natural comparisons, with no real equality test. -/
def check (X : seminorm.Cauchy) (epsilon : Q') (degree : Nat) (delta : Q') (index : Nat) : Bool :=
  decide ((0 : Q') < epsilon ∧ (0 : Q') < delta ∧
    (momentCauchy X 0 (degree+degree)).M delta ≤ index ∧
    sample X degree index + delta ≤ quarter (quarter epsilon))

/-- Finite certificate data for ONE original state and ONE tolerance. -/
structure Certificate (X : seminorm.Cauchy) (epsilon : Q') where
  degree : Nat
  tolerance : Q'
  index : Nat
  accepted : check X epsilon degree tolerance index = true

theorem Certificate.epsilon_positive {X : seminorm.Cauchy} {epsilon : Q'}
    (c : Certificate X epsilon) : (0 : Q') < epsilon :=
  (of_decide_eq_true c.accepted).1

theorem Certificate.residual_bound {X : seminorm.Cauchy} {epsilon : Q'}
    (c : Certificate X epsilon) :
    RCle (mixedMoment (point X) 0 (c.degree+c.degree)) (rat (quarter (quarter epsilon))) := by
  have h := of_decide_eq_true c.accepted
  exact RCle_trans (sample_interval X c.degree c.tolerance h.2.1 c.index h.2.2.1).2
    (leEv_le_ofQ'_of_approx_le (fun _ => h.2.2.2))

def Certificate.radius {X : seminorm.Cauchy} {epsilon : Q'} (c : Certificate X epsilon) : Q' :=
  localRadius oneTimeData (partialPreimageCauchy c.degree X) (quarter (quarter epsilon))

theorem Certificate.radius_positive {X : seminorm.Cauchy} {epsilon : Q'}
    (c : Certificate X epsilon) : (0 : Q') < c.radius :=
  localRadius_positive oneTimeData (partialPreimageCauchy c.degree X) (quarter (quarter epsilon))

theorem Certificate.range_error {X : seminorm.Cauchy} {epsilon : Q'} (c : Certificate X epsilon) :
    RCle (completedDist (point X) (twoStepTransfer (point (partialPreimageCauchy c.degree X)) ))
      (rat (quarter (quarter epsilon))) := by
  rw [partialPreimageCauchy_pin, partialPreimage_distance]
  exact c.residual_bound

theorem Certificate.zero_bound {X : seminorm.Cauchy} {epsilon : Q'}
    (c : Certificate X epsilon) (t : PositiveTimeValue)
    (ht : RCle (realValue t) (rat c.radius)) :
    RCle (completedDist (realTimeAction t (point X)) (point X)) (rat epsilon) := by
  let y := twoStepTransfer (point (partialPreimageCauchy c.degree X))
  have hxy : RCle (completedDist (point X) y) (rat (quarter (quarter epsilon))) := c.range_error
  apply completedDist_three_segment (realTimeAction t (point X)) (realTimeAction t y) y
    (point X) epsilon c.epsilon_positive
  · exact RCle_trans (realTimeAction_distance_contraction t (point X) y) hxy
  · exact twoStep_range_zero_bound (partialPreimageCauchy c.degree X) (quarter (quarter epsilon))
      (quarter_pos (quarter_pos c.epsilon_positive)) t ht
  · rw [completedDist_symm]
    exact hxy

/-- A successful finite test computes a genuine zero-time radius for X. -/
def Certificate.continuityData {X : seminorm.Cauchy} {epsilon : Q'} (c : Certificate X epsilon) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ t : PositiveTimeValue, RCle (realValue t) (rat delta) →
        RCle (completedDist (realTimeAction t (point X)) (point X)) (rat epsilon)) :=
  ⟨c.radius, c.radius_positive, fun t ht => c.zero_bound t ht⟩

private theorem sample_budget (b : Q') : Q'.eqv ((HalfPow.half*b + quarter b) + quarter b) b :=
  Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves (HalfPow.half*b)))
      (ExpNeg.two_halves b))

/-- A quantitative moment bound constructs acceptance, not an unbounded search. -/
def certificateOfMomentBound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (degree : Nat)
    (hm : RCle (mixedMoment (point X) 0 (degree+degree))
      (rat (HalfPow.half * quarter (quarter epsilon)))) : Certificate X epsilon := by
  let b := quarter (quarter epsilon)
  let delta := quarter b
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos (quarter_pos he))
  let index := (momentCauchy X 0 (degree+degree)).M delta
  have hs := (sample_interval X degree delta hd index (Nat.le_refl _)).1
  have hq : sample X degree index ≤ HalfPow.half*b + delta :=
    rational_order (RCle_trans hs (RCadd_le_add hm (RCle_refl (rat delta))))
  have hguard : sample X degree index + delta ≤ b :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ delta hq) (Q'.le_of_eqv (sample_budget b))
  exact ⟨degree, delta, index, decide_eq_true ⟨he, hd, Nat.le_refl _, hguard⟩⟩

/-- Concrete accepted certificates on every actual T2 output, at every tolerance.
The degree is computed from the supplied ORIGINAL preimage data. -/
def rangeCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Certificate (timeCauchy 2 X) epsilon :=
  certificateOfMomentBound (timeCauchy 2 X) epsilon he
    (residualDegree X (HalfPow.half * quarter (quarter epsilon)))
    (range_residual_small X (HalfPow.half * quarter (quarter epsilon))
      (ExpNeg.half_mul_pos _ (quarter_pos (quarter_pos he))))

/-- A supplied nearby ORIGINAL transfer output computes a small residual for X.
Neither the preimage Y nor its approximation estimate is postulated globally. -/
theorem nearby_range_residual (X Y : seminorm.Cauchy) (eta : Q') (he : (0 : Q') < eta)
    (hxy : RCle (completedDist (point X) (twoStepTransfer (point Y))) (rat (quarter eta))) :
    RCle (mixedMoment (point X) 0
      (residualDegree Y (quarter eta) + residualDegree Y (quarter eta))) (rat eta) := by
  let n := residualDegree Y (quarter eta)
  have h := completedDist_two_segment (defectPower n (point X))
    (defectPower n (twoStepTransfer (point Y))) completedZero eta
    (RCle_trans (defectPower_distance_contraction n (point X) (twoStepTransfer (point Y))) hxy)
    (by rw [dist_zero, residual_norm_moment]; exact range_residual_small Y (quarter eta) (quarter_pos he))
  rw [dist_zero, residual_norm_moment] at h
  exact h

/-- Quantitative converse: an actual epsilon/128 range approximation supplies
the finite accepted test at tolerance epsilon, with no representative choice. -/
def certificateOfRangeApproximation (X Y : seminorm.Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon)
    (hxy : RCle (completedDist (point X) (twoStepTransfer (point Y)))
      (rat (quarter (HalfPow.half * quarter (quarter epsilon))))) : Certificate X epsilon :=
  certificateOfMomentBound X epsilon he
    (residualDegree Y (quarter (HalfPow.half * quarter (quarter epsilon))))
    (nearby_range_residual X Y (HalfPow.half * quarter (quarter epsilon))
      (ExpNeg.half_mul_pos _ (quarter_pos (quarter_pos he))) hxy)

end YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.sample
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.cauchy_sample_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.sample_interval
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.check
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate.epsilon_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate.residual_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate.radius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate.radius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate.range_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate.zero_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.Certificate.continuityData
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.certificateOfMomentBound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.rangeCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.nearby_range_residual
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicZeroTimeCertificate.certificateOfRangeApproximation
