/-
# Identification of the two bounded ORIGINAL positive-time maps

The actual finite root/log norm comparison, the supplied representative's
norm ceiling, and the existing represented-limit uniqueness identify
derivativeAction with regularizedLog on the SAME all-nome Wilson completion.
Both original Cauchy constructions and the original boundary kernel remain.
This identifies the derivative of T(1)x with the regularized series map;
it is not a full-carrier unbounded logarithm/generator, an exponential
identity, a changing-family comparison, or a physical mass assertion.
-/

import YMGap.Continuum.BF4WilsonAllNomeRootLogNormComparison
import YMGap.Continuum.BF4WilsonAllNomeLogSeries

namespace YMGap.Continuum.BF4WilsonAllNomeRootLogIdentification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeDyadicContinuity (rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
  (differenceQuotient quotientRows quotientRows_pin derivativeAction derivativeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomeLogPartial (logPartial)
open YMGap.Continuum.BF4WilsonAllNomeLogSeries
  (regularizedLog regularizedLog_approximation convergenceModulus)
open YMGap.Continuum.BF4WilsonAllNomeRootLogNormComparison
  (errorCoefficient root_log_norm_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.RCPolynomialFunctional (rc_scale_coeff_add)

private theorem square_le_self {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1) :
    q*q ≤ q :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hq1 hq0)
    (Q'.le_of_eqv (Q'.one_mul_eqv q))

private theorem coefficient_budget (h v : Q')
    (hh0 : (0 : Q') ≤ h) (hh1 : h ≤ 1)
    (hv0 : (0 : Q') ≤ v) (hv1 : v ≤ 1) :
    (2*h+v)*(2*h+v) ≤ 8*h+2*v := by
  have hs := Q'.add_le_add_left ((2*h+v)*(2*h+v)) 0
    ((2*h + -v)*(2*h + -v)) (SumOfSquares.q_mul_self_nonneg _)
  have hzero : (((2*h+v)*(2*h+v))+0).eqv ((2*h+v)*(2*h+v)) :=
    QPoly.q_add_zero_eqv _
  have hex : (((2*h+v)*(2*h+v))+(2*h + -v)*(2*h + -v)).eqv
      (8*(h*h)+2*(v*v)) :=
    poly_identity_of_normal_eq
      (.add
        (.mul (.add (.mul (.const 2) (.var 0)) (.var 1))
          (.add (.mul (.const 2) (.var 0)) (.var 1)))
        (.mul (.add (.mul (.const 2) (.var 0)) (.neg (.var 1)))
          (.add (.mul (.const 2) (.var 0)) (.neg (.var 1)))))
      (.add (.mul (.const 8) (.mul (.var 0) (.var 0)))
        (.mul (.const 2) (.mul (.var 1) (.var 1)))) (by decide)
      (fun | 0 => h | _ => v)
  have hfirst := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hzero)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hex))
  have hh := Q'.mul_le_mul_of_nonneg_left _ _ (8 : Q')
    (square_le_self hh0 hh1) (by decide)
  have hv := Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
    (square_le_self hv0 hv1) (by decide)
  exact Q'.le_trans' _ _ _ hfirst (Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hh) (Q'.add_le_add_left _ _ _ hv))

private theorem quarter_budget (epsilon : Q') :
    RCadd (RCscale 8 (Quotient.mk crealSetoid (ofQ' (quarter (quarter epsilon)))))
      (RCscale 2 (Quotient.mk crealSetoid (ofQ' (quarter epsilon)))) =
      Quotient.mk crealSetoid (ofQ' epsilon) := by
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change (8*(half*(half*(half*(half*epsilon))))+2*(half*(half*epsilon))).eqv epsilon
  have halgebra :
      (8*(half*(half*(half*(half*epsilon))))+2*(half*(half*epsilon))).eqv
        ((8*(half*(half*(half*half)))+2*(half*half))*epsilon) :=
    poly_identity_of_normal_eq
    (.add (.mul (.const 8)
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.var 1))))))
      (.mul (.const 2) (.mul (.var 0) (.mul (.var 0) (.var 1)))))
    (.mul (.add (.mul (.const 8)
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 0) (.var 0)))))
      (.mul (.const 2) (.mul (.var 0) (.var 0)))) (.var 1))
    (by decide) (fun | 0 => half | _ => epsilon)
  exact Q'.eqv_trans _ _ _ halgebra (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ (1 : Q') epsilon (by decide)) (Q'.one_mul_eqv epsilon))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem two_segment (x y z : V) (epsilon : Q')
    (hxy : RCle (dist x y) (Rq (quarter epsilon)))
    (hyz : RCle (dist y z) (Rq (quarter epsilon))) :
    RCle (dist x z) (Rq epsilon) := by
  have hsum := RCadd_le_add (RCadd_le_add hxy hxy) (RCadd_le_add hyz hyz)
  have h := RCle_trans (completedDist_triangle hw0 hw1 x y z) hsum
  have hbudget : RCadd (RCadd (Rq (quarter epsilon)) (Rq (quarter epsilon)))
      (RCadd (Rq (quarter epsilon)) (Rq (quarter epsilon))) = Rq epsilon := by
    apply Quotient.sound
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (half*epsilon))
        (ExpNeg.two_halves (half*epsilon))) (ExpNeg.two_halves epsilon)
  rwa [hbudget] at h

/-- The SAME representative's tolerance denominator also bounds its harmonic
norm scale: rangeModulus is a rational denominator, not a log-scale index. -/
theorem harmonic_scaled_norm_small (X : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (m : Nat)
    (hm : rangeModulus hw0 hw1 X epsilon ≤ m) :
    RCle (RCscale (Q'.invSucc m) (B (Class X) (Class X))) (Rq epsilon) := by
  let cap := normCeiling PD X
  have hc : (0 : Q') ≤ cap := normCeiling_nonnegative PD X
  let tau := linearTolerance cap hc epsilon
  have hp : Q'.invSucc m ≤ tau := Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hm)
    (HalfPow.invSucc_den_le tau (linearTolerance_pos cap hc he))
  have hb : (Q'.invSucc m)*cap ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ cap hp hc)
      (linearTolerance_budget cap hc he))
  have h := RCscale_mono (Q'.invSucc_nonneg m)
    (completedInner_diagonal_le_normCeiling PD X)
  have hs : RCscale (Q'.invSucc m) (Rq cap) = Rq ((Q'.invSucc m)*cap) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hs] at h
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ => hb))

/-- Actual finite comparison with two explicit cutoffs from ONE supplied
original representative. No uniform norm ceiling is postulated. -/
theorem finite_comparison_small (X : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (d m : Nat) (hm0 : 0 < m)
    (hd : rangeModulus hw0 hw1 X (quarter (quarter epsilon)) ≤ d)
    (hm : rangeModulus hw0 hw1 X (quarter epsilon) ≤ m) :
    RCle (dist (differenceQuotient hw0 hw1 (d+2) (Class X))
      (logPartial hw0 hw1 m (Class X))) (Rq epsilon) := by
  have hh0 : (0 : Q') ≤ half^d := Q'.pow_nonneg half half_nonneg d
  have hh1 : half^d ≤ (1 : Q') := HKPos.pow_le_one half_nonneg (by decide) d
  have hv1 : Q'.invSucc m ≤ (1 : Q') :=
    ExpNeg.invSucc_le_of_le (Nat.zero_le m)
  have hb : errorCoefficient d m * errorCoefficient d m ≤ 8*half^d+2*Q'.invSucc m :=
    coefficient_budget (half^d) (Q'.invSucc m) hh0 hh1 (Q'.invSucc_nonneg m) hv1
  have hf := root_log_norm_bound hw0 hw1 d (Class X) m hm0
  rw [completedDist_symm] at hf
  have hc := RCle_trans hf
    (RCscale_scalar_mono hb (completedInner_nonnegative hw0 hw1 (Class X)))
  have hroot := RCscale_mono (by decide : (0 : Q') ≤ 8)
    (scaled_norm_small hw0 hw1 X (quarter (quarter epsilon))
      (quarter_pos (quarter_pos he)) d hd)
  have hlog := RCscale_mono (by decide : (0 : Q') ≤ 2)
    (harmonic_scaled_norm_small hw0 hw1 X (quarter epsilon) (quarter_pos he) m hm)
  rw [RCscale_RCscale] at hroot hlog
  have hs := RCadd_le_add hroot hlog
  rw [← rc_scale_coeff_add, quarter_budget] at hs
  exact RCle_trans hc hs

/-- Computed rate for the EXISTING quotient rows to approach regularizedLog. -/
def identificationRate (X : (D).Cauchy) (epsilon : Q') : Nat :=
  rangeModulus hw0 hw1 X (quarter (quarter (quarter epsilon))) + 2

/-- The literal quotient sequence converges to the already constructed
regularized series value, retaining the supplied representative and rate. -/
theorem quotient_to_log_bound (X : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : identificationRate hw0 hw1 X epsilon ≤ n) :
    RCle (dist (differenceQuotient hw0 hw1 n (Class X))
      (regularizedLog hw0 hw1 (Class X))) (Rq epsilon) := by
  let delta := quarter epsilon
  have hdelta : (0 : Q') < delta := quarter_pos he
  let m := max 1 (max (convergenceModulus hw0 hw1 X delta)
    (rangeModulus hw0 hw1 X (quarter delta)))
  have hm0 : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)
  have hmrange : rangeModulus hw0 hw1 X (quarter delta) ≤ m :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hmlog : convergenceModulus hw0 hw1 X delta ≤ m :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  let d := n-2
  have hd : rangeModulus hw0 hw1 X (quarter (quarter delta)) ≤ d := by
    change rangeModulus hw0 hw1 X (quarter (quarter delta))+2 ≤ n at hn
    dsimp [d]
    omega
  have hi : d+2 = n := by
    change rangeModulus hw0 hw1 X (quarter (quarter delta))+2 ≤ n at hn
    dsimp [d]
    omega
  have hfinite := finite_comparison_small hw0 hw1 X delta hdelta d m hm0 hd hmrange
  rw [hi] at hfinite
  exact two_segment hw0 hw1
    (differenceQuotient hw0 hw1 n (Class X)) (logPartial hw0 hw1 m (Class X))
    (regularizedLog hw0 hw1 (Class X)) epsilon hfinite
    (regularizedLog_approximation hw0 hw1 X delta hdelta m hmlog)

/-- Equality of the two EXISTING bounded original positive-time maps.
No root is cancelled and the original boundary kernel is not removed. -/
theorem derivativeAction_eq_regularizedLog (x : V) :
    derivativeAction hw0 hw1 x = regularizedLog hw0 hw1 x := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [derivativeAction_pin]
  apply limit_unique hw0 hw1 (quotientRows hw0 hw1 X)
    (regularizedLog hw0 hw1 (Class X)) (identificationRate hw0 hw1 X)
  intro epsilon he n hn
  rw [quotientRows_pin]
  exact quotient_to_log_bound hw0 hw1 X epsilon he n hn

#print axioms harmonic_scaled_norm_small
#print axioms finite_comparison_small
#print axioms identificationRate
#print axioms quotient_to_log_bound
#print axioms derivativeAction_eq_regularizedLog

end YMGap.Continuum.BF4WilsonAllNomeRootLogIdentification
