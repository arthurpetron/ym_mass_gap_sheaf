/-
# Dense two-step bound for the literal-width all-nome Wilson form

The actual centered covariance envelope, even-time positivity, and dyadic
moment inequality remove the expression-dependent prefactor.  The resulting
rate is the existing rational `mixRate^2` at the same nome and literal width.

This is a dense intrinsic form estimate.  It is not yet a statement about
all completed vectors or a width-uniform/continuum gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
import YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4WilsonAllNomeDenseGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
open YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (dyadic_geometric_first_le)

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

private theorem double_power (q : Q') : forall k : Nat, q ^ (2*k) ≈ (q*q) ^ k
  | 0 => Q'.eqv_refl 1
  | k+1 => by
      have hindex : 2*(k+1) = (2*k+1)+1 := by omega
      rw [hindex]
      change q * (q * q ^ (2*k)) ≈ (q*q) * (q*q) ^ k
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left q _ _
          (Q'.mul_eqv_congr_left q _ _ (double_power q k)))
        (Q'.eqv_symm (Q'.mul_assoc_eqv q q ((q*q)^k)))

/-- The centered even moments have a geometric envelope with a strictly
positive auxiliary prefactor, which disappears in `evenMoment_first_le`. -/
theorem evenMoment_le_geometric {width : Nat}
    (x : IntrinsicExpression width) (k : Nat) :
    leEv (evenMoment hw0 hw1 x k)
      (ofQ' ((1 + separationCap x x) * twoStepRate hw0 hw1 width ^ k)) := by
  let A := separationCap x x
  let q := mixRate hw0 hw1 width
  have hA : A <= 1+A :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg A 1 Q'.zero_le_one)
      (Q'.le_of_eqv (Q'.add_comm_eqv A 1))
  have hscale : A * q ^ (2*k) <= (1+A) * q ^ (2*k) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hA
      (Q'.pow_nonneg q (mixRate_nonnegative hw0 hw1 width) (2*k))
  have hp : A * q ^ (2*k) <= (1+A) * twoStepRate hw0 hw1 width ^ k :=
    Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (1+A) _ _ (double_power q k)))
  exact leEv_trans (intrinsic_centered_covariance_le hw0 hw1 (2*k) x x)
    (leEv_ofQ'_of_approx_ge (fun _ => hp))

/-- Dyadic removal includes the rational zero-rate branch and does not divide
by the initial centered norm. -/
theorem evenMoment_first_le {width : Nat} (x : IntrinsicExpression width) :
    leEv (evenMoment hw0 hw1 x 1)
      (mul (ofQ' (twoStepRate hw0 hw1 width)) (evenMoment hw0 hw1 x 0)) := by
  let q := mixRate hw0 hw1 width
  let A := separationCap x x
  let P := 1+A
  by_cases hq : (0 : Q') < q
  · exact dyadic_geometric_first_le
      (evenMoment hw0 hw1 x) (twoStepRate hw0 hw1 width) P
      (Q'.mul_pos hq hq)
      (TuranPositivity.q_pos_add_nonneg (by decide : (0 : Q') < 1)
        (separationCap_nonnegative x x))
      (evenMoment_nonnegative hw0 hw1 x)
      (evenMoment_le_zero hw0 hw1 x)
      (evenMoment_dyadic hw0 hw1 x)
      (evenMoment_le_geometric hw0 hw1 x)
  · have hqle : q <= (0 : Q') := by
      show q.num * ((0 : Q').den : Int) <= (0 : Q').num * (q.den : Int)
      exact Int.not_lt.mp hq
    have hqzero : q ≈ 0 :=
      ExpNeg.eqv_of_le_le hqle (mixRate_nonnegative hw0 hw1 width)
    have hrzero : twoStepRate hw0 hw1 width ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ q hqzero) (QPoly.q_zero_mul q)
    have hcapzero : P * twoStepRate hw0 hw1 width ^ (1 : Nat) ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left P _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) hrzero))
        (QPoly.q_mul_zero P)
    have hsmall : leEv (evenMoment hw0 hw1 x 1) czero :=
      leEv_trans (evenMoment_le_geometric hw0 hw1 x 1)
        (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ => hcapzero)))
    have hright : Equiv
        (mul (ofQ' (twoStepRate hw0 hw1 width)) (evenMoment hw0 hw1 x 0)) czero :=
      SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ ((evenMoment hw0 hw1 x 0).approx k) hrzero)
          (QPoly.q_zero_mul _))
    exact leEv_trans hsmall (leEv_of_equiv hright.symm)

/-- Prefactor-free two-step estimate for every actual intrinsic expression. -/
theorem centered_twoStep_bound {width : Nat} (x : IntrinsicExpression width) :
    leEv (centeredTimeMoment hw0 hw1 2 x x)
      (mul (ofQ' (twoStepRate hw0 hw1 width))
        (centeredTimeMoment hw0 hw1 0 x x)) := by
  simpa only [evenMoment, Nat.mul_one, Nat.mul_zero] using
    evenMoment_first_le hw0 hw1 x

#print axioms evenMoment_le_geometric
#print axioms evenMoment_first_le
#print axioms centered_twoStep_bound

end YMGap.Continuum.BF4WilsonAllNomeDenseGap
