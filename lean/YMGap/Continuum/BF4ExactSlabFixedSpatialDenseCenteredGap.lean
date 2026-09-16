/-
# Strict two-step form bound on actual centered dense presentations

The same physical-time covariance envelope bounds the even moment at k by
separationCap*mixRate^(2*k). Its actual positivity, anchor contraction and
dyadic Cauchy--Schwarz inequality allow the generic scalar dyadic theorem
to remove the presentation-dependent prefactor. The resulting two-step
form rate is exactly mixRate*mixRate, retaining nome and width dependence.

The rational zero-rate branch uses the first even-moment envelope directly.
No positive-norm premise, scalar square root, chosen representative, assumed
decay estimate or unrelated rate shrink is used. This file treats centered
embedded physical presentations only. Extension to every completed unit-
orthogonal vector, nonzero excitations, continuum-uniform estimates and a
physical Hamiltonian gap are not asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion (center)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (dyadic_geometric_first_le)

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

/-- Two units of genuine physical time give the squared actual comparison
rate. It is independent of retained heat stage, but not of nome or width. -/
def twoStepRate (width : Nat) : Q' :=
  mixRate hw0 hw1 width * mixRate hw0 hw1 width

theorem twoStepRate_nonnegative (width : Nat) :
    (0 : Q') ≤ twoStepRate hw0 hw1 width :=
  Q'.mul_nonneg _ _ (mixRate_nonnegative hw0 hw1 width)
    (mixRate_nonnegative hw0 hw1 width)

theorem twoStepRate_lt_one (width : Nat) : twoStepRate hw0 hw1 width < (1 : Q') := by
  have hq := mixRate_lt_one hw0 hw1 width
  have hqq : twoStepRate hw0 hw1 width ≤ mixRate hw0 hw1 width :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hq)
        (mixRate_nonnegative hw0 hw1 width))
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.lt_of_le_of_lt hqq hq

private theorem double_power (q : Q') : ∀ k : Nat, q ^ (2*k) ≈ (q*q) ^ k
  | 0 => Q'.eqv_refl 1
  | k+1 => by
      have hindex : 2*(k+1) = (2*k+1)+1 := by omega
      rw [hindex]
      change q * (q * q ^ (2*k)) ≈ (q*q) * (q*q) ^ k
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left q _ _
          (Q'.mul_eqv_congr_left q _ _ (double_power q k)))
        (Q'.eqv_symm (Q'.mul_assoc_eqv q q ((q*q)^k)))

variable (width stage : Nat)

/-- The actual even moments have a geometric envelope with a computed
strictly positive prefactor. The prefactor is independent of the moment
index and will disappear from the final form inequality. -/
theorem evenMoment_le_geometric (x : PhysicalSpan width) (k : Nat) :
    leEv (evenMoment hw0 hw1 width stage x k)
      (ofQ' ((1 + separationCap width x.val x.val) * twoStepRate hw0 hw1 width ^ k)) := by
  let A := separationCap width x.val x.val
  let q := mixRate hw0 hw1 width
  have hA : A ≤ 1+A :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg A 1 Q'.zero_le_one)
      (Q'.le_of_eqv (Q'.add_comm_eqv A 1))
  have hscale : A * q ^ (2*k) ≤ (1+A) * q ^ (2*k) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hA
      (Q'.pow_nonneg q (mixRate_nonnegative hw0 hw1 width) (2*k))
  have hp : A * q ^ (2*k) ≤ (1+A) * twoStepRate hw0 hw1 width ^ k :=
    Q'.le_trans' _ _ _ hscale
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (1+A) _ _ (double_power q k)))
  exact leEv_trans (centeredMoment_le hw0 hw1 width stage (2*k) x x)
    (leEv_ofQ'_of_approx_ge (fun _ => hp))

/-- Dyadic prefactor removal on the actual even moments. The zero-rate
branch is included and never divides by the initial reflected norm. -/
theorem evenMoment_first_le (x : PhysicalSpan width) :
    leEv (evenMoment hw0 hw1 width stage x 1)
      (mul (ofQ' (twoStepRate hw0 hw1 width)) (evenMoment hw0 hw1 width stage x 0)) := by
  let q := mixRate hw0 hw1 width
  let A := separationCap width x.val x.val
  let P := 1+A
  by_cases hq : (0 : Q') < q
  · exact dyadic_geometric_first_le
      (evenMoment hw0 hw1 width stage x) (twoStepRate hw0 hw1 width) P
      (Q'.mul_pos hq hq)
      (TuranPositivity.q_pos_add_nonneg (by decide : (0 : Q') < 1)
        (separationCap_nonnegative width x.val x.val))
      (evenMoment_nonnegative hw0 hw1 width stage x)
      (evenMoment_le_zero hw0 hw1 width stage x)
      (evenMoment_dyadic hw0 hw1 width stage x)
      (evenMoment_le_geometric hw0 hw1 width stage x)
  · have hqle : q ≤ (0 : Q') := by
      show q.num * ((0 : Q').den : Int) ≤ (0 : Q').num * (q.den : Int)
      exact Int.not_lt.mp hq
    have hqzero : q ≈ 0 := ExpNeg.eqv_of_le_le hqle (mixRate_nonnegative hw0 hw1 width)
    have hrzero : twoStepRate hw0 hw1 width ≈ 0 :=
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ q hqzero) (QPoly.q_zero_mul q)
    have hcapzero : P * twoStepRate hw0 hw1 width ^ (1 : Nat) ≈ 0 :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left P _ _
          (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) hrzero))
        (QPoly.q_mul_zero P)
    have hsmall : leEv (evenMoment hw0 hw1 width stage x 1) czero :=
      leEv_trans (evenMoment_le_geometric hw0 hw1 width stage x 1)
        (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ => hcapzero)))
    have hright : Equiv
        (mul (ofQ' (twoStepRate hw0 hw1 width)) (evenMoment hw0 hw1 width stage x 0)) czero :=
      SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ ((evenMoment hw0 hw1 width stage x 0).approx k) hrzero)
          (QPoly.q_zero_mul _))
    exact leEv_trans hsmall (leEv_of_equiv hright.symm)

/-- Actual dense centered two-step reflected form bound, with common rate
strictly below one at each fixed nome and width. This is not yet an
extension to arbitrary completed unit-complement vectors. -/
theorem dense_twoStep_form_gap (x : PhysicalSpan width) :
    RCle (completedInner hw0 hw1 width stage
        (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage x))
        (completedTime hw0 hw1 width stage 2
          (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage x))))
      (RCscale (twoStepRate hw0 hw1 width)
        (completedInner hw0 hw1 width stage
          (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage x))
          (center hw0 hw1 width stage (embedSpan hw0 hw1 width stage x)))) := by
  have hpin := evenMoment_pin hw0 hw1 width stage x 1
  rw [hpin, evenMoment_zero_pin]
  exact evenMoment_first_le hw0 hw1 width stage x

end YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap.twoStepRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap.twoStepRate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap.twoStepRate_lt_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap.evenMoment_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap.evenMoment_first_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap.dense_twoStep_form_gap
