/-
# Bounded rational-linear inverse for the SAME spatial-union defect

The actual equation R x = center x + T_2 R x and the weighted square
identity give ||R x||^2 <= K ||center x||^2 <= K ||x||^2, with the explicit
K=(1-q(w))^(-2). Only the positive rational q(w)*(1-q(w))^2 is cancelled,
never a vector norm. No continuity of arbitrary quotient-valued row norms
or spectral decomposition is assumed.

Inverse uniqueness proves rational linearity, commutation with actual time,
and the squared-distance bound on the SAME carrier. This is not a full real
module, a continuous-time generator or a spacing-uniform physical gap.
-/

import YMGap.Continuum.BF4SpatialUnionResolvent
import YMGap.Continuum.MeanExpConvexProgress

namespace YMGap.Continuum.BF4SpatialUnionResolventBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionLinearLaws
open YMGap.Continuum.BF4SpatialUnionUnitComplement
open YMGap.Continuum.BF4SpatialUnionCentered
open YMGap.Continuum.BF4SpatialUnionCompletedDistance
open YMGap.Continuum.BF4SpatialUnionRelaxation
open YMGap.Continuum.BF4SpatialUnionWeightedNorm
open YMGap.Continuum.BF4SpatialUnionResolventPartial
open YMGap.Continuum.BF4SpatialUnionResolvent
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem rc_add_cancel (a b c : RC)
    (h : RCle (RCadd a c) (RCadd b c)) : RCle a b := by
  revert h
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C h epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  refine ⟨N, fun n hn => ?_⟩
  apply le_of_add_le_add_right (c := C.approx n)
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv
    (RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => B.approx n | 1 => C.approx n | _ => epsilon)))

private theorem scale_cancel {a : Q'} (ha : (0 : Q') < a) {x y : RC}
    (h : RCle (RCscale a x) (RCscale a y)) : RCle x y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h epsilon he
  obtain ⟨N, hN⟩ := h (a*epsilon) (Q'.mul_pos ha he)
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (hN n hn)
      (Q'.ge_of_eqv (Q'.mul_add_eqv a (Y.approx n) epsilon))) ha

private theorem norm_split (r : Q') (a : RC) :
    RCscale (r*(1-r)) a =
      RCadd (RCscale (r*(1-r)*(1-r)) a) (RCscale ((1-r)*(r*r)) a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 0)))) (.var 1))
      (.add
        (.mul (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 0))))
          (.add (.const 1) (.neg (.var 0)))) (.var 1))
        (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.mul (.var 0) (.var 0))) (.var 1)))
      (by decide) (fun | 0 => r | _ => A.approx n)))

private theorem budget_factor (r : Q') (hr1 : r < (1 : Q')) :
    ((r*(1-r)*(1-r))*budget r hr1).eqv r := by
  have heq : ((r*(1-r)*(1-r))*budget r hr1).eqv
      (r*(budget r hr1*((1-r)*(1-r)))) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => r | 1 => 1-r | _ => budget r hr1)
  exact Q'.eqv_trans _ _ _ heq
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left r _ _ (budget_mul_square r hr1)) (Q'.mul_one_eqv r))

/-- Cancel a common tail and only the positive rational r*(1-r)^2. -/
theorem norm_budget_cancel (r : Q') (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (a c : RC)
    (h : RCle (RCscale (r*(1-r)) a)
      (RCadd (RCscale r c) (RCscale ((1-r)*(r*r)) a))) :
    RCle a (RCscale (budget r hr1) c) := by
  rw [norm_split] at h
  have hc := rc_add_cancel _ _ _ h
  apply scale_cancel (a := r*(1-r)*(1-r))
    (Q'.mul_pos (Q'.mul_pos hr0 (HKPos.one_sub_pos hr1)) (HKPos.one_sub_pos hr1))
  rw [RCscale_RCscale, scale_congr (budget_factor r hr1)]
  exact hc

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "C" => center hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "S" => completedSmul hw0 hw1 hsmall hd hs
local notation "Sub" => completedSub hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "R" => resolvent hw0 hw1 hsmall hd hs
local notation "F" => defect hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd
local notation "K" => budget q (twoStepRate_lt_one hw0 hd hs)

theorem resolvent_norm_centered_bound (x : V) :
    RCle (B (R x) (R x)) (RCscale K (B (C x) (C x))) := by
  have ht := centered_norm_decay hw0 hw1 hsmall hd hs (R x) 2
  rw [resolvent_centered] at ht
  have hq2 : (q^2).eqv (q*q) :=
    Q'.mul_eqv_congr_left q (q*1) q (Q'.mul_one_eqv q)
  rw [scale_congr hq2] at ht
  have h := RCle_trans
    (norm_weighted_add hw0 hw1 hsmall hd hs q (twoStepRate_positive hw0 hd)
      (twoStepRate_lt_one hw0 hd hs) (C x) (T 2 (R x)))
    (RCadd_le_add (RCle_refl _)
      (RCscale_mono (s := 1-q) (Q'.le_of_lt (HKPos.one_sub_pos
        (twoStepRate_lt_one hw0 hd hs))) ht))
  rw [← resolvent_equation, RCscale_RCscale] at h
  exact norm_budget_cancel q (twoStepRate_positive hw0 hd)
    (twoStepRate_lt_one hw0 hd hs) _ _ h

/-- Uniform in the vector, with the nome-dependent budget displayed explicitly. -/
theorem resolvent_norm_bound (x : V) :
    RCle (B (R x) (R x)) (RCscale K (B x x)) :=
  RCle_trans (resolvent_norm_centered_bound hw0 hw1 hsmall hd hs x)
    (RCscale_mono (budget_nonnegative q (twoStepRate_lt_one hw0 hd hs))
      (center_norm_le hw0 hw1 hsmall hd hs x))

theorem centered_eq_of_defect_eq (x y : V)
    (hx : C x = x) (hy : C y = y) (h : F x = F y) : x = y := by
  have he := congrArg R h
  rw [resolvent_left_inverse, resolvent_left_inverse, hx, hy] at he
  exact he

private theorem rc_sub_swap (a b c d : RC) :
    RCsub (RCsub a b) (RCsub c d) = RCsub (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro X0 Y0
  refine Quotient.inductionOn₂ c d ?_
  intro Z0 W0
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => X0.approx n | 1 => Y0.approx n | 2 => Z0.approx n | _ => W0.approx n)))

theorem defect_sub (x y : V) : F (Sub x y) = Sub (F x) (F y) := by
  unfold defect
  rw [completedTime_sub]
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  simp only [completedInner_sub_left]
  exact rc_sub_swap _ _ _ _

theorem resolvent_sub (x y : V) : R (Sub x y) = Sub (R x) (R y) := by
  apply centered_eq_of_defect_eq hw0 hw1 hsmall hd hs _ _
    (resolvent_centered hw0 hw1 hsmall hd hs _)
  · rw [center_sub, resolvent_centered, resolvent_centered]
  · rw [resolvent_right_inverse, defect_sub, resolvent_right_inverse,
      resolvent_right_inverse, center_sub]

theorem resolvent_add (x y : V) : R (A x y) = A (R x) (R y) := by
  have h := congrArg (fun a => A a (R y)) (resolvent_sub hw0 hw1 hsmall hd hs (A x y) y)
  dsimp only at h
  rw [sub_add_right_cancel, completedSub_add_cancel] at h
  exact h.symm

theorem defect_smul (s : Q') (x : V) : F (S s x) = S s (F x) := by
  unfold defect
  rw [completedTime_smul]
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  simp only [completedInner_sub_left, completedInner_smul_left]
  refine Quotient.inductionOn₂ (B x z) (B (T 2 x) z) ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv s (X.approx n) (-(Y.approx n)))
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_neg_eqv s (Y.approx n))))))

/-- Only rational linearity is asserted; no scalar representative is chosen. -/
theorem resolvent_smul (s : Q') (x : V) : R (S s x) = S s (R x) := by
  apply centered_eq_of_defect_eq hw0 hw1 hsmall hd hs _ _
    (resolvent_centered hw0 hw1 hsmall hd hs _)
  · rw [center_smul, resolvent_centered]
  · rw [resolvent_right_inverse, defect_smul, resolvent_right_inverse, center_smul]

theorem defect_time (n : Nat) (x : V) : F (T n x) = T n (F x) := by
  unfold defect
  rw [completedTime_sub, ← completedTime_add, ← completedTime_add, Nat.add_comm 2 n]

theorem resolvent_time (n : Nat) (x : V) : R (T n x) = T n (R x) := by
  apply centered_eq_of_defect_eq hw0 hw1 hsmall hd hs _ _
    (resolvent_centered hw0 hw1 hsmall hd hs _)
  · rw [← completedTime_center, resolvent_centered]
  · rw [resolvent_right_inverse, defect_time, resolvent_right_inverse, ← completedTime_center]

theorem defect_selfAdjoint (x y : V) : B (F x) y = B x (F y) := by
  unfold defect
  rw [completedInner_sub_left, completedInner_sub_right, completedInner_time_balance]

/-- Self-adjointness is about the constructed inverse in the original pairing. -/
theorem resolvent_selfAdjoint (x y : V) : B (R x) y = B x (R y) := by
  calc
    B (R x) y = B (R x) (C y) := by
      have h := center_selfAdjoint hw0 hw1 hsmall hd hs (R x) y
      rw [resolvent_centered] at h
      exact h
    _ = B (R x) (F (R y)) := by rw [resolvent_right_inverse]
    _ = B (F (R x)) (R y) :=
      (defect_selfAdjoint hw0 hw1 hsmall hd hs (R x) (R y)).symm
    _ = B (C x) (R y) := by rw [resolvent_right_inverse]
    _ = B x (R y) := by rw [center_selfAdjoint, resolvent_centered]

theorem resolvent_distance_bound (x y : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs (R x) (R y))
      (RCscale K (completedDist hw0 hw1 hsmall hd hs x y)) := by
  unfold completedDist
  rw [← resolvent_sub]
  exact resolvent_norm_bound hw0 hw1 hsmall hd hs (Sub x y)

theorem defect_zero : F Z = Z := by
  unfold defect
  rw [completedTime_zeroState, completedSub_zero]

theorem resolvent_zero : R Z = Z := by
  have h := resolvent_left_inverse hw0 hw1 hsmall hd hs Z
  rw [defect_zero, center_zero] at h
  exact h

/-- The actual inverse cannot erase a nonzero vector of the original complement. -/
theorem resolvent_ne_zero (x : UnitComplement hw0 hw1 hsmall hd hs) (hx : x.val ≠ Z) :
    R x.val ≠ Z := by
  intro h
  have he := congrArg F h
  rw [resolvent_right_inverse,
    (center_fixed_iff hw0 hw1 hsmall hd hs x.val).mpr x.property, defect_zero] at he
  exact hx he

end YMGap.Continuum.BF4SpatialUnionResolventBound

#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.norm_budget_cancel
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_norm_centered_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_norm_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.centered_eq_of_defect_eq
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.defect_sub
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_sub
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_add
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.defect_smul
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_smul
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.defect_time
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_time
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.defect_selfAdjoint
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_selfAdjoint
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_distance_bound
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.defect_zero
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_zero
#print axioms YMGap.Continuum.BF4SpatialUnionResolventBound.resolvent_ne_zero
