/-
# Explicit norm budget for the current Wilson resolvent

The represented inverse is bounded on the same current Wilson carrier by the
displayed rational budget `(1-q(w))⁻²`.  This is a fixed-spacing SU(2)
estimate; it is not a physical or continuum mass-gap statement.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionResolvent
import YMGap.Continuum.MeanExpConvexProgress

namespace YMGap.Continuum.BF4WilsonSpatialUnionResolventBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionVacuumProjection
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
open YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm
open YMGap.Continuum.BF4WilsonSpatialUnionResolventPartial
open YMGap.Continuum.BF4WilsonSpatialUnionResolvent
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
      RCadd (RCscale (r*(1-r)*(1-r)) a)
        (RCscale ((1-r)*(r*r)) a) := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 0)))) (.var 1))
      (.add
        (.mul (.mul (.mul (.var 0) (.add (.const 1) (.neg (.var 0))))
          (.add (.const 1) (.neg (.var 0)))) (.var 1))
        (.mul (.mul (.add (.const 1) (.neg (.var 0)))
          (.mul (.var 0) (.var 0))) (.var 1)))
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

theorem norm_budget_cancel (r : Q') (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (a c : RC)
    (h : RCle (RCscale (r*(1-r)) a)
      (RCadd (RCscale r c) (RCscale ((1-r)*(r*r)) a))) :
    RCle a (RCscale (budget r hr1) c) := by
  rw [norm_split] at h
  have hc := rc_add_cancel _ _ _ h
  apply scale_cancel (a := r*(1-r)*(1-r))
    (Q'.mul_pos (Q'.mul_pos hr0 (HKPos.one_sub_pos hr1))
      (HKPos.one_sub_pos hr1))
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
local notation "R" => resolvent hw0 hw1 hsmall hd hs
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

theorem resolvent_norm_bound (x : V) :
    RCle (B (R x) (R x)) (RCscale K (B x x)) :=
  RCle_trans (resolvent_norm_centered_bound hw0 hw1 hsmall hd hs x)
    (RCscale_mono (budget_nonnegative q (twoStepRate_lt_one hw0 hd hs))
      (center_norm_le hw0 hw1 hsmall hd hs x))

theorem resolvent_distance_bound (x y : V) :
    RCle (completedDist hw0 hw1 hsmall hd hs (R x) (R y))
      (RCscale K (completedDist hw0 hw1 hsmall hd hs x y)) := by
  unfold completedDist
  rw [← resolvent_sub]
  exact resolvent_norm_bound hw0 hw1 hsmall hd hs (completedSub hw0 hw1 hsmall hd hs x y)

end YMGap.Continuum.BF4WilsonSpatialUnionResolventBound

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventBound.norm_budget_cancel
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventBound.resolvent_norm_bound
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionResolventBound.resolvent_distance_bound
