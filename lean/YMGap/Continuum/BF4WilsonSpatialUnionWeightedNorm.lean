/-
# Rate-dependent geometric-series budget on the current Wilson carrier

The exact weighted-square identity proves the rational Young inequality on the
same completed Wilson form.  Its consumer is a finite geometric partial sum
for the actual current transfer.  All rate dependence remains explicit; this
is fixed-spacing SU(2) data, not a continuum or Clay theorem.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.HeatKernelPos

namespace YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_add_zero)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- The exact rational squared-norm budget, with its positive denominator. -/
def budget (r : Q') (hr1 : r < (1 : Q')) : Q' :=
  Q'.divPos 1 ((1-r)*(1-r))
    (Q'.mul_pos (HKPos.one_sub_pos hr1) (HKPos.one_sub_pos hr1))

theorem budget_positive (r : Q') (hr1 : r < (1 : Q')) :
    (0 : Q') < budget r hr1 :=
  Q'.mul_pos (by decide : (0 : Q') < 1) (Q'.recipPos_pos _ _)

theorem budget_nonnegative (r : Q') (hr1 : r < (1 : Q')) :
    (0 : Q') ≤ budget r hr1 := Q'.le_of_lt (budget_positive r hr1)

theorem budget_mul_square (r : Q') (hr1 : r < (1 : Q')) :
    (budget r hr1 * ((1-r)*(1-r))).eqv 1 :=
  Q'.divPos_mul_eqv 1 _ _

private abbrev PE := RingNormaliser.PolyExpr

private def subExpr (a b : PE) : PE := .add a (.neg b)

private theorem weighted_identity (r a b c : Q') :
    ((r*(1-r))*((a+b)+(b+c)) +
      (r*(r*a - (1-r)*b) - (1-r)*(r*b - (1-r)*c))).eqv
      (r*a+(1-r)*c) := by
  let R : PE := .var 0
  let U : PE := subExpr (.const 1) R
  let A : PE := .var 1
  let M : PE := .var 2
  let C : PE := .var 3
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul (.mul R U) (.add (.add A M) (.add M C)))
      (subExpr
        (.mul R (subExpr (.mul R A) (.mul U M)))
        (.mul U (subExpr (.mul R M) (.mul U C)))))
    (.add (.mul R A) (.mul U C)) (by decide)
    (fun | 0 => r | 1 => a | 2 => b | _ => c)

private theorem series_identity (r k : Q') :
    (r*(k*((1-r)*(1-r)))+(1-r)*(r*r*k)).eqv ((r*(1-r))*k) := by
  let R : PE := .var 0
  let U : PE := subExpr (.const 1) R
  let K : PE := .var 1
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.mul R (.mul K (.mul U U)))
      (.mul U (.mul (.mul R R) K)))
    (.mul (.mul R U) K) (by decide)
    (fun | 0 => r | _ => k)

theorem budget_balance (r : Q') (hr1 : r < (1 : Q')) :
    (r+(1-r)*(r*r*budget r hr1)).eqv ((r*(1-r))*budget r hr1) := by
  have h : (r*(budget r hr1*((1-r)*(1-r)))).eqv r :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left r _ _ (budget_mul_square r hr1))
      (Q'.mul_one_eqv r)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm h))
    (series_identity r (budget r hr1))

private theorem scale_congr {a b : Q'} (h : a.eqv b) (v : RC) :
    RCscale a v = RCscale b v := by
  refine Quotient.inductionOn v ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_eqv_congr_right a b (X.approx n) h))

private theorem add_scales (a b : Q') (v : RC) :
    RCadd (RCscale a v) (RCscale b v) = RCscale (a+b) v := by
  refine Quotient.inductionOn v ?_
  exact fun X => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_symm (Q'.add_mul_eqv a b (X.approx n))))

private theorem scale_cancel {a : Q'} (ha : (0 : Q') < a) {x y : RC}
    (h : RCle (RCscale a x) (RCscale a y)) : RCle x y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h epsilon he
  obtain ⟨N, hN⟩ := h (a*epsilon) (Q'.mul_pos ha he)
  refine ⟨N, fun n hn => ?_⟩
  apply Q'.le_of_mul_le_mul_left (c := a)
  · exact Q'.le_trans' _ _ _ (hN n hn)
      (Q'.ge_of_eqv (Q'.mul_add_eqv a (Y.approx n) epsilon))
  · exact ha

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "S" => completedSmul hw0 hw1 hsmall hd hs
local notation "Sub" => completedSub hw0 hw1 hsmall hd hs

theorem norm_weighted_identity (r : Q') (x y : V) :
    RCadd (RCscale (r*(1-r)) (B (A x y) (A x y)))
        (B (Sub (S r x) (S (1-r) y)) (Sub (S r x) (S (1-r) y))) =
      RCadd (RCscale r (B x x)) (RCscale (1-r) (B y y)) := by
  simp only [completedInner_add_left, completedInner_add_right,
    completedInner_sub_left, completedInner_sub_right,
    completedInner_smul_left, completedInner_smul_right]
  rw [completedInner_symm hw0 hw1 hsmall hd hs y x]
  refine Quotient.inductionOn₃ (B x x) (B x y) (B y y) ?_
  intro X M Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => weighted_identity r (X.approx n) (M.approx n) (Y.approx n)))

theorem norm_weighted_add (r : Q') (_hr0 : (0 : Q') < r) (_hr1 : r < (1 : Q'))
    (x y : V) :
    RCle (RCscale (r*(1-r)) (B (A x y) (A x y)))
      (RCadd (RCscale r (B x x)) (RCscale (1-r) (B y y))) := by
  have h := RCadd_le_add
    (RCle_refl (RCscale (r*(1-r)) (B (A x y) (A x y))))
    (completedInner_nonnegative hw0 hw1 hsmall hd hs
      (Sub (S r x) (S (1-r) y)))
  rw [rc_add_zero, norm_weighted_identity hw0 hw1 hsmall hd hs r x y] at h
  exact h

theorem series_step_bound (r : Q') (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (x y : V)
    (hy : RCle (B y y) (RCscale (r*r*budget r hr1) (B x x))) :
    RCle (B (A x y) (A x y)) (RCscale (budget r hr1) (B x x)) := by
  apply scale_cancel (a := r*(1-r))
    (Q'.mul_pos hr0 (HKPos.one_sub_pos hr1))
  have h := RCle_trans (norm_weighted_add hw0 hw1 hsmall hd hs r hr0 hr1 x y)
    (RCadd_le_add (RCle_refl _) (RCscale_mono
      (Q'.le_of_lt (HKPos.one_sub_pos hr1)) hy))
  have heq : RCadd (RCscale r (B x x))
        (RCscale (1-r) (RCscale (r*r*budget r hr1) (B x x))) =
      RCscale (r*(1-r)) (RCscale (budget r hr1) (B x x)) := by
    rw [RCscale_RCscale, add_scales, RCscale_RCscale]
    exact scale_congr (budget_balance r hr1) (B x x)
  rw [← heq]
  exact h

end YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.budget
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.budget_positive
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.budget_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.budget_mul_square
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.budget_balance
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.norm_weighted_identity
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.norm_weighted_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionWeightedNorm.series_step_bound
