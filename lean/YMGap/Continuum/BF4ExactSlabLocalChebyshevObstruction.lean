/-
# The current degree-dependent collar factor returns to one

For nonempty seed support, the ACTUAL covarianceFactor constructed by the
local auxiliary route lies between 1-half^(n+1) and 1. A rational tolerance
supplies an explicit modulus. Its square is always at least 1/4, so this
particular upper-bound factor cannot establish long-distance decay.

This refutes neither the original covariance's decay nor Yang--Mills. It
identifies the loss in the conservative collar-floor/cone-budget estimate.
-/

import YMGap.Continuum.BF4ExactSlabLocalChebyshevCovariance
import YMGap.Continuum.BF4ExactSlabConeBudgetDegree
import YMGap.Continuum.ChebyshevNearOneUpper
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound

namespace YMGap.Continuum.BF4ExactSlabLocalChebyshevObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.BF4ExactSlabStarRateObstruction
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
open YMGap.Continuum.BF4ExactSlabLocalAuxiliaryCoercivity
open YMGap.Continuum.BF4ExactSlabLocalChebyshevCovariance
open YMGap.Continuum.BF4ExactSlabFiniteVolumeReverseEnergy
open YMGap.Continuum.BF4ExactSlabConeBudgetDegree
open YMGap.Continuum.ChebyshevNearOneUpper

local infix:50 " ≈ " => Q'.eqv
private def eighth : Q' := Q'.mkPos 1 8 (by decide)

private theorem pow_mono_base (a b : Q') (ha : (0 : Q') ≤ a) (hab : a ≤ b) (n : Nat) :
    a^n ≤ b^n := by
  induction n with
  | zero => exact Q'.le_refl' 1
  | succ n ih =>
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hab (Q'.pow_nonneg a ha n))
      (Q'.mul_le_mul_of_nonneg_left _ _ b ih (Q'.le_trans' _ _ _ ha hab))

private theorem one_le_pow (a : Q') (ha : (1 : Q') ≤ a) (n : Nat) : 1 ≤ a^n := by
  induction n with
  | zero => exact Q'.le_refl' 1
  | succ n ih =>
    exact Q'.le_trans' _ _ _ ih (Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.one_mul_eqv _))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha
        (Q'.pow_nonneg a (Q'.le_trans' _ _ _ Q'.zero_le_one ha) n)))

private theorem recip_le_one (a : Q') (ha : (0 : Q') < a) (h1 : (1 : Q') ≤ a) :
    Q'.recipPos a ha ≤ 1 := by
  apply Q'.le_of_mul_le_mul_left (c := a) ?_ ha
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_recipPos_eqv a ha))
    (Q'.le_trans' _ _ _ h1 (Q'.ge_of_eqv (Q'.mul_one_eqv a)))

private theorem ratio_le_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (b : Nat) :
    supportRatio hw0 hw1 b ≤ supportFloor w b := by
  have hr := recip_le_one (supportCap w b) (supportCap_positive hw0 hw1 b)
    (one_le_pow _ (prefixCap_ge_one hw0 hw1) (6*b))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hr
      (Q'.le_of_lt (supportFloor_positive hw0 hw1 b)))
    (Q'.le_of_eqv (Q'.one_mul_eqv _))

/-- The actual positive margin above two, keeping nome, seed size and degree. -/
def excess {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (size n : Nat) : Q' :=
  geometricCalibration * supportRatio hw0 hw1 (coneBudget size n)

theorem excess_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) : (0 : Q') ≤ excess hw0 hw1 size n :=
  Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (supportRatio_positive hw0 hw1 _))

/-- A deliberately weaker dyadic ceiling suffices to expose degeneration. -/
theorem supportRatio_le_eighth_pow {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (b d : Nat) (hd : d ≤ 6*b) :
    supportRatio hw0 hw1 b ≤ (Q'.mkPos 1 8 (by decide))^d := by
  have hh : headFloor w ≤ eighth := Q'.le_trans' _ _ _
    (headFloor_le_oneThirtySecond hw0 hw1) (by decide)
  have hf : supportFloor w b ≤ eighth^d :=
    Q'.le_trans' _ _ _
      (pow_mono_base _ _ (Q'.le_of_lt (headFloor_positive hw0 hw1)) hh (6*b))
      (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ eighth)
        (by decide : eighth ≤ 1) hd)
  exact Q'.le_trans' _ _ _ (ratio_le_floor hw0 hw1 b) hf

/-- The named cone budget supplies the exponent comparison for the actual margin. -/
theorem excess_le_eighth_pow {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) (hs : 1 ≤ size) :
    excess hw0 hw1 size n ≤ (Q'.mkPos 1 8 (by decide))^(n+1) := by
  let b := coneBudget size n
  have hd : n+1 ≤ 6*b := Nat.le_trans (degree_le_coneBudget size n hs) (by omega)
  have he : excess hw0 hw1 size n ≤ supportRatio hw0 hw1 b :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (by decide : geometricCalibration ≤ 1)
        (Q'.le_of_lt (supportRatio_positive hw0 hw1 b)))
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ he (supportRatio_le_eighth_pow hw0 hw1 b (n+1) hd)

private theorem eighth_four_pow (n : Nat) : eighth^n * (4 : Q')^n ≈ HalfPow.half^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (eighth * eighth^n) * ((4 : Q') * (4 : Q')^n) ≈ HalfPow.half * HalfPow.half^n
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => eighth | 1 => eighth^n | 2 => 4 | _ => (4 : Q')^n))
      (Cheb.mul_eqv_congr _ _ _ _
        (by decide : eighth * (4 : Q') ≈ HalfPow.half) ih)

/-- The denominator used by the EXISTING covariance factor stays near one. -/
theorem denominator_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) (hs : 1 ≤ size) :
    (1 : Q') ≤ Cheb.T (n+1) (localCoefficient hw0 hw1 size n + -(1 : Q')) ∧
    Cheb.T (n+1) (localCoefficient hw0 hw1 size n + -(1 : Q')) ≤ 1 + HalfPow.half^(n+1) := by
  let e := excess hw0 hw1 size n
  have he0 := excess_nonnegative hw0 hw1 size n
  have he := excess_le_eighth_pow hw0 hw1 size n hs
  have hehalf : e ≤ HalfPow.half := Q'.le_trans' _ _ _ he
    (Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ eighth)
        (by decide : eighth ≤ 1) (show 1 ≤ n+1 by omega))
      (by decide : eighth^(1 : Nat) ≤ HalfPow.half))
  have harg : localCoefficient hw0 hw1 size n + -(1 : Q') ≈ 1+e :=
    poly_identity_of_normal_eq
      (.add (.add (.const 2) (.var 0)) (.neg (.const 1)))
      (.add (.const 1) (.var 0)) (by decide) (fun _ => e)
  have ht := T_congr _ _ harg (n+1)
  have hlarge : (1 : Q') ≤ 1+e := Q'.add_le_self_of_nonneg 1 e he0
  refine ⟨Q'.le_trans' _ _ _ (ChebyshevAboveOne.T_lower_and_step _ hlarge (n+1)).1
    (Q'.ge_of_eqv ht), ?_⟩
  have hprod : e*(4 : Q')^(n+1) ≤ HalfPow.half^(n+1) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ he (Q'.pow_nonneg 4 (by decide) (n+1)))
      (Q'.le_of_eqv (eighth_four_pow (n+1)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv ht)
    (Q'.le_trans' _ _ _ (T_near_one_upper e he0 hehalf (n+1))
      (Q'.add_le_add_left 1 _ _ hprod))

private theorem reciprocal_band (a h : Q') (ha : (0 : Q') < a)
    (ha1 : (1 : Q') ≤ a) (hah : a ≤ 1+h) (h0 : (0 : Q') ≤ h) (h1 : h ≤ 1) :
    1 + -h ≤ Q'.recipPos a ha ∧ Q'.recipPos a ha ≤ 1 := by
  refine ⟨?_, recip_le_one a ha ha1⟩
  have hn := Q'.sub_nonneg_of_le h1
  have hp : (1 + -h)*(1+h) ≤ (1 : Q') := by
    apply Q'.le_of_sub_nonneg
    have he : (1 : Q') + -((1 + -h)*(1+h)) ≈ h*h :=
      poly_identity_of_normal_eq
        (.add (.const 1) (.neg (.mul (.add (.const 1) (.neg (.var 0)))
          (.add (.const 1) (.var 0)))))
        (.mul (.var 0) (.var 0)) (by decide) (fun _ => h)
    exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ h0 h0) (Q'.ge_of_eqv he)
  apply Q'.le_of_mul_le_mul_left (c := a) ?_ ha
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv a (1 + -h)))
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hah hn)
      (Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv (Q'.mul_recipPos_eqv a ha))))

/-- Two-sided control of the ACTUAL returned factor, not a surrogate factor. -/
theorem factor_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) (hs : 1 ≤ size) :
    1 + -(HalfPow.half^(n+1)) ≤ covarianceFactor hw0 hw1 size n ∧
      covarianceFactor hw0 hw1 size n ≤ 1 := by
  have h := denominator_bounds hw0 hw1 size n hs
  exact reciprocal_band _ _ (denominator_positive hw0 hw1 size n) h.1 h.2
    (Q'.pow_nonneg _ HalfPow.half_nonneg (n+1))
    (HKConvGen.pow_base_antitone HalfPow.half_nonneg
      (by decide : HalfPow.half ≤ 1) (Nat.zero_le (n+1)))

/-- This comparison factor never even falls below one half. -/
theorem factor_ge_half {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) (hs : 1 ≤ size) : HalfPow.half ≤ covarianceFactor hw0 hw1 size n := by
  have hh : HalfPow.half^(n+1) ≤ HalfPow.half := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone HalfPow.half_nonneg
      (by decide : HalfPow.half ≤ 1) (show 1 ≤ n+1 by omega))
    (by decide : HalfPow.half^(1 : Nat) ≤ HalfPow.half)
  exact Q'.le_trans' _ _ _ (by decide : HalfPow.half ≤ 1 + -HalfPow.half)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hh))
      (factor_bounds hw0 hw1 size n hs).1)

/-- The squared multiplier in the original covariance theorem is at least 1/4. -/
theorem factor_square_ge_quarter {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size n : Nat) (hs : 1 ≤ size) :
    Q'.mkPos 1 4 (by decide) ≤ covarianceFactor hw0 hw1 size n * covarianceFactor hw0 hw1 size n := by
  have hf := factor_ge_half hw0 hw1 size n hs
  have h0 := Q'.le_trans' _ _ _ HalfPow.half_nonneg hf
  exact Q'.le_trans' _ _ _ (by decide : Q'.mkPos 1 4 (by decide) ≤ HalfPow.half*HalfPow.half)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hf HalfPow.half_nonneg)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hf h0))

/-- Returned data: a tolerance-dependent degree cutoff for approach to ONE. -/
def factorModulus (epsilon : Q') : Nat := epsilon.den

/-- Uniform in nome and nonempty seed size, with the explicit modulus above. -/
theorem factor_approaches_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (size : Nat) (hs : 1 ≤ size) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : factorModulus epsilon ≤ n) :
    1 + -epsilon ≤ covarianceFactor hw0 hw1 size n ∧ covarianceFactor hw0 hw1 size n ≤ 1 := by
  have hh : HalfPow.half^(n+1) ≤ epsilon := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone HalfPow.half_nonneg (by decide : HalfPow.half ≤ 1)
      (show epsilon.den ≤ n+1 by exact Nat.le_trans hn (Nat.le_succ n)))
    (HalfPow.pow_half_le epsilon he)
  have h := factor_bounds hw0 hw1 size n hs
  exact ⟨Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hh)) h.1, h.2⟩

#print axioms excess
#print axioms excess_nonnegative
#print axioms supportRatio_le_eighth_pow
#print axioms excess_le_eighth_pow
#print axioms denominator_bounds
#print axioms factor_bounds
#print axioms factor_ge_half
#print axioms factor_square_ge_quarter
#print axioms factorModulus
#print axioms factor_approaches_one

end YMGap.Continuum.BF4ExactSlabLocalChebyshevObstruction
