/-
# Quantitative finite Euler head from q-Pascal

If `q^M <= 1/2`, the next M Euler factors are each at least one half.
The exact Gaussian-binomial normalization and its elementary `2^N` cap
then give `E_q(M) >= (1/8)^M`. All products are the original finite
Euler products. This is a head estimate, not an infinite-product floor
or a pointwise heat-spread estimate by itself.
-/

import YMGap.Continuum.FiniteEulerSegment

namespace YMGap.Continuum.EulerRoundedHeadFloor

open YMGap.Constructive
open YMGap.Continuum.GaussQBinom
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.FiniteEulerSegment

set_option autoImplicit false

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.mul_num, Q'.mul_den_cast]; ac_rfl))

/-- q-Pascal preserves nonnegative coefficients at every nonnegative base. -/
theorem qbin_nonnegative {q : Q'} (hq0 : (0 : Q') ≤ q) :
    ∀ N k : Nat, (0 : Q') ≤ qbin q N k := by
  intro N
  induction N with
  | zero =>
      intro k
      cases k with
      | zero => exact Q'.zero_le_one
      | succ k => exact Q'.le_refl' 0
  | succ N ih =>
      intro k
      cases k with
      | zero => exact Q'.zero_le_one
      | succ k =>
          exact Q'.zero_le_add _ _ (ih (k + 1))
            (Q'.mul_nonneg _ _ (Q'.pow_nonneg q hq0 _) (ih k))

private theorem one_le_two_pow : ∀ N : Nat, (1 : Q') ≤ (2 : Q') ^ N
  | 0 => Q'.le_refl' 1
  | N + 1 =>
      Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 2)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 2))
          (Q'.mul_le_mul_of_nonneg_left _ _ 2 (one_le_two_pow N) (by decide)))

private theorem double_eqv (x : Q') : x + x ≈ (2 : Q') * x :=
  Q'.eqv_trans _ _ _
    (Cheb.add_eqv_congr _ _ _ _
      (Q'.eqv_symm (Q'.one_mul_eqv x)) (Q'.eqv_symm (Q'.one_mul_eqv x)))
    (Q'.eqv_symm (Q'.add_mul_eqv 1 1 x))

/-- A Gaussian-binomial coefficient is at most `2^N` for `0 <= q <= 1`. -/
theorem qbin_le_two_pow {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q')) :
    ∀ N k : Nat, qbin q N k ≤ (2 : Q') ^ N := by
  intro N
  induction N with
  | zero =>
      intro k
      cases k with
      | zero => exact Q'.le_refl' 1
      | succ k => exact Q'.zero_le_one
  | succ N ih =>
      intro k
      cases k with
      | zero => exact one_le_two_pow (N + 1)
      | succ k =>
          have hm : q ^ (N - k) * qbin q N k ≤ (2 : Q') ^ N :=
            Q'.le_trans' _ _ _
              (Q'.mul_le_mul_of_nonneg_right _ _ _ (HKPos.pow_le_one hq0 hq1 _)
                (qbin_nonnegative hq0 N k))
              (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _)) (ih k))
          exact Q'.le_trans' _ _ _
            (Q'.le_trans' _ _ _
              (Q'.add_le_add_right _ _ _ (ih (k + 1)))
              (Q'.add_le_add_left _ _ _ hm))
            (Q'.le_of_eqv (double_eqv ((2 : Q') ^ N)))

private theorem segment_half_floor {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (M : Nat) (hpower : q ^ M ≤ HalfPow.half) :
    ∀ len : Nat, HalfPow.half ^ len ≤ segment q M len := by
  intro len
  induction len with
  | zero => exact Q'.le_refl' 1
  | succ len ih =>
      have hp : q ^ (M + len + 1) ≤ HalfPow.half :=
        Q'.le_trans' _ _ _
          (HKConvGen.pow_base_antitone (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) (by omega))
          hpower
      have hf : HalfPow.half ≤ 1 + -(q ^ (M + len + 1)) :=
        Q'.le_trans' _ _ _ (by decide : HalfPow.half ≤ 1 + -HalfPow.half)
          (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hp))
      have hprod := HKConv.mul_le_mul'
        (Q'.pow_nonneg HalfPow.half HalfPow.half_nonneg len)
        (Q'.le_of_lt (HKPos.one_sub_pos
          (HKPos.pow_succ_pos_lt_one hq0 hq1 (M + len)).2)) ih hf
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hprod

private theorem scaled_eighth_pow (M : Nat) :
    (2 : Q') ^ (M + M) * (Q'.mkPos 1 8 (by decide)) ^ M ≈ HalfPow.half ^ M := by
  induction M with
  | zero => exact Q'.mul_one_eqv 1
  | succ M ih =>
      rw [show (M + 1) + (M + 1) = (M + M) + 1 + 1 by omega]
      change ((2 : Q') * (2 * (2 : Q') ^ (M + M))) *
          (Q'.mkPos 1 8 (by decide) * (Q'.mkPos 1 8 (by decide)) ^ M) ≈
        HalfPow.half * HalfPow.half ^ M
      calc ((2 : Q') * (2 * (2 : Q') ^ (M + M))) *
            (Q'.mkPos 1 8 (by decide) * (Q'.mkPos 1 8 (by decide)) ^ M)
          ≈ ((2 : Q') * 2 * Q'.mkPos 1 8 (by decide)) *
            ((2 : Q') ^ (M + M) * (Q'.mkPos 1 8 (by decide)) ^ M) := by mul_ring
        _ ≈ HalfPow.half *
            ((2 : Q') ^ (M + M) * (Q'.mkPos 1 8 (by decide)) ^ M) :=
          Q'.mul_eqv_congr_right _ _ _ (by decide)
        _ ≈ HalfPow.half * HalfPow.half ^ M := Q'.mul_eqv_congr_left _ _ _ ih

/-- The actual finite Euler head has an exponential floor as soon as its
nome power is at most one half. No exact dyadic equality is required. -/
theorem head_floor {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (M : Nat) (hpower : q ^ M ≤ HalfPow.half) :
    (Q'.mkPos 1 8 (by decide)) ^ M ≤ euler q M := by
  have he : qbin q (M + M) M * euler q M ≈ segment q M M := by
    apply Q'.mul_left_cancel_of_pos (euler_pos hq0 hq1 M)
    calc euler q M * (qbin q (M + M) M * euler q M)
        ≈ qbin q (M + M) M * euler q M * euler q M := by mul_ring
      _ ≈ euler q (M + M) := by
        have h := qbin_mul_euler q (M + M) M (by omega)
        rw [show M + M - M = M by omega] at h
        exact h
      _ ≈ euler q M * segment q M M := euler_split q M M
  have hbound : HalfPow.half ^ M ≤ (2 : Q') ^ (M + M) * euler q M :=
    Q'.le_trans' _ _ _ (segment_half_floor hq0 hq1 M hpower M)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          (qbin_le_two_pow (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) (M + M) M)
          (Q'.le_of_lt (euler_pos hq0 hq1 M))))
  exact HKConvGen.mul_le_mul_left_cancel (HKPos.pow_pos (by decide : (0 : Q') < 2) (M + M))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (scaled_eighth_pow M)) hbound)

#print axioms qbin_nonnegative
#print axioms qbin_le_two_pow
#print axioms head_floor

end YMGap.Continuum.EulerRoundedHeadFloor
