/-
# Exponential Euler floor with an explicit rounded nome budget

Group the tail into blocks of M factors. It dominates E(q^M,B)^M;
if q^M<=1/8, the latter Euler product is at least (1/2)^M.
The q-binomial head bound costs (1/8)^M. Thus EVERY finite original
Euler product is at least (1/16)^M, uniformly in its length.

Taking M=HeatRoundedCutoff.cutoff q gives a quantitative exponential
floor at the actual nome, without a Gaussian image or infinite-product
identity assumption. It does not prove a heat-window spread or mass gap.
-/

import YMGap.Continuum.EulerRoundedHeadFloor
import YMGap.Continuum.EulerProductStrictFloor
import YMGap.Continuum.HeatRoundedCutoff
import YMGap.Continuum.TotalMajorantClose

namespace YMGap.Continuum.EulerRoundedBlockFloor

open YMGap.Constructive
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.FiniteEulerSegment

set_option autoImplicit false
local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem one_pow (n : Nat) : (1 : Q') ^ n ≈ 1 := by
  induction n with
  | zero => exact Q'.eqv_refl _
  | succ n ih =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ ih) (Q'.one_mul_eqv _)

/-- Once the blocked nome is small, every finite Euler prefix is >=1/2. -/
theorem small_nome_floor {r : Q'} (hr0 : (0 : Q') < r)
    (hr : r ≤ Q'.mkPos 1 8 (by decide)) (B : Nat) :
    HalfPow.half ≤ euler r B := by
  have hr1 : r < (1 : Q') := Q'.lt_of_le_of_lt hr (by decide)
  have hmargin : HalfPow.half ≤ 1 + -r := Q'.le_trans' _ _ _
    (by decide : HalfPow.half ≤ (1 : Q') + -(Q'.mkPos 1 8 (by decide)))
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hr))
  have hrec : HKConv.divPos 1 (1 + -r) ≤ (2 : Q') :=
    HKConv.divPos_le_of_le (CReal.num_pos_of_pos (HKPos.one_sub_pos hr1))
      (Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (2 : Q') * HalfPow.half)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hmargin (by decide)))
  have hgeo : HKConvGen.geoTailBase 1 r 1 ≤ HalfPow.half := by
    have he : HKConvGen.geoTailBase 1 r 1 ≈ r * HKConv.divPos 1 (1 + -r) :=
      Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
        (Q'.one_mul_eqv _) (Q'.mul_one_eqv _))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (HKConv.mul_le_mul' (Q'.le_of_lt hr0)
        (by decide : (0 : Q') ≤ 2) hr hrec) (by decide))
  have hfloor : HalfPow.half ≤ segment r 0 B := Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (by decide : HalfPow.half ≤ (1 : Q') + -HalfPow.half)
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hgeo)))
    (segment_ge_one_sub_tail hr0 hr1 0 B)
  have he : euler r B ≈ segment r 0 B := by
    have h := euler_split r 0 B
    simpa only [Nat.zero_add, euler_zero] using
      (Q'.eqv_trans _ _ _ h (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hfloor (Q'.ge_of_eqv he)

/-- Every factor after start is at least 1-q^start. -/
theorem segment_constant_floor {q : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (start len : Nat) :
    (1 + -(q ^ start)) ^ len ≤ segment q start len := by
  have hc0 : (0 : Q') ≤ 1 + -(q ^ start) :=
    Q'.sub_nonneg_of_le (HKPos.pow_le_one (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) start)
  induction len with
  | zero => exact Q'.le_refl' _
  | succ len ih =>
      have hp := HKConvGen.pow_base_antitone (Q'.le_of_lt hq0) (Q'.le_of_lt hq1)
        (show start ≤ start + len + 1 by omega)
      have hf := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hp)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (HKConv.mul_le_mul' (Q'.pow_nonneg _ hc0 len)
          (Q'.le_of_lt (HKPos.one_sub_pos (HKPos.pow_succ_pos_lt_one hq0 hq1 (start + len)).2))
          ih hf)

/-- Blocking only compares actual finite products; no independence or
infinite-product denominator enters this inequality. -/
theorem block_comparison {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (M B : Nat) :
    euler q M * (euler (q ^ M) B) ^ M ≤ euler q (M * (B + 1)) := by
  induction B with
  | zero =>
      rw [Nat.zero_add, Nat.mul_one, euler_zero]
      exact Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (one_pow M)) (Q'.mul_one_eqv _))
  | succ B ih =>
      let c := (1 : Q') + -((q ^ M) ^ (B + 1))
      have hc : c ≈ (1 : Q') + -(q ^ (M * (B + 1))) :=
        Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _ (TotalMajorantClose.pow_mul q M (B + 1)))
      have hc0 : (0 : Q') ≤ c := Q'.sub_nonneg_of_le
        (HKPos.pow_le_one (Q'.pow_nonneg q (Q'.le_of_lt hq0) M)
          (HKPos.pow_le_one (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) M) (B + 1))
      have hblock : c ^ M ≤ segment q (M * (B + 1)) M :=
        Q'.le_trans' _ _ _ (HKConv.pow_le_pow_base hc0 (Q'.le_of_eqv hc) M)
          (segment_constant_floor hq0 hq1 _ _)
      have he : euler q M * (euler (q ^ M) (B + 1)) ^ M ≈
          (euler q M * (euler (q ^ M) B) ^ M) * c ^ M := by
        rw [euler_succ]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (TotalMajorantClose.mul_pow _ _ M))
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      have hnon : (0 : Q') ≤ euler q M * (euler (q ^ M) B) ^ M := by
        by_cases hm : M = 0
        · subst M
          exact Q'.le_of_lt (HKPos.q_mul_pos (euler_pos hq0 hq1 0)
            (by change (0 : Q') < 1; decide))
        · have hr1 := (HKPos.pow_succ_pos_lt_one hq0 hq1 (M - 1)).2
          rw [Nat.sub_add_cancel (by omega : 1 ≤ M)] at hr1
          exact Q'.mul_nonneg _ _ (Q'.le_of_lt (euler_pos hq0 hq1 M))
            (Q'.pow_nonneg _ (Q'.le_of_lt (euler_pos (HKPos.pow_pos hq0 M) hr1 B)) M)
      have hprod := HKConv.mul_le_mul' hnon
        (Q'.le_of_lt (segment_pos hq0 hq1 (M * (B + 1)) M)) ih hblock
      have hsplit := euler_split q (M * (B + 1)) M
      rw [← Nat.mul_succ] at hsplit
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.le_trans' _ _ _ hprod (Q'.ge_of_eqv hsplit))

/-- Exponential lower bound for every finite original Euler product. -/
theorem euler_floor {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (M : Nat) (hM : 0 < M) (hp : q ^ M ≤ Q'.mkPos 1 8 (by decide)) (K : Nat) :
    (Q'.mkPos 1 16 (by decide)) ^ M ≤ euler q K := by
  have hhead := EulerRoundedHeadFloor.head_floor hq0 hq1 M
    (Q'.le_trans' _ _ _ hp (by decide : Q'.mkPos 1 8 (by decide) ≤ HalfPow.half))
  have htail := HKConv.pow_le_pow_base HalfPow.half_nonneg
    (small_nome_floor (HKPos.pow_pos hq0 M) hp K) M
  have hprod := HKConv.mul_le_mul'
    (Q'.pow_nonneg (Q'.mkPos 1 8 (by decide)) (by decide) M)
    (Q'.le_trans' _ _ _ (Q'.pow_nonneg _ HalfPow.half_nonneg M) htail) hhead htail
  have he : (Q'.mkPos 1 16 (by decide)) ^ M ≈
      (Q'.mkPos 1 8 (by decide)) ^ M * HalfPow.half ^ M := by
    have hbase : Q'.mkPos 1 16 (by decide) = Q'.mkPos 1 8 (by decide) * HalfPow.half := by decide
    rw [hbase]
    exact TotalMajorantClose.mul_pow _ _ M
  have hKM : K ≤ M * (K + 1) := by
    have h := Nat.mul_le_mul_right (K + 1) (show 1 ≤ M by omega)
    simp only [Nat.one_mul] at h
    omega
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ hprod (Q'.le_trans' _ _ _ (block_comparison hq0 hq1 M K)
      (EulerProductStrictFloor.euler_antitone hq0 hq1 hKM)))

/-- Actual rounded schedule, with no extra cutoff or analytic premise. -/
theorem rounded_euler_floor {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (K : Nat) :
    (Q'.mkPos 1 16 (by decide)) ^ HeatRoundedCutoff.cutoff q ≤ euler q K :=
  euler_floor hq0 hq1 _ (HeatRoundedCutoff.cutoff_positive q)
    (HeatRoundedCutoff.power_le hq0 hq1) K

#print axioms small_nome_floor
#print axioms segment_constant_floor
#print axioms block_comparison
#print axioms euler_floor
#print axioms rounded_euler_floor

end YMGap.Continuum.EulerRoundedBlockFloor
