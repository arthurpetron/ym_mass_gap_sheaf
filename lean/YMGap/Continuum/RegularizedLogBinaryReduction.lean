/-
Computed binary reduction for a positive rational at most one.

The scale is actual dyadic data, not a freely supplied logarithm.  The closed
endpoint uses mantissa one and exponent zero; below one the existing binary
search produces a mantissa in [1/2,1).  The approximation pin concerns the
existing dyadicLogValue only.  Identification with the regularized logarithm
outside its direct window is a separate consumer, not assumed here.
-/

import YMGap.Continuum.HamiltonianAllSep
import YMGap.Continuum.RebasedExpShiftSupportReduction
import YMGap.Constructive.DyadicTimeRationals
import YMGap.Constructive.CauchyConv
import YMGap.Constructive.QPoly

set_option autoImplicit false

namespace YMGap.Continuum.RegularizedLogBinaryReduction

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.RebasedExpShiftSupportReduction

local infix:50 " ≈ " => Q'.eqv

private theorem num_lt_den (x : Q') (h : x < (1 : Q')) :
    x.num < (x.den : Int) := by
  change x.num * 1 < 1 * (x.den : Int) at h
  simpa only [Int.mul_one, Int.one_mul] using h

private theorem endpoint_eqv (x : Q') (hx1 : x ≤ (1 : Q'))
    (h : ¬ x < (1 : Q')) : x ≈ (1 : Q') := by
  have hle : x.num ≤ (x.den : Int) := by
    change x.num * 1 ≤ 1 * (x.den : Int) at hx1
    simpa only [Int.mul_one, Int.one_mul] using hx1
  have hn : ¬ x.num < (x.den : Int) := by
    intro hn
    apply h
    change x.num * 1 < 1 * (x.den : Int)
    simpa only [Int.mul_one, Int.one_mul] using hn
  change x.num * 1 = 1 * (x.den : Int)
  simp only [Int.mul_one, Int.one_mul]
  omega

private theorem scale_zero (k : Nat) : dyadicScale 0 k ≈ scaleQ k := by
  change ((1 : Q') * scaleQ k) ≈ scaleQ k
  exact Q'.one_mul_eqv _

/-- Actual binary search, with a literal closed-endpoint branch. -/
def binaryReduction (x : Q') (hx0 : (0 : Q') < x) (hx1 : x ≤ (1 : Q')) :
    DyadicLogReduction x :=
  if h : x < (1 : Q') then
    let be := binExpOf x (Q'.num_pos_of_pos hx0) (num_lt_den x h)
    { up := 0
      down := be.k
      m := mant x be.k
      hm1 := mant_pos x be.k (Q'.num_pos_of_pos hx0)
      hyb := mant_window x be (Q'.num_pos_of_pos hx0)
      scaling := Q'.eqv_trans _ _ _
        (Q'.eqv_symm (scaleQ_mul_mant_eqv x be.k))
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (scale_zero be.k))) }
  else
    { up := 0
      down := 0
      m := 1
      hm1 := by decide
      hyb := CRealLog.yOf_one_window
      scaling := Q'.eqv_trans _ _ _ (endpoint_eqv x hx1 h)
        (Q'.eqv_symm (by decide : (dyadicScale 0 0 * (1 : Q')) ≈ 1)) }

theorem binaryReduction_up (x : Q') (hx0 : (0 : Q') < x)
    (hx1 : x ≤ (1 : Q')) : (binaryReduction x hx0 hx1).up = 0 := by
  unfold binaryReduction
  split <;> rfl

theorem binaryReduction_m_bounds (x : Q') (hx0 : (0 : Q') < x)
    (hx1 : x ≤ (1 : Q')) :
    (0 : Q') ≤ (binaryReduction x hx0 hx1).m ∧
      (binaryReduction x hx0 hx1).m ≤ 1 ∧
      HalfPow.half ≤ (binaryReduction x hx0 hx1).m := by
  by_cases h : x < (1 : Q')
  · rw [binaryReduction, dif_pos h]
    let be := binExpOf x (Q'.num_pos_of_pos hx0) (num_lt_den x h)
    change (0 : Q') ≤ mant x be.k ∧ mant x be.k ≤ 1 ∧
      HalfPow.half ≤ mant x be.k
    have hh : HalfPow.half ≤ mant x be.k := by
      change 1 * ((mant x be.k).den : Int) ≤ (mant x be.k).num * 2
      simpa only [Int.one_mul] using mant_hhalf x be.k be.hge
    have hm : mant x be.k ≤ (1 : Q') := by
      have ht := mant_lt_one x be.k be.hlt
      change (mant x be.k).num * 1 ≤ 1 * ((mant x be.k).den : Int)
      change (mant x be.k).num * 1 < 1 * ((mant x be.k).den : Int) at ht
      exact Int.le_of_lt ht
    exact ⟨Q'.le_trans' _ _ _ (by decide : (0 : Q') ≤ HalfPow.half) hh, hm, hh⟩
  · rw [binaryReduction, dif_neg h]
    change (0 : Q') ≤ (1 : Q') ∧ (1 : Q') ≤ 1 ∧ HalfPow.half ≤ (1 : Q')
    exact ⟨by decide, by decide, by decide⟩

/-- The recursive rational half power equals the existing explicit dyadic scale. -/
theorem halfPow_scaleQ_eqv (k : Nat) : HalfPow.half ^ k ≈ scaleQ k := by
  change (HalfPow.half ^ k).num * ((scaleQ k).den : Int) =
    (scaleQ k).num * ((HalfPow.half ^ k).den : Int)
  rw [DyadicTimeRationals.half_power_num, DyadicTimeRationals.half_power_den]
  unfold scaleQ
  rw [Q'.mkPos_num, Q'.mkPos_den]

theorem binaryReduction_halfPow_scaling (x : Q') (hx0 : (0 : Q') < x)
    (hx1 : x ≤ (1 : Q')) :
    x ≈ HalfPow.half ^ (binaryReduction x hx0 hx1).down *
      (binaryReduction x hx0 hx1).m := by
  let red := binaryReduction x hx0 hx1
  have hs : dyadicScale red.up red.down ≈ HalfPow.half ^ red.down := by
    change dyadicScale (binaryReduction x hx0 hx1).up red.down ≈ _
    rw [binaryReduction_up]
    exact Q'.eqv_trans _ _ _ (scale_zero red.down)
      (Q'.eqv_symm (halfPow_scaleQ_eqv red.down))
  exact Q'.eqv_trans _ _ _ red.scaling
    (Q'.mul_eqv_congr_right _ _ _ hs)

/-- Primitive recursive copies of log two have the literal multiplication pin. -/
theorem natLogTwo_approx (k n : Nat) :
    (natLogTwo k).approx n ≈ Q'.ofNat k * CRealLog.log2.approx n := by
  induction k with
  | zero =>
      change (0 : Q') ≈ (0 : Q') * CRealLog.log2.approx n
      exact Q'.eqv_symm (q_zero_mul _)
  | succ k ih =>
      change (natLogTwo k).approx n + CRealLog.log2.approx n ≈ _
      have hn : Q'.ofNat (k + 1) ≈ Q'.ofNat k + (1 : Q') :=
        Q'.ofNat_add_eqv k 1
      have hd : (Q'.ofNat k + (1 : Q')) * CRealLog.log2.approx n ≈
          Q'.ofNat k * CRealLog.log2.approx n + CRealLog.log2.approx n :=
        Q'.eqv_trans _ _ _ (q_add_mul _ _ _)
          (q_add_congr (Q'.eqv_refl _) (Q'.one_mul_eqv _))
      exact Q'.eqv_trans _ _ _ (q_add_congr ih (Q'.eqv_refl _))
        (Q'.eqv_symm (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hn) hd))

/-- Exact approximation of the faithful logarithm computed by the reduction. -/
theorem binaryReduction_log_approx (x : Q') (hx0 : (0 : Q') < x)
    (hx1 : x ≤ (1 : Q')) (n : Nat) :
    (dyadicLogValue (binaryReduction x hx0 hx1)).approx n ≈
      -(Q'.ofNat (binaryReduction x hx0 hx1).down * CRealLog.log2.approx n) +
        (CRealLog.logRat (binaryReduction x hx0 hx1).m
          (binaryReduction x hx0 hx1).hm1 (binaryReduction x hx0 hx1).hyb).approx n := by
  let red := binaryReduction x hx0 hx1
  change ((natLogTwo red.up).approx n + -(natLogTwo red.down).approx n) +
      (CRealLog.logRat red.m red.hm1 red.hyb).approx n ≈ _
  have hu : red.up = 0 := binaryReduction_up x hx0 hx1
  rw [hu]
  change ((0 : Q') + -(natLogTwo red.down).approx n) +
      (CRealLog.logRat red.m red.hm1 red.hyb).approx n ≈ _
  exact q_add_congr
    (Q'.eqv_trans _ _ _ (q_zero_add_eqv _)
      (Q'.neg_eqv_congr _ _ (natLogTwo_approx red.down n)))
    (Q'.eqv_refl _)

end YMGap.Continuum.RegularizedLogBinaryReduction

#print axioms YMGap.Continuum.RegularizedLogBinaryReduction.binaryReduction
#print axioms YMGap.Continuum.RegularizedLogBinaryReduction.binaryReduction_up
#print axioms YMGap.Continuum.RegularizedLogBinaryReduction.binaryReduction_m_bounds
#print axioms YMGap.Continuum.RegularizedLogBinaryReduction.halfPow_scaleQ_eqv
#print axioms YMGap.Continuum.RegularizedLogBinaryReduction.binaryReduction_halfPow_scaling
#print axioms YMGap.Continuum.RegularizedLogBinaryReduction.natLogTwo_approx
#print axioms YMGap.Continuum.RegularizedLogBinaryReduction.binaryReduction_log_approx
