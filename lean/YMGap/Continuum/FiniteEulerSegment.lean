/-
# Finite Euler segments and explicit geometric loss

`segment Q start len` is the finite product of 1-Q^(start+i+1).
Its exact Euler-prefix pin, positivity, upper bound one, and geometric
loss estimate are proved here. No positive infinite-product denominator
or limiting product is assumed.
-/

import YMGap.Continuum.GaussQBinomEulerQuotient
import YMGap.Continuum.ProductFloor
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.FiniteEulerSegment

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RationalTail
open YMGap.Continuum.GaussQBinomEulerNormalization

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

/-- Product on the explicit index interval start+1 through start+len. -/
def segment (Q : Q') (start len : Nat) : Q' :=
  ProductFloor.prodOneSub (fun i => Q ^ (start + i + 1)) len

@[simp] theorem segment_zero (Q : Q') (start : Nat) : segment Q start 0 = 1 := rfl

@[simp] theorem segment_succ (Q : Q') (start len : Nat) :
    segment Q start (len + 1) = segment Q start len * (1 + -(Q ^ (start + len + 1))) := rfl

/-- Exact separation of the original Euler prefix into prefix and segment. -/
theorem euler_split (Q : Q') (start len : Nat) :
    euler Q (start + len) ≈ euler Q start * segment Q start len := by
  induction len with
  | zero =>
      rw [Nat.add_zero, segment_zero]
      exact Q'.eqv_symm (Q'.mul_one_eqv _)
  | succ len ih =>
      rw [Nat.add_succ, euler_succ, segment_succ]
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ih) (Q'.mul_assoc_eqv _ _ _)

theorem segment_pos {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (start len : Nat) : (0 : Q') < segment Q start len := by
  induction len with
  | zero => exact (by decide : (0 : Q') < 1)
  | succ len ih =>
      exact HKPos.q_mul_pos ih
        (HKPos.one_sub_pos (HKPos.pow_succ_pos_lt_one hQ0 hQ1 (start + len)).2)

theorem segment_le_one {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (start len : Nat) : segment Q start len ≤ (1 : Q') := by
  induction len with
  | zero => exact Q'.le_refl' _
  | succ len ih =>
      have hneg : -(Q ^ (start + len + 1)) ≤ (0 : Q') :=
        Q'.neg_le_neg (Q'.pow_nonneg Q (Q'.le_of_lt hQ0) _)
      have hfac : 1 + -(Q ^ (start + len + 1)) ≤ (1 : Q') := by
        have h := Q'.add_le_add_left 1 _ _ hneg
        rw [Q'.add_zero'] at h
        exact h
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hfac (Q'.le_of_lt (segment_pos hQ0 hQ1 start len)))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) ih)

private theorem lossSum_eq_finSum (f : Nat → Q') (len : Nat) :
    ProductFloor.lossSum f len = finSum f len := by
  induction len with
  | zero => rfl
  | succ len ih =>
      change ProductFloor.lossSum f len + f len = finSum f len + f len
      rw [ih]

/-- The sum of the segment's actual losses is bounded at its start index,
independently of its finite length. -/
theorem segment_loss_le {Q : Q'} (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q'))
    (start len : Nat) :
    ProductFloor.lossSum (fun i => Q ^ (start + i + 1)) len
      ≤ HKConvGen.geoTailBase 1 Q (start + 1) := by
  rw [lossSum_eq_finSum]
  have he : finSum (fun i => Q ^ (start + i + 1)) len
      ≈ finSum (fun i => HKConvGen.geoIncrBase 1 Q ((start + 1) + i)) len := by
    apply RationalTail.finSum_eqv_congr
    intro i
    unfold HKConvGen.geoIncrBase
    rw [show start + i + 1 = (start + 1) + i by omega]
    exact Q'.eqv_symm (Q'.one_mul_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (HKConvGen.geoTailBase_series_le Q'.zero_le_one hQ0 hQ1 (start + 1) len)

/-- Weierstrass gives a finite-segment floor with an explicit base-dependent
geometric loss; no requirement that the loss already be small. -/
theorem segment_ge_one_sub_tail {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (start len : Nat) :
    1 - HKConvGen.geoTailBase 1 Q (start + 1) ≤ segment Q start len :=
  ProductFloor.prod_floor_of_sum_le (fun i => Q ^ (start + i + 1))
    (fun _ => Q'.pow_nonneg Q (Q'.le_of_lt hQ0) _)
    (fun _ => HKPos.pow_le_one (Q'.le_of_lt hQ0) (Q'.le_of_lt hQ1) _)
    _ (segment_loss_le hQ0 hQ1 start) len

/-- Addition-only form of the exact segment's geometric loss bound. -/
theorem one_le_segment_add_tail {Q : Q'}
    (hQ0 : (0 : Q') < Q) (hQ1 : Q < (1 : Q')) (start len : Nat) :
    (1 : Q') ≤ segment Q start len + HKConvGen.geoTailBase 1 Q (start + 1) := by
  have h := Q'.add_le_add_right _ _ (HKConvGen.geoTailBase 1 Q (start + 1))
    (segment_ge_one_sub_tail hQ0 hQ1 start len)
  have he : ((1 - HKConvGen.geoTailBase 1 Q (start + 1))
      + HKConvGen.geoTailBase 1 Q (start + 1)) ≈ (1 : Q') := by
    calc ((1 + -HKConvGen.geoTailBase 1 Q (start + 1)) + HKConvGen.geoTailBase 1 Q (start + 1))
        ≈ 1 + (-HKConvGen.geoTailBase 1 Q (start + 1) + HKConvGen.geoTailBase 1 Q (start + 1)) :=
          Q'.add_assoc_eqv _ _ _
      _ ≈ (1 : Q') + 0 := Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv _)
      _ ≈ (1 : Q') := by rw [Q'.add_zero']; exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h

end YMGap.Continuum.FiniteEulerSegment

#print axioms YMGap.Continuum.FiniteEulerSegment.segment
#print axioms YMGap.Continuum.FiniteEulerSegment.euler_split
#print axioms YMGap.Continuum.FiniteEulerSegment.segment_pos
#print axioms YMGap.Continuum.FiniteEulerSegment.segment_le_one
#print axioms YMGap.Continuum.FiniteEulerSegment.segment_loss_le
#print axioms YMGap.Continuum.FiniteEulerSegment.segment_ge_one_sub_tail
#print axioms YMGap.Continuum.FiniteEulerSegment.one_le_segment_add_tail
