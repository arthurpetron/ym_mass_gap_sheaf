/-
# Physical spin-one central shells equal the symbolic Hahn matrix

For `2 <= t <= n`, the physical source columns in the `(2,n)` tensor
product are exactly `i = 0,1,2`.  This module identifies all nine entries
of the derived transvectant matrix with `centralHahn (ofNat n) (ofNat t)`.
The only arithmetic bridge needed is exact coercion of a non-truncated
natural subtraction into constructive-rational subtraction.
-/

import YMGap.Continuum.SU2SpinOneCentralHahnDeterminant

namespace YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2SpinOneCentralHahnDeterminant

/-- Natural subtraction agrees with subtraction after embedding in `Q'`
when the natural subtraction is not truncated. -/
theorem ofNat_sub_eqv (a b : Nat) (h : b <= a) :
    (Q'.ofNat (a - b)).eqv (Q'.ofNat a + -(Q'.ofNat b)) := by
  change (Int.ofNat (a - b)) * 1 =
    (Int.ofNat a * 1 + (-Int.ofNat b) * 1) * 1
  simp
  omega

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl
private theorem one_num : (1 : Q').num = 1 := rfl
private theorem one_den : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num : (2 : Q').num = 2 := rfl
private theorem two_den : ((2 : Q').den : Int) = 1 := rfl

/-- First-row, first-column specialization. -/
theorem hahnEntry_one_zero (n t : Nat) :
    (hahnEntry 2 n t 1 0).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) 1 0) := by
  refine Q'.eqv_trans _ _ _ (hahnEntry_one 2 n t 0) ?_
  change (Q'.ofNat (0 * (n - (t - 0))) +
      -(Q'.ofNat ((2 - 0) * (t - 0)))).eqv
    (-((2 : Q') * Q'.ofNat t))
  unfold Q'.eqv
  change
    (Int.ofNat (0 * (n - (t - 0))) * 1 +
      (-Int.ofNat ((2 - 0) * (t - 0))) * 1) * 1 =
    (-(Int.ofNat 2 * Int.ofNat t)) * 1
  simp

/-- First-row, middle-column specialization on the central range. -/
theorem hahnEntry_one_one (n t : Nat) (ht : 2 <= t) (htn : t <= n) :
    (hahnEntry 2 n t 1 1).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) 1 1) := by
  refine Q'.eqv_trans _ _ _ (hahnEntry_one 2 n t 1) ?_
  change (Q'.ofNat (1 * (n - (t - 1))) +
      -(Q'.ofNat ((2 - 1) * (t - 1)))).eqv
    (Q'.ofNat n + -((2 : Q') * Q'.ofNat t) + 2)
  unfold Q'.eqv
  rw [show ((Q'.ofNat n + -((2 : Q') * Q'.ofNat t) + 2).den : Int) = 1 from rfl]
  rw [show ((Q'.ofNat (1 * (n - (t - 1))) +
      -(Q'.ofNat ((2 - 1) * (t - 1)))).den : Int) = 1 from rfl]
  rw [Int.mul_one, Int.mul_one]
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.neg_den,
    neg_num, two_num, two_den, Int.mul_one]
  omega

/-- The constant row agrees with the symbolic matrix in every column. -/
theorem hahnEntry_zero_central (n t i : Nat) :
    (hahnEntry 2 n t 0 i).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) 0 i) := by
  simpa only [centralHahn] using hahnEntry_zero 2 n t i

/-- First-row, last-column specialization on the central range. -/
theorem hahnEntry_one_two (n t : Nat) (ht : 2 <= t) (htn : t <= n) :
    (hahnEntry 2 n t 1 2).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) 1 2) := by
  refine Q'.eqv_trans _ _ _ (hahnEntry_one 2 n t 2) ?_
  unfold centralHahn Q'.eqv
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.neg_den,
    neg_num, two_num, two_den, Int.mul_one]
  omega

/-- Quadratic-row, first-column specialization on the central range. -/
theorem hahnEntry_two_zero (n t : Nat) (ht : 2 <= t) :
    (hahnEntry 2 n t 2 0).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) 2 0) := by
  refine Q'.eqv_trans _ _ _ (hahnEntry_two 2 n t 0) ?_
  unfold centralHahn Q'.eqv
  have ht1 : ((t - 1 : Nat) : Int) = (t : Int) - 1 := by omega
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.neg_den,
    neg_num, one_num, one_den, two_num, two_den, Int.mul_one,
    Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.mul_one, Nat.sub_zero,
    Nat.zero_sub, Nat.add_zero, Nat.zero_add]
  push_cast
  rw [ht1]
  simp only [Int.zero_add, Int.zero_mul, Int.add_zero, Int.sub_eq_add_neg,
    Int.mul_assoc]

/-- Quadratic-row, middle-column specialization on the central range. -/
theorem hahnEntry_two_one (n t : Nat) (ht : 2 <= t) (htn : t <= n) :
    (hahnEntry 2 n t 2 1).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) 2 1) := by
  refine Q'.eqv_trans _ _ _ (hahnEntry_two 2 n t 1) ?_
  unfold centralHahn Q'.eqv
  have ht1 : ((t - 1 : Nat) : Int) = (t : Int) - 1 := by omega
  have hnt1 : ((n - (t - 1) : Nat) : Int) =
      (n : Int) - (t : Int) + 1 := by omega
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.neg_den,
    neg_num, one_num, one_den, two_num, two_den, Int.mul_one,
    Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.mul_one, Nat.sub_zero,
    Nat.zero_sub, Nat.add_zero, Nat.zero_add]
  push_cast
  rw [ht1, hnt1]
  simp only [Int.zero_add, Int.zero_mul, Int.add_zero, Int.sub_eq_add_neg,
    Int.mul_assoc]

/-- Quadratic-row, last-column specialization on the central range. -/
theorem hahnEntry_two_two (n t : Nat) (ht : 2 <= t) (htn : t <= n) :
    (hahnEntry 2 n t 2 2).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) 2 2) := by
  refine Q'.eqv_trans _ _ _ (hahnEntry_two 2 n t 2) ?_
  unfold centralHahn Q'.eqv
  have hnt2 : ((n - (t - 2) : Nat) : Int) =
      (n : Int) - (t : Int) + 2 := by omega
  have hnt21 : ((n - (t - 2) - 1 : Nat) : Int) =
      (n : Int) - (t : Int) + 1 := by omega
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.neg_den,
    neg_num, one_num, one_den, two_num, two_den, Int.mul_one,
    Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.mul_one, Nat.sub_zero,
    Nat.zero_sub, Nat.add_zero, Nat.zero_add]
  push_cast
  rw [hnt2, hnt21]
  simp only [Int.zero_add, Int.zero_mul, Int.add_zero, Int.sub_eq_add_neg,
    Int.mul_assoc]
  omega

/-- All nine physical entries on a central spin-one shell agree with the
symbolic matrix. -/
theorem hahnEntry_eq_central (n t r i : Nat) (ht : 2 <= t) (htn : t <= n)
    (hr : r < 3) (hi : i < 3) :
    (hahnEntry 2 n t r i).eqv
      (centralHahn (Q'.ofNat n) (Q'.ofNat t) r i) := by
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hr' with rfl | rfl | rfl <;> rcases hi' with rfl | rfl | rfl
  · exact hahnEntry_zero_central n t 0
  · exact hahnEntry_zero_central n t 1
  · exact hahnEntry_zero_central n t 2
  · exact hahnEntry_one_zero n t
  · exact hahnEntry_one_one n t ht htn
  · exact hahnEntry_one_two n t ht htn
  · exact hahnEntry_two_zero n t ht
  · exact hahnEntry_two_one n t ht htn
  · exact hahnEntry_two_two n t ht htn

end YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge

#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.ofNat_sub_eqv
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_zero_central
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_one_zero
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_one_one
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_one_two
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_two_zero
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_two_one
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_two_two
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge.hahnEntry_eq_central
