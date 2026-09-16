/-
# Value-based rounded heat cutoff

For the actual rational nome `0 < w < 1`, round `8 / (1-w)` upward by
taking its floor plus one. This preserves an explicit bounded scale window
and gives a small power without an exact dyadic matching requirement.
No spatial, Harnack, or continuum estimate is asserted here.
-/

import YMGap.Constructive.CRealCanonicalReciprocalIndex
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.HeatRoundedCutoff

open YMGap.Constructive

set_option autoImplicit false

/-- The executable cutoff `floor (8 / (1-w)) + 1`, on `w < 1`. -/
def cutoff (w : Q') : Nat :=
  CReal.canonicalReciprocalIndex ((1 + -w) * Q'.mkPos 1 8 (by decide)) + 1

theorem cutoff_positive (w : Q') : 0 < cutoff w := Nat.succ_pos _

private theorem reciprocal_index_bounds (ε : Q') (hε : (0 : Q') < ε) :
    (ε.den : Int) ≤
        ((CReal.canonicalReciprocalIndex ε + 1 : Nat) : Int) * ε.num ∧
      ((CReal.canonicalReciprocalIndex ε + 1 : Nat) : Int) * ε.num ≤
        (ε.den : Int) + ε.num := by
  have hnum : (0 : Int) < ε.num := CReal.num_pos_of_pos hε
  have hcast : (ε.num.toNat : Int) = ε.num :=
    Int.toNat_of_nonneg (Int.le_of_lt hnum)
  have hnatpos : 0 < ε.num.toNat := by
    have h : (0 : Int) < (ε.num.toNat : Int) := by rw [hcast]; exact hnum
    exact_mod_cast h
  have hlo : ε.den ≤ (ε.den / ε.num.toNat + 1) * ε.num.toNat := by
    have hdiv := Nat.div_add_mod ε.den ε.num.toNat
    have hrem := Nat.mod_lt ε.den hnatpos
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (ε.den / ε.num.toNat)]
    omega
  have hhi : (ε.den / ε.num.toNat + 1) * ε.num.toNat ≤
      ε.den + ε.num.toNat := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self ε.den ε.num.toNat) _
  have hlo' : (ε.den : Int) ≤
      ((ε.den / ε.num.toNat + 1 : Nat) : Int) * (ε.num.toNat : Int) := by
    exact_mod_cast hlo
  have hhi' : ((ε.den / ε.num.toNat + 1 : Nat) : Int) * (ε.num.toNat : Int) ≤
      (ε.den : Int) + (ε.num.toNat : Int) := by
    exact_mod_cast hhi
  rw [hcast] at hlo' hhi'
  exact ⟨hlo', hhi'⟩

private theorem cutoff_cross {w : Q'} (hw1 : w < (1 : Q')) :
    (8 : Int) * ((1 + -w).den : Int) ≤ (cutoff w : Int) * (1 + -w).num ∧
      (cutoff w : Int) * (1 + -w).num ≤
        8 * ((1 + -w).den : Int) + (1 + -w).num := by
  let g : Q' := 1 + -w
  let ε : Q' := g * Q'.mkPos 1 8 (by decide)
  have hε : (0 : Q') < ε :=
    HKPos.q_mul_pos (HKPos.one_sub_pos hw1) (by decide)
  have hnum : ε.num = g.num := by
    change g.num * 1 = g.num
    exact Int.mul_one _
  have hden : (ε.den : Int) = 8 * (g.den : Int) := by
    change ((g * Q'.mkPos 1 8 (by decide)).den : Int) = _
    rw [Q'.mul_den_cast]
    change (g.den : Int) * 8 = 8 * (g.den : Int)
    exact Int.mul_comm _ _
  have h := reciprocal_index_bounds ε hε
  rw [hnum, hden] at h
  exact h

/-- The rounded cutoff supplies at least eight units of nome gap. -/
theorem cutoff_gap_lower {w : Q'} (_hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (8 : Q') ≤ Q'.ofNat (cutoff w) * (1 + -w) := by
  have h := (cutoff_cross hw1).1
  show (8 : Int) * ((Q'.ofNat (cutoff w) * (1 + -w)).den : Int) ≤
    (Q'.ofNat (cutoff w) * (1 + -w)).num * (1 : Int)
  rw [Q'.mul_den_cast]
  change 8 * (1 * ((1 + -w).den : Int)) ≤
    ((cutoff w : Int) * (1 + -w).num) * 1
  simpa only [Int.one_mul, Int.mul_one] using h

/-- Rounding costs at most one additional unit, uniformly for `0 < w < 1`. -/
theorem cutoff_gap_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.ofNat (cutoff w) * (1 + -w) ≤ (9 : Q') := by
  have h := (cutoff_cross hw1).2
  have hg1 : 1 + -w ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left 1 (-w) (-(0 : Q')) (Q'.neg_le_neg (Q'.le_of_lt hw0)))
      (by decide)
  have hgnum : (1 + -w).num ≤ ((1 + -w).den : Int) := by
    change (1 + -w).num * 1 ≤ 1 * ((1 + -w).den : Int) at hg1
    simpa only [Int.mul_one, Int.one_mul] using hg1
  show (Q'.ofNat (cutoff w) * (1 + -w)).num * (1 : Int) ≤
    (9 : Int) * ((Q'.ofNat (cutoff w) * (1 + -w)).den : Int)
  rw [Q'.mul_den_cast]
  change ((cutoff w : Int) * (1 + -w).num) * 1 ≤
    9 * (1 * ((1 + -w).den : Int))
  simp only [Int.mul_one, Int.one_mul]
  omega

/-- The actual nome power at the rounded cutoff is at most one eighth. -/
theorem power_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    w ^ cutoff w ≤ Q'.mkPos 1 8 (by decide) := by
  have hg : (0 : Q') ≤ 1 + -w := Q'.le_of_lt (HKPos.one_sub_pos hw1)
  have hB : (8 : Q') ≤ HKConvGen.bScale (1 + -w) (cutoff w) :=
    Q'.le_trans' _ _ _ (cutoff_gap_lower hw0 hw1)
      (HKConvGen.ofNat_mul_le_bScale hg (cutoff w))
  have hscale : (1 : Q') ≤
      HKConvGen.bScale (1 + -w) (cutoff w) * Q'.mkPos 1 8 (by decide) :=
    Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 8 * Q'.mkPos 1 8 (by decide))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hB (by decide))
  have hBpos : (0 : Q') < HKConvGen.bScale (1 + -w) (cutoff w) :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 8) hB
  exact HKConvGen.mul_le_mul_left_cancel hBpos
    (Q'.le_trans' _ _ _
      (HKConvGen.bernoulli_pow (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (cutoff w))
      hscale)

/-- Equivalent positive subunit nomes compute exactly the same cutoff. -/
theorem cutoff_eq_of_eqv {w v : Q'}
    (_hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (_hv0 : (0 : Q') < v) (hv1 : v < (1 : Q')) (h : Q'.eqv w v) :
    cutoff w = cutoff v := by
  have he : Q'.eqv ((1 + -w) * Q'.mkPos 1 8 (by decide))
      ((1 + -v) * Q'.mkPos 1 8 (by decide)) :=
    Q'.mul_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr w v h))
  have hw : (0 : Q') < (1 + -w) * Q'.mkPos 1 8 (by decide) :=
    HKPos.q_mul_pos (HKPos.one_sub_pos hw1) (by decide)
  have hv : (0 : Q') < (1 + -v) * Q'.mkPos 1 8 (by decide) :=
    HKPos.q_mul_pos (HKPos.one_sub_pos hv1) (by decide)
  apply congrArg (fun n : Nat => n + 1)
  exact Nat.le_antisymm
    (CReal.canonicalReciprocalIndex_antitone _ _ hv (Q'.ge_of_eqv he))
    (CReal.canonicalReciprocalIndex_antitone _ _ hw (Q'.le_of_eqv he))

#print axioms cutoff
#print axioms cutoff_positive
#print axioms cutoff_gap_lower
#print axioms cutoff_gap_upper
#print axioms power_le
#print axioms cutoff_eq_of_eqv

end YMGap.Continuum.HeatRoundedCutoff
