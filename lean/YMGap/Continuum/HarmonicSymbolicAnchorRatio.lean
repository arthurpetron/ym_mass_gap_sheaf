/-
# Symbolic coefficient ratio for variable harmonic anchors

This removes the per-anchor polynomial identity from the fixed-head PF2
modules.  The exact dimension factor is kept division-free:

  (b+1)c_(b+1) = ((b+2)w^(2b+3))c_b.

Consequently a single scalar cross-multiplied ratio bound implies the next
coefficient step for any symbolic anchor `b`.
-/

import YMGap.Continuum.HarmonicFixedTenPrefix

namespace YMGap.Continuum.HarmonicSymbolicAnchorRatio

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

theorem c4_succ_gap (b : Nat) : c4 b + (2 * b + 3) = c4 (b + 1) := by
  unfold c4
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
  omega

/-- Exact cross-multiplied successor ratio, valid at a symbolic index. -/
theorem coeffW_succ_cross_eqv (w : Q') (b : Nat) :
    Q'.ofNat (b + 1) * coeffW w (b + 1) ≈
      (Q'.ofNat (b + 2) * qpow w (2 * b + 3)) * coeffW w b := by
  have hp : qpow w (c4 (b + 1)) ≈
      qpow w (c4 b) * qpow w (2 * b + 3) := by
    rw [← c4_succ_gap b]
    exact qpow_add w (c4 b) (2 * b + 3)
  unfold coeffW dimQ
  have hl := Q'.mul_eqv_congr_left (Q'.ofNat (b + 2)) _ _ hp
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (b + 1)) _ _ hl) ?_
  ring_qeqv

/-- A division-free scalar ratio bound gives the symbolic next-mode step. -/
theorem coeffW_succ_le_of_cross {w R : Q'} (b : Nat)
    (hw0 : (0 : Q') ≤ w)
    (hcross : Q'.ofNat (b + 2) * qpow w (2 * b + 3) ≤
      R * Q'.ofNat (b + 1)) :
    coeffW w (b + 1) ≤ R * coeffW w b := by
  have hc0 : (0 : Q') ≤ coeffW w b := coeffW_nonneg hw0 b
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (coeffW w b) hcross hc0
  have hright : (R * Q'.ofNat (b + 1)) * coeffW w b ≈
      Q'.ofNat (b + 1) * (R * coeffW w b) := by
    ring_qeqv
  have hcancel : Q'.ofNat (b + 1) * coeffW w (b + 1) ≤
      Q'.ofNat (b + 1) * (R * coeffW w b) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (coeffW_succ_cross_eqv w b))
      (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hright))
  exact Q'.le_of_mul_le_mul_left hcancel (Q'.ofNat_succ_pos b)

end YMGap.Continuum.HarmonicSymbolicAnchorRatio

#print axioms YMGap.Continuum.HarmonicSymbolicAnchorRatio.c4_succ_gap
#print axioms YMGap.Continuum.HarmonicSymbolicAnchorRatio.coeffW_succ_cross_eqv
#print axioms YMGap.Continuum.HarmonicSymbolicAnchorRatio.coeffW_succ_le_of_cross
