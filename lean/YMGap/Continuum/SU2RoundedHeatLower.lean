/-
# Rounded exponential payment for the actual positive heat-window floor

The existing window lower endpoint is the retained Euler prefix squared,
divided by 64. The proved all-length Euler floor therefore pays it with
`4^(4*N(w)+3)`, where N is the executable rounded nome cutoff.
This supplies the lower-side budget only, not the upper-side spread estimate,
an interacting comparison, an OS transfer bound, or a continuum gap.
-/

import YMGap.Continuum.EulerRoundedBlockFloor
import YMGap.Continuum.SU2PointwiseHeatPositiveWindow

namespace YMGap.Continuum.SU2RoundedHeatLower

open YMGap.Constructive
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient

set_option autoImplicit false

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

local macro "mul_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Cheb.mul_num, Q'.mul_den_cast]; ac_rfl))

/-- Exact pin to the existing Euler prefix, without changing the window. -/
theorem lower_formula (w : Q') :
    SU2PointwiseHeatPositiveWindow.lower w ≈
      (euler w (EulerProductStrictFloor.cutoff w) *
        euler w (EulerProductStrictFloor.cutoff w)) * Q'.mkPos 1 64 (by decide) := by
  unfold SU2PointwiseHeatPositiveWindow.lower SU2PointwiseHeatStrictFloor.finiteFloor
    SU2PointwiseHeatStrictFloor.floor ThetaProductStrictFloor.floor EulerProductStrictFloor.floor
  let E := euler w (EulerProductStrictFloor.cutoff w)
  let h := HalfPow.half
  change (((E * h) * (E * h)) * (h * h)) * h * h ≈
    (E * E) * Q'.mkPos 1 64 (by decide)
  calc (((E * h) * (E * h)) * (h * h)) * h * h
      ≈ (E * E) * ((h * h) * (h * h) * (h * h)) := by mul_ring
    _ ≈ (E * E) * Q'.mkPos 1 64 (by decide) :=
      Q'.mul_eqv_congr_left _ _ _ (by decide)

private theorem power_payment (N : Nat) :
    (4 : Q') ^ (4 * N + 3) *
      (((Q'.mkPos 1 16 (by decide)) ^ N * (Q'.mkPos 1 16 (by decide)) ^ N) *
        Q'.mkPos 1 64 (by decide)) ≈ 1 := by
  induction N with
  | zero => decide
  | succ N ih =>
      rw [show 4 * (N + 1) + 3 = (4 * N + 3) + 1 + 1 + 1 + 1 by omega]
      let a := Q'.mkPos 1 16 (by decide)
      let c := Q'.mkPos 1 64 (by decide)
      change ((4 : Q') * (4 * (4 * (4 * (4 : Q') ^ (4 * N + 3))))) *
        (((a * a ^ N) * (a * a ^ N)) * c) ≈ 1
      calc ((4 : Q') * (4 * (4 * (4 * (4 : Q') ^ (4 * N + 3))))) *
            (((a * a ^ N) * (a * a ^ N)) * c)
          ≈ (((4 : Q') * 4 * 4 * 4) * a * a) *
            ((4 : Q') ^ (4 * N + 3) * ((a ^ N * a ^ N) * c)) := by mul_ring
        _ ≈ (1 : Q') * ((4 : Q') ^ (4 * N + 3) * ((a ^ N * a ^ N) * c)) :=
          Q'.mul_eqv_congr_right _ _ _ (by decide)
        _ ≈ (4 : Q') ^ (4 * N + 3) * ((a ^ N * a ^ N) * c) := Q'.one_mul_eqv _
        _ ≈ (1 : Q') := ih

/-- Explicit exponential payment for the actual finite-tail window floor. -/
theorem lower_paid {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ (4 : Q') ^ (4 * HeatRoundedCutoff.cutoff w + 3) *
      SU2PointwiseHeatPositiveWindow.lower w := by
  let N := HeatRoundedCutoff.cutoff w
  let E := euler w (EulerProductStrictFloor.cutoff w)
  let a := Q'.mkPos 1 16 (by decide)
  let c := Q'.mkPos 1 64 (by decide)
  have hE : a ^ N ≤ E :=
    EulerRoundedBlockFloor.rounded_euler_floor hw0 hw1 (EulerProductStrictFloor.cutoff w)
  have hs : (a ^ N * a ^ N) * c ≤ (E * E) * c :=
    Q'.mul_le_mul_of_nonneg_right _ _ c
      (HKConv.mul_le_mul' (Q'.pow_nonneg a (by decide) N)
        (Q'.le_of_lt (euler_pos hw0 hw1 _)) hE hE) (by decide)
  have hl : (a ^ N * a ^ N) * c ≤ SU2PointwiseHeatPositiveWindow.lower w :=
    Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv (lower_formula w))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (power_payment N))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hl
      (Q'.pow_nonneg (4 : Q') (by decide) (4 * N + 3)))

/-- The same actual lower endpoint never exceeds one sixty-fourth. -/
theorem lower_le_oneSixtyFourth {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    SU2PointwiseHeatPositiveWindow.lower w ≤ Q'.mkPos 1 64 (by decide) := by
  let E := euler w (EulerProductStrictFloor.cutoff w)
  have hE : E ≤ (1 : Q') :=
    EulerProductStrictFloor.euler_antitone hw0 hw1 (Nat.zero_le _)
  have hs : E * E ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (HKConv.mul_le_mul' (Q'.le_of_lt (euler_pos hw0 hw1 _)) Q'.zero_le_one hE hE)
      (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (lower_formula w))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.mkPos 1 64 (by decide)) hs (by decide))
      (Q'.le_of_eqv (Q'.one_mul_eqv _)))

theorem lower_le_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    SU2PointwiseHeatPositiveWindow.lower w ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (lower_le_oneSixtyFourth hw0 hw1) (by decide)

#print axioms lower_formula
#print axioms lower_paid
#print axioms lower_le_oneSixtyFourth
#print axioms lower_le_one

end YMGap.Continuum.SU2RoundedHeatLower
