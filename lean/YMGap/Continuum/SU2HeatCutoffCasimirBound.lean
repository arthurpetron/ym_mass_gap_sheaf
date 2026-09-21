/-
# Scalar cutoff/Casimir attenuation bound

For a fixed finite heat cutoff, the actual SU(2) harmonic attenuation is
either `w^(d(d+2))` or zero.  A single explicit guard on the first omitted
Casimir makes its defect at most the usual linear Bernoulli budget for every
degree.  This is only rational scalar arithmetic; it is not an interacting
energy comparison or a continuum statement.
-/

import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.HeatKernelPos
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.SU2HeatCutoffCasimirBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HKPos

local infix:50 " ≈ " => Q'.eqv

/-- The actual finite-cutoff attenuation of a degree-`d` SU(2) harmonic. -/
def attenuation (w : Q') (K d : Nat) : Q' :=
  if d ≤ K then qpow w (d * (d + 2)) else 0

/-- Finite-cutoff attenuation is nonnegative on the nonnegative nome ray. -/
theorem attenuation_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w) (K d : Nat) :
    (0 : Q') ≤ attenuation w K d := by
  unfold attenuation
  by_cases hd : d ≤ K
  · rw [if_pos hd]
    exact qpow_nonneg w hw0 _
  · rw [if_neg hd]
    exact Q'.le_refl' 0

/-- Finite-cutoff attenuation is at most one on the nome unit interval. -/
theorem attenuation_le_one {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K d : Nat) :
    attenuation w K d ≤ (1 : Q') := by
  unfold attenuation
  by_cases hd : d ≤ K
  · rw [if_pos hd]
    exact qpow_le_one hw0 hw1 _
  · rw [if_neg hd]
    decide

/-- If the first omitted Casimir pays one unit of defect, every cutoff mode
and every omitted mode obeys the same linear Casimir defect estimate. -/
theorem one_sub_attenuation_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K d : Nat)
    (hguard : (1 : Q') ≤
      ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3))) :
    (1 : Q') - attenuation w K d ≤
      ((1 : Q') - w) * Q'.ofNat (d * (d + 2)) := by
  unfold attenuation
  by_cases hd : d ≤ K
  · rw [if_pos hd]
    have hbern := oneSub_qpow_le hw0 hw1 (d * (d + 2))
    exact Q'.le_trans' _ _ _ hbern
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv (Q'.ofNat (d * (d + 2))) ((1 : Q') - w)))
  · rw [if_neg hd]
    have hKd : K + 1 ≤ d := by omega
    have hKCasimir : (K + 1) * (K + 3) ≤ d * (d + 2) :=
      Nat.mul_le_mul hKd (by omega)
    have hmargin : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
    have hscaled :
        ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3)) ≤
          ((1 : Q') - w) * Q'.ofNat (d * (d + 2)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (CReal.ofNat_le_ofNat hKCasimir) hmargin
    have hone : (1 : Q') ≤
        ((1 : Q') - w) * Q'.ofNat (d * (d + 2)) :=
      Q'.le_trans' _ _ _ hguard hscaled
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : ((1 : Q') - 0) ≈ (1 : Q'))) hone

/-- A computable cutoff whose size is the denominator of the positive nome
defect.  It is deliberately elementary rather than asymptotically sharp. -/
def sufficientCutoff (w : Q') : Nat := ((1 : Q') - w).den

private theorem one_le_mul_den_succ {delta : Q'} (hdelta : (0 : Q') < delta) :
    (1 : Q') ≤ delta * Q'.ofNat (delta.den + 1) := by
  have hnum : (0 : Int) < delta.num := Q'.num_pos_of_pos hdelta
  show (1 : Q').num * ((delta * Q'.ofNat (delta.den + 1)).den : Int) ≤
    (delta * Q'.ofNat (delta.den + 1)).num * ((1 : Q').den : Int)
  show (1 : Int) * ((delta * Q'.ofNat (delta.den + 1)).den : Int) ≤
    (delta.num * ((delta.den + 1 : Nat) : Int)) * (1 : Int)
  rw [Q'.mul_den_cast]
  change (1 : Int) * ((delta.den : Int) * 1) ≤
    (delta.num * ((delta.den + 1 : Nat) : Int)) * 1
  simp only [Int.one_mul, Int.mul_one]
  have hden : (delta.den : Int) ≤ ((delta.den + 1 : Nat) : Int) := by
    exact Int.ofNat_le.mpr (Nat.le_succ _)
  have honeNum : (1 : Int) ≤ delta.num := by omega
  have hnonnegative : (0 : Int) ≤ ((delta.den + 1 : Nat) : Int) :=
    Int.natCast_nonneg _
  have hscaled : ((delta.den + 1 : Nat) : Int) ≤
      delta.num * ((delta.den + 1 : Nat) : Int) := by
    have h := Int.mul_le_mul_of_nonneg_right honeNum hnonnegative
    simpa only [Int.one_mul] using h
  exact Int.le_trans hden hscaled

/-- The explicit cutoff satisfies the omitted-Casimir guard for every strict
nome below one.  This is data, not an assumed large-cutoff hypothesis. -/
theorem sufficientCutoff_guard {w : Q'} (hw1 : w < (1 : Q')) :
    (1 : Q') ≤ ((1 : Q') - w) *
      Q'.ofNat ((sufficientCutoff w + 1) * (sufficientCutoff w + 3)) := by
  let delta := (1 : Q') - w
  have hdelta : (0 : Q') < delta := one_sub_pos hw1
  have hbase : (1 : Q') ≤ delta * Q'.ofNat (delta.den + 1) :=
    one_le_mul_den_succ hdelta
  have hNat : delta.den + 1 ≤ (delta.den + 1) * (delta.den + 3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hscaled : delta * Q'.ofNat (delta.den + 1) ≤
      delta * Q'.ofNat ((delta.den + 1) * (delta.den + 3)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (CReal.ofNat_le_ofNat hNat) (Q'.le_of_lt hdelta)
  exact Q'.le_trans' _ _ _ hbase hscaled

/-- Every cutoff above the computed witness satisfies the same guard. -/
theorem cutoff_guard_of_le {w : Q'} (hw1 : w < (1 : Q')) {K : Nat}
    (hK : sufficientCutoff w ≤ K) :
    (1 : Q') ≤ ((1 : Q') - w) * Q'.ofNat ((K+1)*(K+3)) :=
  Q'.le_trans' _ _ _ (sufficientCutoff_guard hw1)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (CReal.ofNat_le_ofNat (Nat.mul_le_mul (by omega) (by omega)))
      (Q'.le_of_lt (one_sub_pos hw1)))

end YMGap.Continuum.SU2HeatCutoffCasimirBound

#print axioms YMGap.Continuum.SU2HeatCutoffCasimirBound.attenuation_nonnegative
#print axioms YMGap.Continuum.SU2HeatCutoffCasimirBound.attenuation_le_one
#print axioms YMGap.Continuum.SU2HeatCutoffCasimirBound.one_sub_attenuation_le
#print axioms YMGap.Continuum.SU2HeatCutoffCasimirBound.sufficientCutoff_guard
#print axioms YMGap.Continuum.SU2HeatCutoffCasimirBound.cutoff_guard_of_le
