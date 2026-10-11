/-
# Computed finite polynomial localization parameters

The degree block `D c` lies between `2*c` and `2*c+1` for nonnegative
`c`. The halving exponent `n eta heta` is obtained from the existing binary
search, not from the denominator of `eta`; it is positive and its actual
halving power is at most `eta`. These are rational scalar parameters for
finite polynomial localization, not a partition or response estimate.
-/

import YMGap.Constructive.DyadicTimeRationals
import YMGap.Continuum.HamiltonianAllSep

namespace YMGap.Continuum.PolynomialHeatLocalizationParameters

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.DyadicTimeRationals
open YMGap.Constructive.HalfPow (half)
open YMGap.Continuum.HamiltonianAllSep

local infix:50 " ≈ " => Q'.eqv

/-- A value-based integer degree, computed by the depth-zero upper mesh. -/
def D (c : Q') : Nat := (upper ((2 : Q') * c) 0).steps

private theorem upper_zero_value (c : Q') :
    value (upper ((2 : Q') * c) 0) ≈ Q'.ofNat (D c) := by
  change (value (upper ((2 : Q') * c) 0)).num *
      ((Q'.ofNat (D c)).den : Int) =
    (Q'.ofNat (D c)).num * ((value (upper ((2 : Q') * c) 0)).den : Int)
  rw [value_num, value_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast]
  change (D c : Int) * 1 = (D c : Int) * 1
  rfl

/-- The degree is positive even at zero cost. -/
theorem D_positive (c : Q') : 0 < D c := upper_steps_positive _ 0

/-- The computed degree pays twice the actual rational cost. -/
theorem D_lower (c : Q') (hc : (0 : Q') ≤ c) :
    (2 : Q') * c ≤ Q'.ofNat (D c) :=
  Q'.le_trans' _ _ _
    (rational_le_upper _ (Q'.mul_nonneg _ _ (by decide) hc) 0)
    (Q'.le_of_eqv (upper_zero_value c))

/-- Rounding adds at most one, independently of the rational representation. -/
theorem D_upper (c : Q') (hc : (0 : Q') ≤ c) :
    Q'.ofNat (D c) ≤ (2 : Q') * c + 1 := by
  have hu := (upper_error ((2 : Q') * c)
    (Q'.mul_nonneg _ _ (by decide) hc) 0).2
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (upper_zero_value c)) hu

private theorem num_lt_den (eta : Q') (h : eta < (1 : Q')) :
    eta.num < (eta.den : Int) := by
  change eta.num * 1 < 1 * (eta.den : Int) at h
  simpa only [Int.mul_one, Int.one_mul] using h

/-- Positive binary-search exponent; the below-one branch records
`eta*2^(n-1)<1<=eta*2^n` in the original search datum. -/
def n (eta : Q') (heta : (0 : Q') < eta) : Nat :=
  if h : eta < (1 : Q') then
    (binExpOf eta (Q'.num_pos_of_pos heta) (num_lt_den eta h)).k + 1
  else 1

/-- There is no zero-exponent branch in these selected parameters. -/
theorem n_positive (eta : Q') (heta : (0 : Q') < eta) :
    1 ≤ n eta heta := by
  unfold n
  split
  · exact Nat.succ_le_succ (Nat.zero_le _)
  · exact Nat.le_refl 1

/-- The actual halving power is bounded by the requested positive floor. -/
theorem half_pow_n_le (eta : Q') (heta : (0 : Q') < eta) :
    half ^ n eta heta ≤ eta := by
  by_cases h : eta < (1 : Q')
  · rw [n, dif_pos h]
    let be := binExpOf eta (Q'.num_pos_of_pos heta) (num_lt_den eta h)
    change (half ^ (be.k + 1)).num * (eta.den : Int) ≤
      eta.num * ((half ^ (be.k + 1)).den : Int)
    rw [half_power_num, half_power_den, Int.one_mul]
    exact be.hge
  · rw [n, dif_neg h]
    have hden : (eta.den : Int) ≤ eta.num := by
      have hn : ¬ eta.num < (eta.den : Int) := by
        intro hn
        apply h
        change eta.num * 1 < 1 * (eta.den : Int)
        simpa only [Int.mul_one, Int.one_mul] using hn
      omega
    have hone : (1 : Q') ≤ eta := by
      change 1 * (eta.den : Int) ≤ eta.num * 1
      simpa only [Int.one_mul, Int.mul_one] using hden
    exact Q'.le_trans' _ _ _ (by decide : half ^ 1 ≤ (1 : Q')) hone

end YMGap.Continuum.PolynomialHeatLocalizationParameters

#print axioms YMGap.Continuum.PolynomialHeatLocalizationParameters.D
#print axioms YMGap.Continuum.PolynomialHeatLocalizationParameters.D_positive
#print axioms YMGap.Continuum.PolynomialHeatLocalizationParameters.D_lower
#print axioms YMGap.Continuum.PolynomialHeatLocalizationParameters.D_upper
#print axioms YMGap.Continuum.PolynomialHeatLocalizationParameters.n
#print axioms YMGap.Continuum.PolynomialHeatLocalizationParameters.n_positive
#print axioms YMGap.Continuum.PolynomialHeatLocalizationParameters.half_pow_n_le
