/-
# Lightweight positive-time geometric rate-power variation

For any explicit rational base `0 < r < 1`, this module constructs the
summable rational variation of `r^(time * 2^scale)` at every positive integer
time. The fixed BF4 family supplies its concrete `r` through the checked rate
pin and sampler arithmetic; no large continuum compiler is imported here.
-/

import YMGap.Continuum.GeometricAntitoneTailControl
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.GeometricAntitoneTailControl
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SummableRationalStepVariation

private theorem succ_le_two_pow : ∀ n : Nat, n + 1 ≤ 2 ^ n
  | 0 => by decide
  | n + 1 => by
      have h := Nat.mul_le_mul_left 2 (succ_le_two_pow n)
      have hs : n + 2 ≤ 2 * (n + 1) := by omega
      simpa only [Nat.pow_succ, Nat.mul_comm] using Nat.le_trans hs h

private theorem scale_le_two_pow (scale : Nat) : scale ≤ 2 ^ scale := by
  cases scale with
  | zero => exact Nat.zero_le _
  | succ scale =>
      exact Nat.le_trans (succ_le_two_pow scale) (by
        rw [Nat.pow_succ]
        exact Nat.le_mul_of_pos_right _ (by decide))

private theorem scale_le_time_dyadic
    (time scale : Nat) (htime : 0 < time) :
    scale ≤ time * 2 ^ scale := by
  exact Nat.le_trans (scale_le_two_pow scale)
    (Nat.le_mul_of_pos_left _ htime)

private theorem stream_le_variation
    (r : Q') (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (time scale : Nat) (htime : 0 < time) :
    r ^ (time * 2 ^ scale) ≤ r ^ scale := by
  exact HKConvGen.pow_base_antitone
    (Q'.le_of_lt hr0) (Q'.le_of_lt hr1)
    (scale_le_time_dyadic time scale htime)

private theorem stream_nonnegative
    (r : Q') (hr0 : (0 : Q') < r) (time scale : Nat) :
    (0 : Q') ≤ r ^ (time * 2 ^ scale) :=
  Q'.pow_nonneg r (Q'.le_of_lt hr0) (time * 2 ^ scale)

/-- Positive integer times have a constructive rational variation certificate
for an exact dyadic-exponent rate-power stream. -/
def positiveRatePowerVariation
    (r : Q') (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (time : Nat) (htime : 0 < time) :
    SummableRationalStepVariation
      (fun scale => r ^ (time * 2 ^ scale)) where
  variation := fun scale => r ^ scale
  variation_nonnegative := fun scale => Q'.pow_nonneg r (Q'.le_of_lt hr0) scale
  tailControl := geometricPowerTailControl hr0 hr1
  stepBound := by
    intro scale
    have hnext_le := stream_le_variation r hr0 hr1 time (scale + 1) htime
    have hnext_le_variation : r ^ (time * 2 ^ (scale + 1)) ≤ r ^ scale :=
      Q'.le_trans' _ _ _ hnext_le
        (HKConvGen.pow_base_le_succ (Q'.le_of_lt hr0)
          (Q'.le_of_lt hr1) scale)
    have hcurrent_le := stream_le_variation r hr0 hr1 time scale htime
    have hnext_nn := stream_nonnegative r hr0 time (scale + 1)
    have hcurrent_nn := stream_nonnegative r hr0 time scale
    have hvar_le_sum : r ^ scale ≤
        r ^ (time * 2 ^ scale) + r ^ scale :=
      Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg _ _ hcurrent_nn)
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
    have hnext_le_sum : r ^ (time * 2 ^ (scale + 1)) ≤
        r ^ (time * 2 ^ scale) + r ^ scale :=
      Q'.le_trans' _ _ _ hnext_le_variation hvar_le_sum
    have hcurrent_le_sum : r ^ (time * 2 ^ scale) ≤
        r ^ (time * 2 ^ (scale + 1)) + r ^ scale :=
      Q'.le_trans' _ _ _ hcurrent_le
        (Q'.le_trans' _ _ _
          (Q'.add_le_self_of_nonneg _ _ hnext_nn)
          (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
    exact ⟨hnext_le_sum, hcurrent_le_sum⟩

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.positiveRatePowerVariation
