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

/-! ## Positive-time limit obstruction

The preceding certificate proves summability of the exact geometric sampler
stream.  Its positive-time limit is nevertheless zero: the dyadic exponent
`time * 2^scale` eventually exceeds every rational power cutoff.  This is a
constructive consequence of the current spacing family, not a mass-gap
construction. -/

theorem positiveRatePowerVariation_limit_equiv_zero
    (r : Q') (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    (time : Nat) (htime : 0 < time) :
    CReal.Equiv
      (positiveRatePowerVariation r hr0 hr1 time htime).limit
      (CReal.ofQ' 0) := by
  let data := positiveRatePowerVariation r hr0 hr1 time htime
  change CReal.Equiv data.limit (CReal.ofQ' 0)
  have hconv := data.converges
  intro ε hε
  let q : Q' := HalfPow.half * ε
  have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos ε hε
  obtain ⟨Ntail, hNtail⟩ := HKConvGen.pow_base_le hr0 hr1 q hqpos
  obtain ⟨Nconv, hNconv⟩ := hconv q hqpos
  let N : Nat := max Ntail Nconv
  have hNtailN : Ntail ≤ N := Nat.le_max_left _ _
  have hNconvN : Nconv ≤ N := Nat.le_max_right _ _
  obtain ⟨Napx, happrox⟩ := hNconv N hNconvN
  refine ⟨Napx, fun n hn => ?_⟩
  have happrox' :
      r ^ (time * 2 ^ N) ≤ data.limit.approx n + q ∧
        data.limit.approx n ≤ r ^ (time * 2 ^ N) + q := by
    simpa only [CReal.ofQ'_approx] using happrox n hn
  have hexp : N ≤ time * 2 ^ N := scale_le_time_dyadic time N htime
  have hstream : r ^ (time * 2 ^ N) ≤ q :=
    hNtail (time * 2 ^ N) (Nat.le_trans hNtailN hexp)
  have hstream_nonnegative : (0 : Q') ≤ r ^ (time * 2 ^ N) :=
    stream_nonnegative r hr0 time N
  constructor
  · change data.limit.approx n ≤ (0 : Q') + ε
    have hstep : r ^ (time * 2 ^ N) + q ≤ q + q :=
      Q'.add_le_add_right _ _ q hstream
    have hbound : data.limit.approx n ≤ q + q :=
      Q'.le_trans' _ _ _ happrox'.2 hstep
    have hqq : (q + q).eqv ((0 : Q') + ε) :=
      Q'.eqv_trans _ _ _ (ExpNeg.two_halves ε)
        (Q'.eqv_symm (Q'.eqv_of_eq' (Q'.zero_add' ε)))
    exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hqq)
  · change (0 : Q') ≤ data.limit.approx n + ε
    have hzero_q : (0 : Q') ≤ data.limit.approx n + q :=
      Q'.le_trans' _ _ _ hstream_nonnegative happrox'.1
    have hq_le : q ≤ (data.limit.approx n + q) + q := by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_of_eq' (Eq.symm (Q'.zero_add' q)))) ?_
      exact Q'.add_le_add_right _ _ q hzero_q
    have hzero_sum : (0 : Q') ≤ (data.limit.approx n + q) + q :=
      Q'.le_trans' _ _ _ (Q'.le_of_lt hqpos) hq_le
    have hsum_eps : ((data.limit.approx n + q) + q).eqv
        (data.limit.approx n + ε) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (data.limit.approx n) q q) ?_
      exact Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves ε)
    exact Q'.le_trans' _ _ _ hzero_sum (Q'.le_of_eqv hsum_eps)

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.positiveRatePowerVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.positiveRatePowerVariation_limit_equiv_zero
