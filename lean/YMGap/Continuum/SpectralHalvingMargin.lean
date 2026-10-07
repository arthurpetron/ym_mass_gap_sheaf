/-
# Trace bounds ⇒ halving time ⇒ Wilson lower margin (REDUCTION, finite check)

ADDITIVE. Connects `SpectralTraceSandwich` (rational trace bounds on a finite
`SpectralModel`) to `BF4WilsonHalvingTimeMargin` (halving-time certificates).

* `specMax_pow_le_half_of_trace`: `s_n ≤ U ≤ 1/2`, `0 < n` ⇒ `specMax^n ≤ 1/2`.
* `specMax_le_one_of_trace`: the same bound already gives `specMax ≤ 1`.
* `halvingMargin_le_of_trace`: ⇒ `1/(2n) ≤ 1 − specMax` (no extra hypothesis).
* `rate_pow_le_half_of_trace`: any `0 ≤ r ≤ specMax` has `r^n ≤ 1/2`.
* `wilsonLowerMargin_of_traceCertificates` (all scales, `n_j = M0·2^j`) and
  `wilsonLowerMargin_of_traceCertificatesFrom` (certificates only for `j ≥ j0`, all-scale
  margin via `prefixRateMargin`).

**OPEN input, stated as a hypothesis `hlink : F.rate j ≤ specMax (S j)`.** Nothing ties
`WilsonDynamicFamily.rate` (an all-vector squared-norm contraction rate) to a finite
spectral model; the only existing model, `WilsonSpectralBridge.excitedCharModel`, is
closed-form and tied to its transfer operator only via the OPEN
`CharacterDiagResolution`. **REDUCTION / finite check.** Axioms `propext`, `Quot.sound`.
-/

import YMGap.Continuum.SpectralTraceSandwich
import YMGap.Continuum.BF4WilsonHalvingTimeMargin

namespace YMGap.Continuum.SpectralHalvingMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.SpectralGap (SpectralModel pow_le_pow_left)
open YMGap.Continuum (specMax specMax_nonneg)
open YMGap.Continuum.SpectralTraceSandwich
  (excitedTrace specMax_pow_le_excitedTrace specMax_le_of_trace_le)
open YMGap.Continuum.BF4WilsonHalvingTimeMargin
  (halvingMargin margin_of_pow_le_half wilsonLowerMargin_of_halvingTime
   prefixRateMargin wilsonLowerMargin_of_halvingTimeFrom)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily (WilsonDynamicFamily WilsonLowerMargin)
open YMGap.Continuum.BF4WilsonAllNomeStepRatioLinearCeiling (lc_one_pow)

/-- `s_n ≤ U ≤ 1/2`, `0 < n` ⇒ `specMax^n ≤ 1/2`. -/
theorem specMax_pow_le_half_of_trace (S : SpectralModel) (n : Nat) (hn : 0 < n) (U : Q')
    (hU : excitedTrace S n ≤ U) (hUh : U ≤ half) : specMax S ^ n ≤ half :=
  Q'.le_trans' _ _ _ (specMax_pow_le_excitedTrace S n hn) (Q'.le_trans' _ _ _ hU hUh)

/-- The same trace bound gives `specMax ≤ 1` (since `1/2 ≤ 1 = 1^n`). -/
theorem specMax_le_one_of_trace (S : SpectralModel) (n : Nat) (hn : 0 < n) (U : Q')
    (hU : excitedTrace S n ≤ U) (hUh : U ≤ half) : specMax S ≤ 1 :=
  specMax_le_of_trace_le S n hn U 1 (by decide) hU
    (Q'.le_trans' _ _ _ hUh (Q'.le_trans' _ _ _ (by decide : half ≤ (1 : Q'))
      (Q'.le_of_eqv (Q'.eqv_symm (lc_one_pow n)))))

/-- **PROVED (finite check).** `s_n ≤ U ≤ 1/2`, `0 < n` ⇒ `1/(2n) ≤ 1 − specMax`. -/
theorem halvingMargin_le_of_trace (S : SpectralModel) (n : Nat) (hn : 0 < n) (U : Q')
    (hU : excitedTrace S n ≤ U) (hUh : U ≤ half) :
    halvingMargin n ≤ (1 : Q') - specMax S :=
  margin_of_pow_le_half (specMax S) n hn (specMax_nonneg S)
    (specMax_le_one_of_trace S n hn U hU hUh) (specMax_pow_le_half_of_trace S n hn U hU hUh)

/-- Any rate `0 ≤ r ≤ specMax` inherits the halving certificate. -/
theorem rate_pow_le_half_of_trace (S : SpectralModel) (n : Nat) (hn : 0 < n) (U r : Q')
    (hr0 : (0 : Q') ≤ r) (hlink : r ≤ specMax S)
    (hU : excitedTrace S n ≤ U) (hUh : U ≤ half) : r ^ n ≤ half :=
  Q'.le_trans' _ _ _ (pow_le_pow_left hr0 hlink n) (specMax_pow_le_half_of_trace S n hn U hU hUh)

/-- **PROVED (REDUCTION).** Per-scale models `S j`, OPEN link `F.rate j ≤ specMax (S j)`,
trace bounds `s_{M0·2^j}(S j) ≤ U j ≤ 1/2` on dyadic spacing ⇒
`WilsonLowerMargin F (1/(2M0))`. -/
theorem wilsonLowerMargin_of_traceCertificates (F : WilsonDynamicFamily) (M0 : Nat)
    (hM0 : 0 < M0) (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (S : Nat → SpectralModel) (U : Nat → Q') (hlink : ∀ j, F.rate j ≤ specMax (S j))
    (hU : ∀ j, excitedTrace (S j) (M0 * 2 ^ j) ≤ U j) (hUh : ∀ j, U j ≤ half) :
    WilsonLowerMargin F (halvingMargin M0) :=
  wilsonLowerMargin_of_halvingTime F M0 hM0 hsp fun j =>
    rate_pow_le_half_of_trace (S j) (M0 * 2 ^ j) (Nat.mul_pos hM0 (Nat.two_pow_pos j)) (U j)
      (F.rate j) (F.rate_nonnegative j) (hlink j) (hU j) (hUh j)

/-- **PROVED (REDUCTION).** Certificates and link only for `j ≥ j0`; all-scale margin
`prefixRateMargin F.rate (1/(2M0)) j0` (uses `F.rate_lt_one` below `j0`). -/
theorem wilsonLowerMargin_of_traceCertificatesFrom (F : WilsonDynamicFamily) (j0 M0 : Nat)
    (hM0 : 0 < M0) (hsp : ∀ j, F.transferSpacing.spacing j = half ^ j)
    (S : Nat → SpectralModel) (U : Nat → Q')
    (hlink : ∀ j, j0 ≤ j → F.rate j ≤ specMax (S j))
    (hU : ∀ j, j0 ≤ j → excitedTrace (S j) (M0 * 2 ^ j) ≤ U j)
    (hUh : ∀ j, j0 ≤ j → U j ≤ half) :
    WilsonLowerMargin F (prefixRateMargin F.rate (halvingMargin M0) j0) :=
  wilsonLowerMargin_of_halvingTimeFrom F j0 M0 hM0 hsp fun j hj =>
    rate_pow_le_half_of_trace (S j) (M0 * 2 ^ j) (Nat.mul_pos hM0 (Nat.two_pow_pos j)) (U j)
      (F.rate j) (F.rate_nonnegative j) (hlink j hj) (hU j hj) (hUh j hj)

end YMGap.Continuum.SpectralHalvingMargin

#print axioms YMGap.Continuum.SpectralHalvingMargin.specMax_pow_le_half_of_trace
#print axioms YMGap.Continuum.SpectralHalvingMargin.specMax_le_one_of_trace
#print axioms YMGap.Continuum.SpectralHalvingMargin.halvingMargin_le_of_trace
#print axioms YMGap.Continuum.SpectralHalvingMargin.rate_pow_le_half_of_trace
#print axioms YMGap.Continuum.SpectralHalvingMargin.wilsonLowerMargin_of_traceCertificates
#print axioms YMGap.Continuum.SpectralHalvingMargin.wilsonLowerMargin_of_traceCertificatesFrom
