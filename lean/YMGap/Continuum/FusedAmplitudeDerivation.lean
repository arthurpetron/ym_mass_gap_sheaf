/-
`FusedAmplitudeDerivation` — Milestone 13.4, step 4 (OPENED): the
CONSTRUCTIVE derivation route for the fused channel amplitudes, replacing
any appearance of "matching measured numbers" (measurement-model map §6,
v2 correction).

# The principle (map §0)

One RG block step on a compact group is a FINITE Haar integral — a finite
character sum — an EXACT RATIONAL in-substrate.  The fused channel
amplitudes are therefore DERIVABLE objects (`bondMovedCoeff`/`boxSum` are
precisely these sums); the item-9 MCMC was scouting only, and no measured
number may enter the proof.  This module opens the derivation front with
its first reusable bricks and names the target.

# What is delivered (all PROVED, axiom-clean)

  * `qpow_mono_base` — base-monotonicity of the channel weight
    (`0 ≤ x ≤ y → qpow x n ≤ qpow y n`), the elementary brick every
    channel-wise domination step uses;
  * `coeffW_mono_w` — the character coefficient `coeffW w s = dimQ s·w^{C₄(s)}`
    is monotone in the coupling on `[0, ∞)` channelwise;
  * `boxSum_mono_w` — the one-step fused (p = 2) channel sum `boxSum w N s`
    is monotone in `w` (termwise through the fusion indicator) — the
    exact-rational comparison principle for blocked coefficients.

# The NAMED derivation target (deliberately uninhabited — the honest core)

`FusedDominatedByHK` — that the one-step fused channel coefficient, as a
function of `u = 1 − w`, is dominated channel-wise by an exact heat-kernel
channel `d_s · (1−u)^{n_s}` with DERIVED amplitude `d_s` (an exact rational
produced by the character calculus, e.g. a `boxSum`/Clebsch value) — the
constructive replacement for `TMDefectCertificateOS.dominate`'s content.
Inhabiting it is character/Clebsch calculus over the compact group: finite,
exact, in-substrate — genuinely hard where the blocked action's
NON-single-channel terms interfere, which is exactly the interacting
physics (map §0, second fact).  NOT faked here.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  No `Classical.*`, no `Real`, no
`native_decide`, no `sorry` / `admit` / new `axiom`.  Gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.HKChannelList
import YMGap.Continuum.SelfFusionLogConcave

namespace YMGap.Continuum.FusedAmplitudeDerivation

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.HKChannelList

/-! ## 1. Base-monotonicity bricks -/

/-- `0 ≤ x ≤ y → qpow x n ≤ qpow y n`. -/
theorem qpow_mono_base {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n, qpow x n ≤ qpow y n
  | 0 => Q'.le_refl' 1
  | n + 1 => by
      show qpow x n * x ≤ qpow y n * y
      exact Q'.mul_le_mul_of_nonneg (qpow_mono_base hx hxy n) hxy
        (qpow_nonneg _ (Q'.le_trans' _ _ _ hx hxy) n) hx

/-- The character coefficient is monotone in the coupling, channelwise. -/
theorem coeffW_mono_w {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y)
    (s : Nat) : coeffW x s ≤ coeffW y s := by
  show dimQ s * qpow x (c4 s) ≤ dimQ s * qpow y (c4 s)
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (qpow_mono_base hx hxy (c4 s)) (dimQ_nonneg s)

/-- Termwise `fsum` monotonicity (local replica). -/
theorem fsum_le_fsum' {f g : Nat → Q'} (h : ∀ i, f i ≤ g i) :
    ∀ n, fsum f n ≤ fsum g n
  | 0 => Q'.le_refl' 0
  | n + 1 => Q'.add_le_add (fsum_le_fsum' h n) (h n)

/-- **`boxSum_mono_w` (PROVED).**  The one-step fused (p = 2) channel sum is
monotone in the coupling: `0 ≤ x ≤ y → boxSum x N s ≤ boxSum y N s` —
termwise through the (nonnegative) fusion indicator.  The exact-rational
comparison principle for blocked coefficients. -/
theorem boxSum_mono_w {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y)
    (N s : Nat) : boxSum x N s ≤ boxSum y N s := by
  unfold boxSum
  exact fsum_le_fsum'
    (fun a => fsum_le_fsum'
      (fun b =>
        Q'.mul_le_mul_of_nonneg_left _ _ _
          (Q'.mul_le_mul_of_nonneg (coeffW_mono_w hx hxy a)
            (coeffW_mono_w hx hxy b)
            (coeffW_nonneg (Q'.le_trans' _ _ _ hx hxy) a)
            (coeffW_nonneg hx b))
          (fusionInd_nonneg a b s))
      (N + 1))
    (N + 1)

/-! ## 2. THE NAMED DERIVATION TARGET -/

/-- **`FusedDominatedByHK` (NAMED-OPEN — the constructive core of
`dominate`).**  The one-step fused channel coefficient at coupling
`w = 1 − u`, dominated channel-wise by an exact heat-kernel channel with a
DERIVED rational amplitude.  Inhabiting this for the real blocked action's
channels — by character/Clebsch calculus over the compact group, exact and
finite — is the constructive replacement for any "matching": no measured
number enters.  LEFT UNINHABITED (the interacting physics), never faked. -/
structure FusedDominatedByHK (N s : Nat) : Type where
  /-- The DERIVED amplitude (an exact rational from the character calculus). -/
  amp : Q'
  /-- The derived channel exponent. -/
  expn : Nat
  /-- Amplitude nonnegativity. -/
  amp_nonneg : (0 : Q') ≤ amp
  /-- **The channel-wise domination** of the fused coefficient by the exact
  heat-kernel channel, uniformly on the coupling window. -/
  dominates : ∀ u, (0 : Q') ≤ u → u ≤ (1 : Q') →
    boxSum ((1 : Q') - u) N s ≤ amp * qpow ((1 : Q') - u) expn

/-- **The producer (PROVED):** channel-wise fused domination assembles into
the list-certificate pipeline — if each retained channel of the blocked
action is `FusedDominatedByHK`-dominated and the derived amplitudes (plus
tail budget) pass the single kernel certificate, the uniform
`singleStep`-shaped defect bound follows via
`HKChannelList.hk_defect_uniform_tail`.  (Stated here as the wiring
comment; the assembly is definitional once the inhabitants exist — the
open content is ONLY the `dominates` fields.) -/
theorem fused_channel_le_amp {N s : Nat} (F : FusedDominatedByHK N s) :
    ∀ u, (0 : Q') ≤ u → u ≤ (1 : Q') →
      boxSum ((1 : Q') - u) N s ≤ F.amp := by
  intro u hu0 hu1
  refine Q'.le_trans' _ _ _ (F.dominates u hu0 hu1) ?_
  exact YMGap.Continuum.HeatKernelChannelTM.hk_channel_le
    F.amp_nonneg F.expn hu0 hu1

end YMGap.Continuum.FusedAmplitudeDerivation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusedAmplitudeDerivation.qpow_mono_base
#print axioms YMGap.Continuum.FusedAmplitudeDerivation.coeffW_mono_w
#print axioms YMGap.Continuum.FusedAmplitudeDerivation.boxSum_mono_w
#print axioms YMGap.Continuum.FusedAmplitudeDerivation.fused_channel_le_amp
