/-
`HKChannelList` — Milestone 13.4, step 3: the channel certificate at
ARBITRARY truncation order, with the truncation TAIL as one more budget
term under the SAME single kernel certificate.

# Why (measurement-model map §3/§5)

The pilot fixed the truncation at `N = 4` channels.  A real variational
measurement uses whatever operator basis it needs, and the discarded
(excited-state) tail enters the error budget as one exponentially small
term (`TruncationTailChannelBound`'s ϑ₃ bound).  This module makes the
certified pipeline match that shape: channels are a LIST of
(amplitude, Casimir-exponent) pairs, the certificate is the single kernel
`decide` `Σ amplitudes ≤ 6`, and the tail folds in as a constant budget
term — any truncation order, one check.

# What is delivered (all PROVED, axiom-clean)

  * `hkSum` / `ampSum` / `ampsNonnegB` — the list-indexed heat-kernel
    channel sum, its amplitude sum, and the decidable nonnegativity test;
  * `hkSum_nonneg` / `hkSum_le_ampSum` — the DERIVED uniform enclosure at
    every truncation order (`0 ≤ hkSum chs u ≤ ampSum chs` on `u ∈ [0,1]`);
  * **`hk_defect_uniform_list`** — the N-channel certificate: if the single
    kernel `decide` `ampSum chs ≤ 6` passes, the truncated defect
    `hkSum chs u · u² ≤ 6u²` at EVERY `u ∈ [0,1]`;
  * **`hk_defect_uniform_tail`** — the tail folded in: retained channels
    plus a constant tail budget `T ≥ 0` (the ϑ₃ bound of the discarded
    channels), certificate `ampSum chs + T ≤ 6`, same conclusion for the
    FULL (retained + tail) defect;
  * `pilot_list_instance` — the `N = 4` pilot re-derived as an instance
    (non-vacuity of the generalization).

# What remains open (AGENTS.md Rule 6)

The amplitude identification (`TMDefectCertificateOS.dominate`) — now at
any truncation order: that the true fused defect is dominated by
`hkSum chs u · u²` with the tail budget.  The ϑ₃ tail VALUE
(`TruncationTailChannelBound.chanTailPartial_le`) supplies the `T`
instance when the fused amplitudes land.  No frontier type is touched;
the Clay problem remains OPEN.

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` / `List` core.  No `Classical.*`, no
`Real`, no `native_decide`, no `sorry` / `admit` / new `axiom`.  Gated
with `#print axioms` (permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.TMDefectCertOneSided

namespace YMGap.Continuum.HKChannelList

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.TaylorModel
open YMGap.Continuum.TaylorModelStep2
open YMGap.Continuum.TruncatedBlockSpinContraction
open YMGap.Continuum.HeatKernelChannelTM

/-! ## 1. List-indexed channels -/

/-- The heat-kernel channel sum over a list of (amplitude, exponent) pairs. -/
def hkSum : List (Q' × Nat) → Q' → Q'
  | [], _ => 0
  | (d, n) :: t, u => d * qpow ((1 : Q') - u) n + hkSum t u

/-- The amplitude sum. -/
def ampSum : List (Q' × Nat) → Q'
  | [] => 0
  | (d, _) :: t => d + ampSum t

/-- Decidable amplitude nonnegativity. -/
def ampsNonnegB : List (Q' × Nat) → Bool
  | [] => true
  | (d, _) :: t => decide ((0 : Q') ≤ d) && ampsNonnegB t

/-! ## 2. The derived enclosure at every truncation order -/

theorem hkSum_nonneg {chs : List (Q' × Nat)} (h : ampsNonnegB chs = true)
    {u : Q'} (hu1 : u ≤ (1 : Q')) : (0 : Q') ≤ hkSum chs u := by
  induction chs with
  | nil => exact Q'.le_refl' 0
  | cons c t ih =>
      obtain ⟨d, n⟩ := c
      have h' : (decide ((0 : Q') ≤ d) && ampsNonnegB t) = true := h
      obtain ⟨hd, ht⟩ := (Bool.and_eq_true _ _).mp h'
      exact Q'.zero_le_add _ _
        (hk_channel_nonneg (of_decide_eq_true hd) n hu1) (ih ht)

/-- **The uniform enclosure, any order:** `hkSum chs u ≤ ampSum chs` on
`u ∈ [0, 1]`. -/
theorem hkSum_le_ampSum {chs : List (Q' × Nat)} (h : ampsNonnegB chs = true)
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    hkSum chs u ≤ ampSum chs := by
  induction chs with
  | nil => exact Q'.le_refl' 0
  | cons c t ih =>
      obtain ⟨d, n⟩ := c
      have h' : (decide ((0 : Q') ≤ d) && ampsNonnegB t) = true := h
      obtain ⟨hd, ht⟩ := (Bool.and_eq_true _ _).mp h'
      exact Q'.add_le_add
        (hk_channel_le (of_decide_eq_true hd) n hu0 hu1) (ih ht)

/-! ## 3. The N-channel certificate and the tail -/

/-- **`hk_defect_uniform_list` (PROVED).**  At ANY truncation order: the
single kernel certificate `ampSum chs ≤ 6` gives
`hkSum chs u · u² ≤ 6u²` at EVERY `u ∈ [0, 1]`. -/
theorem hk_defect_uniform_list (chs : List (Q' × Nat))
    (hnn : ampsNonnegB chs = true)
    (hcert : coeffLeB [0, 0, ampSum chs] sixUsq = true) :
    ∀ u, (0 : Q') ≤ u → u ≤ (1 : Q') →
      hkSum chs u * (u * u) ≤ evalPoly sixUsq u := by
  intro u hu0 hu1
  have husq : (0 : Q') ≤ u * u := Q'.mul_nonneg _ _ hu0 hu0
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (hkSum_le_ampSum hnn hu0 hu1)
      husq) ?_
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (evalPoly_c2 (ampSum chs) u)) ?_
  exact evalPoly_le_of_coeffLeB hu0 [0, 0, ampSum chs] sixUsq hcert

/-- **`hk_defect_uniform_tail` (PROVED — the ϑ₃ tail folded in).**  Retained
channels plus a constant tail budget `T ≥ 0` (the bound on the discarded
excited channels): the certificate `ampSum chs + T ≤ 6` gives the FULL
defect bound `(hkSum chs u + T) · u² ≤ 6u²` at every `u ∈ [0, 1]`. -/
theorem hk_defect_uniform_tail (chs : List (Q' × Nat)) (T : Q')
    (hnn : ampsNonnegB chs = true) (hT : (0 : Q') ≤ T)
    (hcert : coeffLeB [0, 0, ampSum chs + T] sixUsq = true) :
    ∀ u, (0 : Q') ≤ u → u ≤ (1 : Q') →
      (hkSum chs u + T) * (u * u) ≤ evalPoly sixUsq u := by
  intro u hu0 hu1
  have husq : (0 : Q') ≤ u * u := Q'.mul_nonneg _ _ hu0 hu0
  have hsum : hkSum chs u + T ≤ ampSum chs + T :=
    Q'.add_le_add (hkSum_le_ampSum hnn hu0 hu1) (Q'.le_refl' T)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsum husq) ?_
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (evalPoly_c2 (ampSum chs + T) u)) ?_
  exact evalPoly_le_of_coeffLeB hu0 [0, 0, ampSum chs + T] sixUsq hcert

/-! ## 4. The pilot as an instance (non-vacuity) -/

/-- The pilot channel list. -/
def pilotChs : List (Q' × Nat) :=
  [(coeff0.hi, c4 0), (coeff1.hi, c4 1), (coeff2.hi, c4 2), (coeff3.hi, c4 3)]

/-- **`pilot_list_instance` (PROVED — the `N = 4` pilot re-derived).**  The
generalization is non-vacuous: the pilot's four channels pass the list
certificate (`Σ = 39/10 ≤ 6`, one axiom-clean `decide`). -/
theorem pilot_list_instance :
    ∀ u, (0 : Q') ≤ u → u ≤ (1 : Q') →
      hkSum pilotChs u * (u * u) ≤ evalPoly sixUsq u :=
  hk_defect_uniform_list pilotChs (by decide) (by decide)

end YMGap.Continuum.HKChannelList

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HKChannelList.hkSum_nonneg
#print axioms YMGap.Continuum.HKChannelList.hkSum_le_ampSum
#print axioms YMGap.Continuum.HKChannelList.hk_defect_uniform_list
#print axioms YMGap.Continuum.HKChannelList.hk_defect_uniform_tail
#print axioms YMGap.Continuum.HKChannelList.pilot_list_instance
