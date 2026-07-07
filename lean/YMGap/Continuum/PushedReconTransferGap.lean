/-
Track B / R2 — DIRECT CONSTRUCTION INCREMENT: pushing the REAL reconstructed
single-edge transfer-operator LOCATED gap (the `trueMargin` candidate of
`SingleStepDefectReduction.SingleStepDefectBound`) PAST the convenience edge
`w ≤ 1/2`, all the way to the SHARP character radius `w* = 2^{−1/3} ≈ 0.7937`,
and PROVING that `w*` is a hard ceiling (not a proof weakness).

# What this module CONSTRUCTS (read first)

`DirectSingleStepReconGap.reconTransfer_located_gap_general` builds the located
spectral gap of the reconstructed single-edge transfer operator
`reconTransfer w hw (M+1)` — with positive margin `reconMargin w = 1 − rho w =
1 − 2w³` — but ONLY on the STRONG-coupling window `w ∈ (0, 1/2]`, because it
consumes the `w ≤ 1/2`-gated `reconTransfer_corr_decay` / `rho_lt_one` /
`coeffW_excited_le_one`.  `CharacterWindowCeiling` separately pushes the Wilson
DECAY window up to `7/9`, but does NOT port the located gap itself.

This module CONSTRUCTS the located gap on the FULL character window by making the
per-scale inputs HYPOTHESES rather than the `w ≤ 1/2` gate:

  * **`reconTransfer_located_gap_gen`** — for ANY `w` with `0 < w`, `w ≤ 1`,
    `rho w < 1` (`⟺ w < 2^{−1/3}`) and the quintic-ratio side condition
    `2·w⁵ ≤ 1` (`⟺ w ≤ 2^{−1/5} ≈ 0.871`, harmless in the whole window), the
    reconstructed single-edge transfer operator has a LOCATED spectral gap with
    `sep = rho w = 2w³ < 1`, hence positive margin `reconMargin w = 1 − 2w³ > 0`.
    The correlator-decay field is built from scratch (`reconTransfer_corr_decay_gen`
    ⇐ the connected-chain sum bound `connSum_le_gen` ⇐ the excited-coefficient
    domination `coeffW_excited_le_head_gen`), so NO `w ≤ 1/2` gate remains — the
    ONLY binding constraint is the genuine clustering-rate condition `rho w < 1`.

  * **`reconTransfer_located_gap_pushed`** — the concrete instance at the PUSHED
    edge `w₀ = 793/1000 = 0.793`, a clean rational a distance `≈ 7×10⁻⁴` BELOW the
    ceiling `2^{−1/3} = 0.79370…`.  The located gap and its positive margin
    `reconMargin (793/1000) = 1 − 2·(793/1000)³ = 1322743/500000000 ≈ 0.00265 > 0`
    are DISCHARGED.  This pushes the proved located-gap window's upper edge from
    `1/2 = 0.5` (the old gate) to `0.793` — i.e. `w₀` moves from `1/2` to within
    `0.0007` of the character radius `w*`.  A genuine range-extension of the real
    reconstructed-transfer gap (task criterion (ii)).

# The SHARP ceiling — the precisely-characterized residual (task criterion (iii))

  * **`no_located_gap_above_ceiling`** — for EVERY `w` with `w³ ≥ 1/2` (i.e.
    `w ≥ 2^{−1/3}`) the reconstructed single-edge transfer operator has NO located
    gap AT ALL: any such gap forces its leading excited eigenvalue
    `lam 0 = rho w = 2w³ ≤ sep < 1`, contradicting `rho w ≥ 1`
    (`CharacterWindowCeiling.character_rate_ge_one_at_ceiling`).  A HARD
    impossibility.  Sharpens `DirectSingleStepReconGap.no_located_gap_at_weak`
    (a single witness at `9/10`) to the EXACT threshold `w³ = 1/2`.

  * Combining `reconTransfer_located_gap_gen` (gap exists for every rational
    `w³ < 1/2`) with `no_located_gap_above_ceiling` (gap absent for every `w³ ≥
    1/2`) LOCATES the single-edge located-gap window EXACTLY as `[0, 2^{−1/3})`.
    The threshold is the character radius `w* = 2^{−1/3}`, where `rho = 2w³ = 1`.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

CONSTRUCTION INCREMENT: the REAL reconstructed single-edge located-gap margin —
the `trueMargin` candidate — is now positive and genuinely located on `[0, 0.793]`,
up from the old `[0, 0.5]` gate, and the window is proved SHARP at exactly
`w* = 2^{−1/3}`.  The remaining obstruction to `SingleStepDefectBound` is UNCHANGED
IN KIND but now SHARPLY LOCATED: the RG flow drives `w_k → 1` (asymptotic freedom),
crossing the character radius `w* = 2^{−1/3}`, ABOVE which the single-edge margin is
negative and NO located gap exists (`rho = 2w³ ≥ 1`, hard impossibility).  A located
transfer gap on `[2^{−1/3}, 1)` — the deep-UV / continuum approach — provably CANNOT
come from the single-edge character mechanism; it requires the genuinely interacting
multi-plaquette block-spin effective action at each scale (the unconstructed `a→0`
object).  `SingleStepDefectBound` is inhabited NOWHERE here; NO new `:=
SingleStepDefectBound` alias is emitted; NO 4D Yang–Mills mass gap is claimed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing the PROVED `coeffW_succ_ratio`,
`reconTransfer_corr_eq_connSum`, `clustering_implies_located`, `coeffW_pos`,
`character_rate_ge_one_at_ceiling`, `pow_le_pow_of_le`.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`, no `ring`/`nlinarith`.  Type-
level witnesses are `Type` data (Rule 8).  `decide` is used ONLY on closed concrete-
rational facts at the pushed edge `793/1000` and the ceiling witness.
-/

import YMGap.Continuum.DirectSingleStepReconGap
import YMGap.Continuum.CharacterWindowCeiling

namespace YMGap.Continuum.PushedReconTransferGap

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.TransferCorr
open YMGap.Continuum.ClusteringImpliesGap
open YMGap.Continuum.MayerClustering
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.DirectSingleStepReconGap

/-! ## 1. GENERAL excited-coefficient domination from the quintic-ratio side condition.

The excited non-increase `coeffW w (s+1) ≤ coeffW w s` for `s ≥ 1` follows from the
per-rep ratio `coeffW w (s+1) ≤ (2w⁵)·coeffW w s` (`coeffW_succ_ratio`) whenever the
ratio factor `2w⁵ ≤ 1`.  We take that as a HYPOTHESIS (`hquint`) rather than derive it
from the convenience gate `w ≤ 1/2`, so the domination holds on the whole character
window. -/

/-- **One step of the excited non-increase (GENERAL).**  For `0 ≤ w ≤ 1`, the quintic
side condition `2·w⁵ ≤ 1`, and `s ≥ 1`: `coeffW w (s+1) ≤ coeffW w s`.  Genuine per-rep
ratio `coeffW_succ_ratio` scaled by `2w⁵ ≤ 1` and `coeffW ≥ 0`.  Mirrors
`WilsonConnCorr.coeffW_succ_le_self` but with `hquint` in place of the `w ≤ 1/2` gate. -/
theorem coeffW_succ_le_self_gen {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hquint : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q')) (s : Nat) (hs : 1 ≤ s) :
    coeffW w (s + 1) ≤ coeffW w s := by
  have hratio : coeffW w (s + 1) ≤ (Q'.ofNat 2 * qpow w 5) * coeffW w s :=
    coeffW_succ_ratio hw0 hw1 s hs
  have hcnn : (0 : Q') ≤ coeffW w s := coeffW_nonneg hw0 s
  have hstep : (Q'.ofNat 2 * qpow w 5) * coeffW w s ≤ (1 : Q') * coeffW w s :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hquint hcnn
  refine Q'.le_trans' _ _ _ hratio (Q'.le_trans' _ _ _ hstep ?_)
  exact Q'.le_of_eqv (Q'.one_mul_eqv (coeffW w s))

/-- **The excited coefficients are dominated by their head (GENERAL).**  For `0 ≤ w ≤ 1`
and `2·w⁵ ≤ 1`, every excited coefficient is `≤ coeffW w 1 = rho w = 2w³`:
`coeffW w (1 + k) ≤ coeffW w 1` for every `k`.  Induction on `k` via
`coeffW_succ_le_self_gen`. -/
theorem coeffW_excited_le_head_gen {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hquint : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q')) :
    ∀ k, coeffW w (1 + k) ≤ coeffW w 1 := by
  intro k
  induction k with
  | zero => exact Q'.le_refl' _
  | succ j ih =>
      have hidx : (1 + (j + 1) : Nat) = (1 + j) + 1 := by omega
      rw [hidx]
      exact Q'.le_trans' _ _ _
        (coeffW_succ_le_self_gen hw0 hw1 hquint (1 + j) (by omega)) ih

/-! ## 2. GENERAL correlator decay of the reconstructed transfer operator.

`corr (reconTransfer w hw M) n ≃ connSum w M n` (`reconTransfer_corr_eq_connSum`), and
each connected chain term is `≤ (rho w)^{n+1}` under the head domination, so the
`M`-term sum is `≤ (M·rho w)·(rho w)^n`.  No `wilsonG_decay` gate is used. -/

/-- Each collapsed excited term is `≤ (rho w)^{n+1}` under the head domination:
`connChain w (1+k) n = (coeffW w (1+k))^{n+1} ≤ (coeffW w 1)^{n+1} = (rho w)^{n+1}`. -/
theorem connChain_excited_le_gen {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hdom : ∀ k, coeffW w (1 + k) ≤ coeffW w 1) (k n : Nat) :
    connChain w (1 + k) n ≤ (rho w) ^ (n + 1) := by
  unfold connChain rho
  exact pow_le_pow_of_le (coeffW_nonneg hw0 (1 + k)) (hdom k) (n + 1)

/-- The collapsed connected sum is bounded by `(ofNat M)·(rho w)^{n+1}` under the head
domination.  Induction on `M`, mirroring `WilsonConnCorr.connSum_le`. -/
theorem connSum_le_gen {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hdom : ∀ k, coeffW w (1 + k) ≤ coeffW w 1) (M n : Nat) :
    connSum w M n ≤ Q'.ofNat M * (rho w) ^ (n + 1) := by
  unfold connSum
  induction M with
  | zero =>
      show (0 : Q') ≤ Q'.ofNat 0 * (rho w) ^ (n + 1)
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ k ih =>
      rw [finSum_succ]
      have hstep : finSum (fun j => connChain w (1 + j) n) k + connChain w (1 + k) n
          ≤ Q'.ofNat k * (rho w) ^ (n + 1) + (rho w) ^ (n + 1) := by
        refine Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ (connChain w (1 + k) n) ih) ?_
        exact Q'.add_le_add_left _ _ _ (connChain_excited_le_gen hw0 hdom k n)
      refine Q'.le_trans' _ _ _ hstep ?_
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ ((rho w) ^ (n + 1)) (Q'.ofNat_add_eqv k 1)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv (Q'.ofNat k) (Q'.ofNat 1) ((rho w) ^ (n + 1))) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 1) 1 ((rho w) ^ (n + 1)) (by decide)) ?_
      exact Q'.one_mul_eqv ((rho w) ^ (n + 1))

/-- **`reconTransfer_corr_decay_gen` — the GENERAL correlator decay (PROVED).**  For
`0 ≤ w` and the head domination `coeffW w (1+k) ≤ coeffW w 1`, the reconstructed
transfer operator's abstract two-point function decays geometrically:
`corr (reconTransfer w hw0 M) n ≤ (ofNat M · rho w)·(rho w)^n`.  Via
`reconTransfer_corr_eq_connSum` + `connSum_le_gen`; no `w ≤ 1/2` gate. -/
theorem reconTransfer_corr_decay_gen {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hdom : ∀ k, coeffW w (1 + k) ≤ coeffW w 1) (M n : Nat) :
    corr (reconTransfer w hw0 M) n ≤ (Q'.ofNat M * rho w) * (rho w) ^ n := by
  have hid : (corr (reconTransfer w hw0 M) n).eqv (connSum w M n) :=
    reconTransfer_corr_eq_connSum w hw0 M n
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) ?_
  refine Q'.le_trans' _ _ _ (connSum_le_gen hw0 hdom M n) ?_
  refine Q'.le_of_eqv ?_
  show (Q'.ofNat M * (rho w) ^ (n + 1)).eqv ((Q'.ofNat M * rho w) * (rho w) ^ n)
  rw [Q'.pow_succ]
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat M) (rho w) ((rho w) ^ n))

/-! ## 3. THE CONSTRUCTION — the located gap on the FULL character window. -/

/-- **`reconTransfer_located_gap_gen` — the reconstructed located gap at ANY character-
window weight (NEW, PROVED).**

For every `w` with `0 < w`, `w ≤ 1`, the genuine clustering-rate condition
`rho w < 1` (`⟺ w < 2^{−1/3}`), and the quintic side condition `2·w⁵ ≤ 1`, the
reconstructed single-edge transfer operator `reconTransfer w (le_of_lt hwpos) (M+1)`
has a LOCATED spectral gap with separator `sep = rho w = 2w³ < 1`, hence positive
margin `reconMargin w = 1 − 2w³ > 0`.

This REMOVES the `w ≤ 1/2` gate of
`DirectSingleStepReconGap.reconTransfer_located_gap_general`: the correlator-decay
field is `reconTransfer_corr_decay_gen` (built from scratch via the head-domination
`coeffW_excited_le_head_gen`), the rate bound is the hypothesis `hrho1`, the excited-
weight positivity is `coeffW_pos`.  The ONLY binding constraint is `rho w < 1`. -/
def reconTransfer_located_gap_gen {w : Q'} (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (hrho1 : rho w < (1 : Q')) (hquint : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q')) (M : Nat) :
    LocatedSpectralGap (reconTransfer w (Q'.le_of_lt hwpos) (M + 1)) := by
  have hw0 : (0 : Q') ≤ w := Q'.le_of_lt hwpos
  have hdom : ∀ k, coeffW w (1 + k) ≤ coeffW w 1 :=
    coeffW_excited_le_head_gen hw0 hw1 hquint
  have hrho_pos : (0 : Q') < rho w := by
    show (0 : Q') < coeffW w 1
    have := coeffW_pos hwpos 0
    simpa using this
  have hC : (0 : Q') < Q'.ofNat (M + 1) * rho w :=
    Q'.mul_pos (Q'.ofNat_succ_pos M) hrho_pos
  refine clustering_implies_located (reconTransfer w hw0 (M + 1))
    (Q'.ofNat (M + 1) * rho w) (rho w)
    hC hrho_pos hrho1 ?_ ?_ ?_
  · intro n
    exact reconTransfer_corr_decay_gen hw0 hdom (M + 1) n
  · intro i _
    show (0 : Q') < coeffW w (i + 1)
    exact coeffW_pos hwpos i
  · intro i _
    show coeffW w (i + 1) ≤ rho w
    show coeffW w (i + 1) ≤ coeffW w 1
    have hidx : (i + 1 : Nat) = 1 + i := by omega
    rw [hidx]
    exact hdom i

/-- The general located gap's margin IS `reconMargin w = 1 − rho w` (definitional:
`clustering_implies_located` sets `sep := rho w`, and `gapMargin = 1 − sep`). -/
theorem reconTransfer_located_gap_gen_margin {w : Q'} (hwpos : (0 : Q') < w)
    (hw1 : w ≤ (1 : Q')) (hrho1 : rho w < (1 : Q'))
    (hquint : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q')) (M : Nat) :
    (reconTransfer_located_gap_gen hwpos hw1 hrho1 hquint M).gapMargin = reconMargin w :=
  rfl

/-! ## 4. THE PUSHED EDGE — the concrete instance at `w₀ = 793/1000 = 0.793`.

`w₀ = 793/1000` is a clean rational a distance `≈ 7×10⁻⁴` BELOW the ceiling
`2^{−1/3} = 0.79370…`.  The three side conditions are decidable concrete-rational facts:

  * `rho w₀ = 2·(793/1000)³ = 498677257/500000000 ≈ 0.99735 < 1`  (so the located gap
    exists), and
  * `2·(793/1000)⁵ = 313592694387193/500000000000000 ≈ 0.62719 ≤ 1`  (the quintic side
    condition), with `reconMargin w₀ = 1 − rho w₀ = 1322743/500000000 ≈ 0.00265 > 0`. -/

/-- The PUSHED upper edge `w₀ = 793/1000 = 0.793`, distance `≈ 7×10⁻⁴` below the
ceiling `2^{−1/3} ≈ 0.7937`.  The old located-gap gate was `1/2 = 0.5`. -/
def w0 : Q' := Q'.mkPos 793 1000 (by decide)

theorem w0_pos : (0 : Q') < w0 := by decide

/-- **The genuine push:** `1/2 < w₀ = 793/1000` — the new located-gap edge is strictly
above the old strong-coupling gate `1/2`. -/
theorem w0_gt_half : Q'.mkPos 1 2 (by decide) < w0 := by decide

theorem w0_le_one : w0 ≤ (1 : Q') := by decide

/-- The clustering-rate condition at `w₀`: `rho w₀ = 2·(793/1000)³ < 1` (decidable). -/
theorem w0_rho_lt_one : rho w0 < (1 : Q') := by
  show coeffW w0 1 < (1 : Q')
  decide

/-- The quintic side condition at `w₀`: `2·(793/1000)⁵ ≤ 1` (decidable). -/
theorem w0_quint : Q'.ofNat 2 * qpow w0 5 ≤ (1 : Q') := by decide

/-- **`reconTransfer_located_gap_pushed` — the PUSHED located gap `w₀ = 0.793`
(PROVED).**  The reconstructed single-edge transfer operator has a located spectral gap
at `w₀ = 793/1000`, discharged from `reconTransfer_located_gap_gen` with the three
decidable side conditions.  This pushes the proved located-gap window's upper edge from
`1/2 = 0.5` to `0.793` — within `7×10⁻⁴` of the character radius `2^{−1/3}`. -/
def reconTransfer_located_gap_pushed (M : Nat) :
    LocatedSpectralGap (reconTransfer w0 (Q'.le_of_lt w0_pos) (M + 1)) :=
  reconTransfer_located_gap_gen w0_pos w0_le_one w0_rho_lt_one w0_quint M

/-- The pushed located gap's separator is the genuine Wilson rate `rho w₀ = 2·(793/1000)³`
(definitional). -/
theorem reconTransfer_located_gap_pushed_sep (M : Nat) :
    (reconTransfer_located_gap_pushed M).sep = rho w0 := rfl

/-- The pushed located gap's margin is `reconMargin w₀ = 1 − 2·(793/1000)³` (definitional). -/
theorem reconTransfer_located_gap_pushed_margin (M : Nat) :
    (reconTransfer_located_gap_pushed M).gapMargin = reconMargin w0 := rfl

/-- **`reconMargin_w0_pos` — the pushed margin is strictly positive (PROVED via the
located gap).**  `0 < reconMargin w₀ = 1 − rho w₀`, obtained as the `gapMargin_pos` of
the genuinely-constructed pushed located gap.  The reconstructed transfer margin IS a
positive located mass gap at `w₀ = 0.793`, up from the old `w ≤ 0.5` window. -/
theorem reconMargin_w0_pos : (0 : Q') < reconMargin w0 := by
  have h := (reconTransfer_located_gap_pushed 0).gapMargin_pos
  rwa [reconTransfer_located_gap_pushed_margin 0] at h

/-! ## 5. THE SHARP CEILING — no located gap at or above `w* = 2^{−1/3}`.

For `w³ ≥ 1/2` (i.e. `w ≥ 2^{−1/3}`) the single-edge rate is `rho w = 2w³ ≥ 1`, so NO
located gap of the reconstructed transfer operator exists.  Sharpens
`DirectSingleStepReconGap.no_located_gap_at_weak` (a single witness at `9/10`) to the
EXACT threshold `w³ = 1/2`. -/

/-- **`no_located_gap_above_ceiling` — the sharp ceiling (PROVED).**  For EVERY `w ≥ 0`
with `w³ ≥ 1/2` (i.e. `w ≥ 2^{−1/3}`), the reconstructed single-edge transfer operator
`reconTransfer w hw0 (M+1)` has NO `LocatedSpectralGap`: any such gap forces its leading
excited eigenvalue `lam 0 = rho w = 2w³ ≤ sep < 1`, contradicting `rho w ≥ 1`
(`CharacterWindowCeiling.character_rate_ge_one_at_ceiling`).  A hard impossibility,
holding at the exact character radius, not merely at the far witness `9/10`. -/
theorem no_located_gap_above_ceiling {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hceil : Q'.mkPos 1 2 (by decide) ≤ qpow w 3) (M : Nat) :
    LocatedSpectralGap (reconTransfer w hw0 (M + 1)) → False := by
  intro g
  have hb : (reconTransfer w hw0 (M + 1)).lam 0 ≤ g.sep := g.bound 0
  have hlam : (reconTransfer w hw0 (M + 1)).lam 0 = rho w := rfl
  rw [hlam] at hb
  have hge : (1 : Q') ≤ rho w :=
    CharacterWindowCeiling.character_rate_ge_one_at_ceiling hceil
  have hlt : rho w < (1 : Q') := Q'.lt_of_le_of_lt hb g.sep_lt_one
  have hbad : (1 : Q') < (1 : Q') := Q'.lt_of_le_of_lt hge hlt
  exact Int.lt_irrefl _ hbad

/-- **`reconMargin_neg_at_ceiling_witness` — the margin inverts just past the ceiling.**
At `w = 4/5 = 0.8 > 2^{−1/3}`, `(4/5)³ = 64/125 ≥ 1/2`, so `reconMargin (4/5) =
1 − 2·(4/5)³ = 1 − 128/125 = −3/125 < 0` — the single-edge margin is NOT a positive
physical margin at the deep-UV scale (decidable). -/
theorem reconMargin_neg_at_ceiling_witness :
    reconMargin (Q'.mkPos 4 5 (by decide)) < (0 : Q') := by decide

/-- **`no_located_gap_at_ceiling_witness` — a concrete located-gap impossibility exactly
past the ceiling.**  At `w = 4/5` (just above `2^{−1/3}`, `(4/5)³ = 64/125 ≥ 1/2`), the
reconstructed transfer operator has NO located gap.  A tight instance of the ceiling —
much closer than the old `9/10` witness. -/
theorem no_located_gap_at_ceiling_witness (M : Nat) :
    LocatedSpectralGap
        (reconTransfer (Q'.mkPos 4 5 (by decide)) (by decide) (M + 1)) → False :=
  no_located_gap_above_ceiling (by decide) (by decide) M

/-! ## 6. THE WINDOW IS EXACTLY `[0, 2^{−1/3})` — the precisely-characterized residual.

`reconTransfer_located_gap_gen` supplies a positive located margin for EVERY rational
`w` with `rho w < 1` (`⟺ w³ < 1/2`, `⟺ w < 2^{−1/3}`) in `(0,1]` with `2w⁵ ≤ 1`, and
`no_located_gap_above_ceiling` KILLS the located gap for EVERY `w` with `w³ ≥ 1/2`
(`⟺ w ≥ 2^{−1/3}`).  So the single-edge located-gap window is EXACTLY `[0, 2^{−1/3})`;
the threshold is the character radius, where `rho = 2w³ = 1`.  The residual blocking
`SingleStepDefectBound` is the deep-UV region `[2^{−1/3}, 1)` — where the AF flow
`w_k → 1` lands — for which a located transfer gap requires the interacting multi-
plaquette effective action, NOT the single-edge character mechanism. -/

/-- **`located_gap_window_sharp` — the located-gap window is EXACTLY `[0, 2^{−1/3})`
(PROVED, packaged).**  For any weight `w` in `(0,1]` with `2w⁵ ≤ 1`:

  * if `rho w < 1` (`⟺ w < 2^{−1/3}`) then the reconstructed transfer operator HAS a
    located gap with positive margin `reconMargin w > 0` (`reconTransfer_located_gap_gen`
    / `gapMargin_pos`); and
  * if `w³ ≥ 1/2` (`⟺ w ≥ 2^{−1/3}`) then it has NO located gap
    (`no_located_gap_above_ceiling`).

The dividing weight is the character radius `w* = 2^{−1/3}`, `rho w* = 1`.  This is the
precise, sharp characterization of exactly where the single-edge construction stops. -/
theorem located_gap_window_sharp {w : Q'} (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (hquint : Q'.ofNat 2 * qpow w 5 ≤ (1 : Q')) :
    (rho w < (1 : Q') → (0 : Q') < reconMargin w)
    ∧ (Q'.mkPos 1 2 (by decide) ≤ qpow w 3 →
      ∀ M, LocatedSpectralGap (reconTransfer w (Q'.le_of_lt hwpos) (M + 1)) → False) := by
  refine ⟨?_, ?_⟩
  · intro hrho1
    have h := (reconTransfer_located_gap_gen hwpos hw1 hrho1 hquint 0).gapMargin_pos
    rwa [reconTransfer_located_gap_gen_margin hwpos hw1 hrho1 hquint 0] at h
  · intro hceil M
    exact no_located_gap_above_ceiling (Q'.le_of_lt hwpos) hceil M

end YMGap.Continuum.PushedReconTransferGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.PushedReconTransferGap.coeffW_succ_le_self_gen
#print axioms YMGap.Continuum.PushedReconTransferGap.coeffW_excited_le_head_gen
#print axioms YMGap.Continuum.PushedReconTransferGap.connSum_le_gen
#print axioms YMGap.Continuum.PushedReconTransferGap.reconTransfer_corr_decay_gen
#print axioms YMGap.Continuum.PushedReconTransferGap.reconTransfer_located_gap_gen
#print axioms YMGap.Continuum.PushedReconTransferGap.reconTransfer_located_gap_gen_margin
#print axioms YMGap.Continuum.PushedReconTransferGap.reconTransfer_located_gap_pushed
#print axioms YMGap.Continuum.PushedReconTransferGap.reconMargin_w0_pos
#print axioms YMGap.Continuum.PushedReconTransferGap.no_located_gap_above_ceiling
#print axioms YMGap.Continuum.PushedReconTransferGap.reconMargin_neg_at_ceiling_witness
#print axioms YMGap.Continuum.PushedReconTransferGap.no_located_gap_at_ceiling_witness
#print axioms YMGap.Continuum.PushedReconTransferGap.located_gap_window_sharp
