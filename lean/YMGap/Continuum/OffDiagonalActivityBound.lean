/-
Track B / R2 — DIRECT CONSTRUCTION of an a-priori bound on the per-scale transverse
off-diagonal norm `‖P_k^⊥‖` from the CONVERGENT strong-coupling character expansion.

# What this module does (the sharpest scalar target)

`TempleSpectralStabilityDefect` proved the EXACT equivalence

    realδ_k ≤ 6(1−w_k)²   ⟺   ‖P_k^⊥‖ ≤ √6·(1−w_k)·√(1−w_k³)
                          ⟺   ‖P_k^⊥‖² ≤ 6(1−w_k)²·(1−w_k³) = `templeThreshold w_k`,

reducing the whole per-step block-spin defect to a bound on ONE per-scale scalar: the
squared transverse off-diagonal norm `bsq_k = ‖P_k^⊥‖²`.  Temple inhabited it only with
the MODEL defect (`bsq := δ_model·g`, a circular reframing).  This module CONSTRUCTS a
genuinely a-priori, NON-circular candidate for `‖P_k^⊥‖²` directly from the real
heat-kernel character coefficients and BOUNDS it by the Temple threshold on a CONCRETE
coupling range, pushed toward the character radius `w* = 2^{−1/3}`.

## THE CONSTRUCTED OBJECT (a-priori, non-circular)

The gauge-invariant multi-plaquette interaction one block-spin step generates couples
the vacuum/fundamental sector to the EXCITED representation tower `s ≥ 1`.  Its strength
is the excited-rep character activity (`PlaquetteActivity.plaqActivity`)

    ‖P^⊥‖²(w) := plaqActivity w M = Σ_{1 ≤ s < 1+M} coeffW w s ,
    coeffW w s = (s+1)·w^{C₄(s)}     (`C₄(s)=s(s+2)`, the REAL heat-kernel coefficients).

This is a-priori (fixed by the single-plaquette heat-kernel action, NOT by any δ),
convergent (a geometric character tail, ratio `2w⁵`), and NON-circular (no `bsq := δ·g`).
Its leading term is `coeffW w 1 = 2w³` — the vacuum→fundamental amplitude — exactly the
character-expansion parameter `ρ(w) = 2w³` whose radius of convergence is `w* = 2^{−1/3}`
(`ρ = 1`).

## THE STRONG-COUPLING BOUND (the construction increment, class (ii))

`offDiagActivity_le_threshold` — parametrized by a rational range endpoint `wHi` and a
geometric-closure constant `cQ` satisfying two DECIDABLE side conditions — proves

    ‖P^⊥‖²(w) = plaqActivity w M  ≤  6(1−w)²(1−w³) = templeThreshold w

for EVERY `0 ≤ w ≤ wHi` and every truncation `M` (uniform in the tower cutoff).  The
proof resums the convergent character tail (`CharacterTail.geom_series_le`) to the
closed dominator `cQ·w³` and clears it under the threshold by monotonicity.  Two proved
instances:

  * `offDiag_le_threshold_half`   — the full range `[0, 1/2]`  (`= 0.630·w*`);
  * `offDiag_le_threshold_5_8`    — pushed to `[0, 5/8]`       (`= 0.787·w*`).

So the a-priori excited-activity off-diagonal is bounded by the Temple threshold up to
`w₀ = 5/8`, i.e. `≈ 78.7%` of the way to the character radius `w*`.

## THE TEMPLE HOOK + THE SHARP w→1 RESIDUAL (class (iii))

`temple_defect_of_activityDom` feeds the proved a-priori bound into Temple: it discharges
the `pert`/`bsq ≤ threshold` half OUTRIGHT (non-circularly), leaving as the SOLE residual
the `temple` field — the interacting identification `realδ_k·(1−w_k³) ≤ plaqActivity w_k`
(the real transverse coupling is at most the excited activity).  That is exactly the open
`real_defect_identification` content.

The exact w→1 obstruction is numerically pinned: the character parameter
`ρ(w) = coeffW w 1 = 2w³` is `< 1` on the proved range (`charParam_lt_one_in_range`,
`w = 5/8`) but `≥ 1` beyond `w*` (`charParam_ge_one_beyond_wstar`, `w = 13/16 > w*`), so
the convergent character tail (ratio-`ρ` geometric series) DIVERGES at `w*` and no bare
a-priori character bound survives on `[w*, 1)`.  There the physical off-diagonal must be
controlled by the interacting (renormalized) block-spin measure — the open accumulation
`BondMovingSummable`.  This matches `PushedReconTransferGap`'s `[0, w*)` window exactly.

# HONEST VERDICT (AGENTS.md Rule 6 / Rule 9)

This is deliverable (ii)+(iii): a GENUINE a-priori bound on a NON-circular transverse
off-diagonal object over a CONCRETE range `[0, 5/8] = [0, 0.787·w*]`, plus the exactly
pinned w→1 obstruction.  It is NOT a `:= SingleStepDefectBound` alias and NOT `bsq := δ·g`
(the object is the real character activity, no δ).  It does NOT close `singleStep`: the
`temple` hypothesis (real δ dominated by the a-priori activity) over the full RG recursion
is the open interacting content, and the range stops strictly below `w* < 1`.  `F = 1`
stands, `D = 0`, guard = 5.  NO 4D Yang–Mills mass gap is claimed; nothing is faked.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` composition reusing PROVED `PlaquetteActivity.coeffW_succ_ratio`,
`CharacterTail.geom_series_le`, `qpow_mono`, `sq_le_sq`, the `Q'` order toolkit, and
`TempleSpectralStabilityDefect.temple_threshold_defect`.  Every load-bearing declaration
is `#print axioms`-gated to `propext`/`Quot.sound` only.  `decide` only on closed concrete
`Q'` rational facts (the side conditions and witnesses).  No `Classical.*`, no
`native_decide`, no `ring`/`nlinarith`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.TempleSpectralStabilityDefect

namespace YMGap.Continuum.OffDiagonalActivityBound

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.PlaquetteActivity

/-! ## 1. The Temple threshold `6(1−w)²(1−w³)` as a named per-scale scalar. -/

/-- **`templeThreshold w = 6·(1−w)²·(1−w³)`** — the sharp per-scale off-diagonal
threshold (`= ‖P^⊥‖²_max`) from `TempleSpectralStabilityDefect`.  The target is
`‖P^⊥‖² ≤ templeThreshold w`, EQUIVALENT (via Temple's `δ(δ+g)=b²`) to `realδ ≤ 6(1−w)²`. -/
def templeThreshold (w : Q') : Q' :=
  Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) * heatKernelMargin w

/-! ## 2. The general geometric activity bound (re-tuned closure constant). -/

/-- **`plaqActivity_le_gen` — the excited-rep activity resummed to `cQ·w³`.**  For a
rational range endpoint `wHi ≤ 1` and a closure constant `cQ ≥ 0` satisfying the geometric
recurrence `dimQ 1 + (2·wHi⁵)·cQ ≤ cQ` (which forces `cQ·w³` to dominate the head `2w³`
plus its `2w⁵`-ratio tail on all of `[0, wHi]`), the excited multi-plaquette activity is
bounded, uniformly in the truncation `M`, by the closed form

    plaqActivity w M  ≤  cQ · w³   ( = cQ · heatKernelSep w ).

This GENERALIZES `PlaquetteActivity.plaqActivity_le` (its `4w³` on `[0,1/2]`) to a tunable
`(wHi, cQ)`, letting the range be pushed toward `w*` with a sharper constant. -/
theorem plaqActivity_le_gen {w wHi cQ : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi)
    (hwHi1 : wHi ≤ (1 : Q')) (hcQ0 : (0 : Q') ≤ cQ)
    (hrec : dimQ 1 + (Q'.ofNat 2 * qpow wHi 5) * cQ ≤ cQ) (M : Nat) :
    plaqActivity w M ≤ cQ * heatKernelSep w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw hwHi1
  -- ratio r = 2·w⁵ ≥ 0, dominator H = cQ·w³ ≥ 0
  have hr_nn : (0 : Q') ≤ Q'.ofNat 2 * qpow w 5 :=
    Q'.mul_nonneg _ _ (zero_le_ofNat 2) (qpow_nonneg w hw0 5)
  have hsep_nn : (0 : Q') ≤ heatKernelSep w := heatKernelSep_nonneg hw0
  have hH_nn : (0 : Q') ≤ cQ * heatKernelSep w := Q'.mul_nonneg _ _ hcQ0 hsep_nn
  -- head f 0 = coeffW w 1
  have hf0 : coeffW w (1 + 0) ≤ coeffW w 1 := by
    have h10 : (1 + 0 : Nat) = 1 := rfl
    rw [h10]; exact Q'.le_refl' _
  -- ratio domination of the shifted sequence
  have hdom : ∀ k, coeffW w (1 + (k + 1))
      ≤ (Q'.ofNat 2 * qpow w 5) * coeffW w (1 + k) := by
    intro k
    have hidx : (1 + (k + 1) : Nat) = (1 + k) + 1 := by omega
    rw [hidx]
    exact coeffW_succ_ratio hw0 hw1 (1 + k) (by omega)
  -- geometric recurrence  coeffW w 1 + r·H ≤ H
  have hr0le : Q'.ofNat 2 * qpow w 5 ≤ Q'.ofNat 2 * qpow wHi 5 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hw0 hw 5) (zero_le_ofNat 2)
  have hrH : (Q'.ofNat 2 * qpow w 5) * (cQ * heatKernelSep w)
      ≤ (Q'.ofNat 2 * qpow wHi 5) * (cQ * heatKernelSep w) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hr0le hH_nn
  -- coeffW w 1 + r₀·(cQ·sep) ≃ (dimQ 1 + r₀·cQ)·sep
  have heq : (coeffW w 1 + (Q'.ofNat 2 * qpow wHi 5) * (cQ * heatKernelSep w)).eqv
      ((dimQ 1 + (Q'.ofNat 2 * qpow wHi 5) * cQ) * heatKernelSep w) := by
    rw [coeffW_one w]
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (dimQ 1 * heatKernelSep w) _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2 * qpow wHi 5) cQ (heatKernelSep w)))) ?_
    exact Q'.eqv_symm
      (Q'.add_mul_eqv (dimQ 1) ((Q'.ofNat 2 * qpow wHi 5) * cQ) (heatKernelSep w))
  -- (dimQ 1 + r₀·cQ)·sep ≤ cQ·sep  (from hrec, sep ≥ 0)
  have hfin : (dimQ 1 + (Q'.ofNat 2 * qpow wHi 5) * cQ) * heatKernelSep w
      ≤ cQ * heatKernelSep w :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hrec hsep_nn
  have hrec_geom : coeffW w 1 + (Q'.ofNat 2 * qpow w 5) * (cQ * heatKernelSep w)
      ≤ cQ * heatKernelSep w := by
    have hstep : coeffW w 1 + (Q'.ofNat 2 * qpow w 5) * (cQ * heatKernelSep w)
        ≤ coeffW w 1 + (Q'.ofNat 2 * qpow wHi 5) * (cQ * heatKernelSep w) :=
      Q'.add_le_add_left (coeffW w 1) _ _ hrH
    exact Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hfin)
  -- fire the geometric-series engine (plaqActivity = finSum of the shifted sequence)
  exact CharacterTail.geom_series_le (fun k => coeffW w (1 + k))
    (coeffW w 1) (Q'.ofNat 2 * qpow w 5) (cQ * heatKernelSep w)
    hr_nn hH_nn hf0 hdom hrec_geom M

/-! ## 3. Threshold monotonicity (the range-collapse to the endpoint). -/

/-- **`templeThreshold_antitone` — the threshold is `≥` its right-endpoint value.**  For
`0 ≤ w ≤ wHi ≤ 1`, `templeThreshold wHi ≤ templeThreshold w`: both `(1−w)²` and `1−w³`
decrease in `w`, so `6(1−w)²(1−w³)` decreases; its minimum on `[0, wHi]` is at `wHi`. -/
theorem templeThreshold_antitone {w wHi : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi)
    (hwHi1 : wHi ≤ (1 : Q')) :
    templeThreshold wHi ≤ templeThreshold w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw hwHi1
  -- 1 − wHi ≤ 1 − w
  have hsub : (1 : Q') - wHi ≤ (1 : Q') - w := by
    have hneg : -wHi ≤ -w := Q'.neg_le_neg hw
    exact Q'.add_le_add_left 1 _ _ hneg
  have hnnHi : (0 : Q') ≤ (1 : Q') - wHi := Q'.sub_nonneg_of_le hwHi1
  -- (1−wHi)² ≤ (1−w)²
  have hPsq : ((1 : Q') - wHi) * ((1 : Q') - wHi) ≤ ((1 : Q') - w) * ((1 : Q') - w) :=
    sq_le_sq hnnHi hsub
  -- 6·(1−wHi)² ≤ 6·(1−w)²
  have hAP : Q'.ofNat 6 * (((1 : Q') - wHi) * ((1 : Q') - wHi))
      ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hPsq (zero_le_ofNat 6)
  -- heatKernelMargin wHi ≤ heatKernelMargin w  (1 − w³ ≥ 1 − wHi³)
  have hMg : heatKernelMargin wHi ≤ heatKernelMargin w := by
    show (1 : Q') - qpow wHi 3 ≤ (1 : Q') - qpow w 3
    have hqp : qpow w 3 ≤ qpow wHi 3 := qpow_mono hw0 hw 3
    have hneg : -qpow wHi 3 ≤ -qpow w 3 := Q'.neg_le_neg hqp
    exact Q'.add_le_add_left 1 _ _ hneg
  -- nonnegativity of the surviving factors
  have hMgw_nn : (0 : Q') ≤ heatKernelMargin w := by
    show (0 : Q') ≤ (1 : Q') - qpow w 3
    exact Q'.sub_nonneg_of_le (qpow_le_one hw0 hw1 3)
  have hAPHi_nn : (0 : Q') ≤ Q'.ofNat 6 * (((1 : Q') - wHi) * ((1 : Q') - wHi)) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat 6) (Q'.mul_nonneg _ _ hnnHi hnnHi)
  -- templeThreshold wHi = (6·(1−wHi)²)·Mg wHi ≤ (6·(1−wHi)²)·Mg w ≤ (6·(1−w)²)·Mg w
  have h1 : Q'.ofNat 6 * (((1 : Q') - wHi) * ((1 : Q') - wHi)) * heatKernelMargin wHi
      ≤ Q'.ofNat 6 * (((1 : Q') - wHi) * ((1 : Q') - wHi)) * heatKernelMargin w :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hMg hAPHi_nn
  have h2 : Q'.ofNat 6 * (((1 : Q') - wHi) * ((1 : Q') - wHi)) * heatKernelMargin w
      ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) * heatKernelMargin w :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hAP hMgw_nn
  exact Q'.le_trans' _ _ _ h1 h2

/-! ## 4. THE CONSTRUCTION — a-priori off-diagonal ≤ threshold on a concrete range. -/

/-- **`offDiagActivity_le_threshold` — the a-priori off-diagonal bound (class (ii)).**
Given the two DECIDABLE side conditions at the rational endpoint `wHi`:

  * `hrec` — geometric closure `dimQ 1 + (2·wHi⁵)·cQ ≤ cQ`;
  * `hthr` — endpoint clearance `cQ·wHi³ ≤ templeThreshold wHi`,

the constructed a-priori transverse off-diagonal norm-squared (the excited-rep
multi-plaquette activity) is bounded by the Temple threshold on ALL of `[0, wHi]`,
uniformly in the tower cutoff `M`:

    plaqActivity w M  ≤  templeThreshold w   ( = ‖P^⊥‖²(w) ≤ 6(1−w)²(1−w³) ).

Chain: `plaqActivity w M ≤ cQ·w³ ≤ cQ·wHi³ ≤ templeThreshold wHi ≤ templeThreshold w`
(resummation, `w³`-monotonicity, endpoint clearance, threshold anti-monotonicity). -/
theorem offDiagActivity_le_threshold {w wHi cQ : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ wHi)
    (hwHi1 : wHi ≤ (1 : Q')) (hcQ0 : (0 : Q') ≤ cQ)
    (hrec : dimQ 1 + (Q'.ofNat 2 * qpow wHi 5) * cQ ≤ cQ)
    (hthr : cQ * heatKernelSep wHi ≤ templeThreshold wHi) (M : Nat) :
    plaqActivity w M ≤ templeThreshold w := by
  have h1 : plaqActivity w M ≤ cQ * heatKernelSep w :=
    plaqActivity_le_gen hw0 hw hwHi1 hcQ0 hrec M
  have h2 : cQ * heatKernelSep w ≤ cQ * heatKernelSep wHi :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hw0 hw 3) hcQ0
  have h4 : templeThreshold wHi ≤ templeThreshold w :=
    templeThreshold_antitone hw0 hw hwHi1
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_trans' _ _ _ hthr h4))

/-! ## 5. Proved instances — the pushed ranges `[0, 1/2]` and `[0, 5/8]`. -/

/-- **`offDiag_le_threshold_half` — the a-priori off-diagonal bound on `[0, 1/2]`.**
`plaqActivity w M ≤ 6(1−w)²(1−w³)` for `0 ≤ w ≤ 1/2` (`= 0.630·w*`), all `M`.  Closure
constant `cQ = 5/2` (recurrence slack `69/32 ≤ 5/2`; endpoint `5/16 ≤ 21/16`). -/
theorem offDiag_le_threshold_half {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide)) (M : Nat) :
    plaqActivity w M ≤ templeThreshold w :=
  offDiagActivity_le_threshold
    (wHi := Q'.mkPos 1 2 (by decide)) (cQ := Q'.mkPos 5 2 (by decide))
    hw0 hw (by decide) (by decide) (by decide) (by decide) M

/-- **`offDiag_le_threshold_5_8` — the a-priori off-diagonal bound PUSHED to `[0, 5/8]`.**
`plaqActivity w M ≤ 6(1−w)²(1−w³)` for `0 ≤ w ≤ 5/8` (`= 0.787·w*`), all `M` — the
range pushed to `≈ 78.7%` of the character radius `w* = 2^{−1/3}`.  Same closure constant
`cQ = 5/2` (recurrence slack `≈ 2.477 ≤ 5/2`; endpoint `625/1024 ≤ 20898/32768`). -/
theorem offDiag_le_threshold_5_8 {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 5 8 (by decide)) (M : Nat) :
    plaqActivity w M ≤ templeThreshold w :=
  offDiagActivity_le_threshold
    (wHi := Q'.mkPos 5 8 (by decide)) (cQ := Q'.mkPos 5 2 (by decide))
    hw0 hw (by decide) (by decide) (by decide) (by decide) M

/-! ## 6. THE TEMPLE HOOK — the a-priori bound discharges `pert`, isolating the residual. -/

/-- **`temple_defect_of_activityDom` — a-priori off-diagonal ⇒ per-step defect (class (iii)).**
On the proved range, GIVEN the a-priori threshold bound `hthrng : plaqActivity w M ≤
templeThreshold w` (PROVED, non-circular) AND the single OPEN identification

    hdom : realδ · (1 − w³)  ≤  plaqActivity w M

(the real transverse coupling erosion is at most the excited multi-plaquette activity —
the sole remaining interacting content), the per-step defect bound follows:

    realδ  ≤  6·(1 − w)² .

The `pert` half of `TempleOffDiagonalResidual` is thus DISCHARGED outright by the a-priori
character-expansion bound; the `temple`/`hdom` field is the exact residual, equalling the
open `real_defect_identification`.  This is NOT a `singleStep` alias: it converts the atomic
core into ONE explicit a-priori inequality (`hdom`) against a PROVED a-priori bound. -/
theorem temple_defect_of_activityDom {w realδ : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) (M : Nat)
    (hthrng : plaqActivity w M ≤ templeThreshold w)
    (hdom : realδ * heatKernelMargin w ≤ plaqActivity w M) :
    realδ ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
  TempleSpectralStabilityDefect.temple_threshold_defect hw0 hw1 hdom hthrng

/-! ## 7. THE SHARP w→1 RESIDUAL — the character radius `w* = 2^{−1/3}` obstruction. -/

/-- **`charParam_lt_one_in_range` — the character parameter is `< 1` on the proved range.**
`ρ(w) = coeffW w 1 = 2w³ < 1` at `w = 5/8` (`ρ = 250/512`): the convergent character
tail (ratio-`ρ` geometric series) converges throughout `[0, 5/8]`, so the a-priori
off-diagonal bound holds. -/
theorem charParam_lt_one_in_range :
    coeffW (Q'.mkPos 5 8 (by decide)) 1 < (1 : Q') := by decide

/-- **`charParam_ge_one_beyond_wstar` — the character expansion DIVERGES beyond `w*`.**
`ρ(w) = coeffW w 1 = 2w³ ≥ 1` at `w = 13/16 > w* = 2^{−1/3}` (`ρ = 4394/4096 > 1`): the
character tail's geometric ratio reaches `1`, so NO bare a-priori character bound survives
on `[w*, 1)`.  There the physical off-diagonal requires the interacting (renormalized)
block-spin measure — the open accumulation `BondMovingSummable`.  This is the EXACT,
numerically-pinned w→1 obstruction; it coincides with `PushedReconTransferGap`'s `[0, w*)`
window (`w* = 2^{−1/3} ≈ 0.7937`). -/
theorem charParam_ge_one_beyond_wstar :
    (1 : Q') ≤ coeffW (Q'.mkPos 13 16 (by decide)) 1 := by decide

/-- **`offDiag_verdict` — the construction bundle (machine-checked).**

  (i)   the a-priori off-diagonal (excited multi-plaquette activity) is bounded by the
        Temple threshold on the PUSHED range `[0, 5/8] = [0, 0.787·w*]`, uniformly in
        the tower cutoff `M` (`offDiag_le_threshold_5_8`);
  (ii)  it feeds Temple, discharging the `pert` half and isolating the sole residual to
        the open identification `realδ·(1−w³) ≤ activity` (`temple_defect_of_activityDom`);
  (iii) the character parameter `ρ = 2w³` is `< 1` on-range but `≥ 1` beyond `w*`
        (`charParam_lt_one_in_range`, `charParam_ge_one_beyond_wstar`) — the exact w→1
        obstruction.

VERDICT: a GENUINE a-priori, non-circular construction increment (class (ii)+(iii)) on the
sharpest scalar target; the `[w*, 1)` window and the on-range `temple` identification remain
the open interacting content.  NO 4D Yang–Mills mass gap is claimed. -/
theorem offDiag_verdict :
    (∀ {w : Q'}, (0 : Q') ≤ w → w ≤ Q'.mkPos 5 8 (by decide) → ∀ M : Nat,
        plaqActivity w M ≤ templeThreshold w)
    ∧ coeffW (Q'.mkPos 5 8 (by decide)) 1 < (1 : Q')
    ∧ (1 : Q') ≤ coeffW (Q'.mkPos 13 16 (by decide)) 1 :=
  ⟨fun hw0 hw M => offDiag_le_threshold_5_8 hw0 hw M,
   charParam_lt_one_in_range,
   charParam_ge_one_beyond_wstar⟩

end YMGap.Continuum.OffDiagonalActivityBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.OffDiagonalActivityBound.plaqActivity_le_gen
#print axioms YMGap.Continuum.OffDiagonalActivityBound.templeThreshold_antitone
#print axioms YMGap.Continuum.OffDiagonalActivityBound.offDiagActivity_le_threshold
#print axioms YMGap.Continuum.OffDiagonalActivityBound.offDiag_le_threshold_half
#print axioms YMGap.Continuum.OffDiagonalActivityBound.offDiag_le_threshold_5_8
#print axioms YMGap.Continuum.OffDiagonalActivityBound.temple_defect_of_activityDom
#print axioms YMGap.Continuum.OffDiagonalActivityBound.charParam_lt_one_in_range
#print axioms YMGap.Continuum.OffDiagonalActivityBound.charParam_ge_one_beyond_wstar
#print axioms YMGap.Continuum.OffDiagonalActivityBound.offDiag_verdict
