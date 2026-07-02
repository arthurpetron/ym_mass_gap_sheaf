/-
Track A / R2 (track: 1-worstcase) — factoring `FiniteSMarginWorstcase w` through ONE cross-ratio
inequality (★), the `w²`-monotonicity of the per-mode margin ratio.

# What this module adds (all axiom-clean)

`LaplaceMarginDeep.FiniteSMarginWorstcase w` is the ANALYTIC content of `FiniteSMargin` — the
`w`-monotonicity reduction collapsing the two-parameter `(w,s)` family to the one-parameter wH
sequence.  Here we DISCHARGE its entire `w`-dependence algebraically, reducing it to exactly ONE
named inequality per mode:

    (★)  A_s(w)·M_s(wH)  ≤  A_s(wH)·M_s(w)          (`CrossRatioMonotone`)

where, per mode `s`,

    A_s(w)  := acN w (s+1) s · acN w (s+1) (s+2)          ("off-diagonal antidiagonal product")
    M_s(w)  := acN w (s+1) (s+1) · acN w (s+1) (s+1)      ("diagonal square")

(★) is the cross-multiplied "increasing-ratio" statement `A_s(w)/M_s(w)` nondecreasing in `w` on
`[0, wH]`.  Given (★), a wH-margin `40000·A_s(wH) ≤ 22801·M_s(wH)` implies the `w`-margin
`40000·A_s(w) ≤ 22801·M_s(w)` by a 3-step positive cancellation:

    40000·(A_w·M_wH) ≤ 40000·(A_wH·M_w) = (40000·A_wH)·M_w
                     ≤ (22801·M_wH)·M_w = (22801·M_w)·M_wH,

and `40000·(A_w·M_wH) = (40000·A_w)·M_wH`, so cancel the strictly-positive `M_wH` (>0).

# What is PROVED here (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `acN_pos_diag_wH` — the diagonal instance `0 < acN wH (s+1) (s+1)` (the `p=0` term
    `coeffW wH 0 · coeffW wH (s+1) > 0` dominates the nonnegative fsum tail).
  * `crossRatioMonotoneToWorstcase` — the 3-step positive-cancellation reduction
    `CrossRatioMonotone w → FiniteSMarginWorstcase w` (with `0 ≤ w`).
  * `finiteSMarginOfCrossRatio` — the final wiring: `CrossRatioMonotone w` + `WHAllSMargin`
    ⟹ `AcNReserveAnalytic.FiniteSMargin w`.

# The honest wall

`CrossRatioMonotone w` (= (★)) is NOT free.  Its standard sufficient condition is the
coefficient-ratio monotonicity (total positivity / Newton log-concavity) of the two nonneg
polynomials `A_w = Σ aₖ wᵏ`, `M_w = Σ bₖ wᵏ`.  The proved atom `coeffW_superLogConcave_wsq`
supplies the per-mode `k`-local monotone step, but the uniform-in-`s` closure of (★) is the genuine
theta / local-CLT wall.  So (★) is the correctly-located restatement of that wall — the sharpest
reduction available, not an escape from it.  NAMED-OPEN (never `sorry`).
-/

import YMGap.Continuum.LaplaceMarginDeep
import YMGap.Continuum.BakryEmery
import YMGap.Continuum.BondMovingMoment

namespace YMGap.Continuum.FiniteSMarginWorstcase

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.LaplaceMarginDeep

/-! ## 1. The single named residual (★): the `w²`-monotonicity of the margin ratio. -/

/-- **(★) `CrossRatioMonotone w`** — the margin ratio `A_s(w)/M_s(w)` is nondecreasing in `w` on
`[0, wH]`, in cross-multiplied "increasing-ratio" form, per mode `s`:

    A_s(w)·M_s(wH)  ≤  A_s(wH)·M_s(w),

i.e. `(acN w (s+1) s · acN w (s+1)(s+2)) · (acN wH (s+1)(s+1))²
        ≤ (acN wH (s+1) s · acN wH (s+1)(s+2)) · (acN w (s+1)(s+1))²`.
NAMED-OPEN (never `sorry`): the uniform-in-`s` theta / local-CLT wall. -/
structure CrossRatioMonotone (w : Q') : Type where
  cross : ∀ s,
    (acN w  (s+1) s * acN w  (s+1) (s+2)) * (acN wH (s+1) (s+1) * acN wH (s+1) (s+1))
      ≤ (acN wH (s+1) s * acN wH (s+1) (s+2)) * (acN w (s+1) (s+1) * acN w (s+1) (s+1))

/-! ## 2. Positivity helper: the diagonal `0 < acN wH (s+1) (s+1)`. -/

/-- **`acN_pos_diag_wH`** — the diagonal autoconvolution at the worst case `w = wH` is strictly
positive.  `acN wH (s+1) (s+1) = Σ_{p<s+1} c_p·c_{(s+1)−p}` with all summands `≥ 0` and the `p=0`
summand `c_0·c_{s+1} > 0` (`coeffW_pos` twice, `BakryEmery.mul_pos`), so the fsum dominates a
strictly positive term. -/
theorem acN_pos_diag_wH (s : Nat) : (0 : Q') < acN wH (s + 1) (s + 1) := by
  have hwpos : (0 : Q') < wH := by decide
  have hnn : ∀ t, (0 : Q') ≤ coeffW wH t * coeffW wH ((s + 1) - t) := fun t =>
    Q'.mul_nonneg _ _ (coeffW_nonneg (Q'.le_of_lt hwpos) t)
      (coeffW_nonneg (Q'.le_of_lt hwpos) ((s + 1) - t))
  have hterm : (coeffW wH 0 * coeffW wH ((s + 1) - 0))
      ≤ fsum (fun p => coeffW wH p * coeffW wH ((s + 1) - p)) (s + 1) :=
    fsum_term_le_of_nonneg hnn 0 (s + 1) (Nat.succ_pos s)
  have h0 : (0 : Q') < coeffW wH 0 * coeffW wH ((s + 1) - 0) :=
    BakryEmery.mul_pos (coeffW_pos hwpos 0) (coeffW_pos hwpos ((s + 1) - 0))
  exact HeatKernelRGStep.lt_of_lt_of_le h0 hterm

/-! ## 3. The pure-`Q'` 3-step positive-cancellation core. -/

/-- **`cancel3`** — the algebraic engine.  From the cross-ratio inequality `A_w·M_wH ≤ A_wH·M_w`,
the wH margin `40000·A_wH ≤ 22801·M_wH`, `0 ≤ M_w` and `0 < M_wH`, conclude the `w` margin
`40000·A_w ≤ 22801·M_w` by three positive multiplications plus one strictly-positive right-cancel.
-/
theorem cancel3 {Aw AwH Mw MwH : Q'}
    (hMw : (0 : Q') ≤ Mw) (hMwH : (0 : Q') < MwH)
    (hcross : Aw * MwH ≤ AwH * Mw)
    (hwH : Q'.ofNat 40000 * AwH ≤ Q'.ofNat 22801 * MwH) :
    Q'.ofNat 40000 * Aw ≤ Q'.ofNat 22801 * Mw := by
  -- Step 1: scale the cross-ratio by 40000 on the left.
  have s1 : Q'.ofNat 40000 * (Aw * MwH) ≤ Q'.ofNat 40000 * (AwH * Mw) :=
    Q'.mul_le_mul_of_nonneg_left (Aw * MwH) (AwH * Mw) (Q'.ofNat 40000) hcross (by decide)
  -- Step 2: scale the wH margin by Mw on the right.
  have s2 : (Q'.ofNat 40000 * AwH) * Mw ≤ (Q'.ofNat 22801 * MwH) * Mw :=
    Q'.mul_le_mul_of_nonneg_right (Q'.ofNat 40000 * AwH) (Q'.ofNat 22801 * MwH) Mw hwH hMw
  -- reassoc: 40000·(A_wH·M_w) ≃ (40000·A_wH)·M_w
  have e2a : (Q'.ofNat 40000 * (AwH * Mw)).eqv ((Q'.ofNat 40000 * AwH) * Mw) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) AwH Mw)
  -- reassoc: (22801·M_wH)·M_w ≃ 22801·(M_wH·M_w) ≃ 22801·(M_w·M_wH) ≃ (22801·M_w)·M_wH
  have e2b : ((Q'.ofNat 22801 * MwH) * Mw).eqv ((Q'.ofNat 22801 * Mw) * MwH) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 22801) MwH Mw) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 22801) (MwH * Mw) (Mw * MwH) (Q'.mul_comm_eqv MwH Mw)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 22801) Mw MwH)
  -- chain: 40000·(A_w·M_wH) ≤ (22801·M_w)·M_wH
  have chain : Q'.ofNat 40000 * (Aw * MwH) ≤ (Q'.ofNat 22801 * Mw) * MwH :=
    Q'.le_trans' _ _ _ s1
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv e2a)
        (Q'.le_trans' _ _ _ s2 (Q'.le_of_eqv e2b)))
  -- reassoc: 40000·(A_w·M_wH) ≃ (40000·A_w)·M_wH
  have e1 : (Q'.ofNat 40000 * (Aw * MwH)).eqv ((Q'.ofNat 40000 * Aw) * MwH) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) Aw MwH)
  have chain2 : (Q'.ofNat 40000 * Aw) * MwH ≤ (Q'.ofNat 22801 * Mw) * MwH :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv e1) chain
  -- cancel the strictly-positive right factor M_wH
  exact BakryEmery.le_of_mul_le_mul_right_pos hMwH chain2

/-! ## 4. The reduction: (★) ⟹ `FiniteSMarginWorstcase w`. -/

/-- **`crossRatioMonotoneToWorstcase` — THE REDUCTION.**  A cross-ratio witness `CrossRatioMonotone
w` (with `0 ≤ w`) inhabits `LaplaceMarginDeep.FiniteSMarginWorstcase w`: for each mode `s`, the
wH-margin is turned into the `w`-margin by `cancel3`, using `star.cross s` for the cross-ratio,
`acN_nonneg` for `0 ≤ M_w`, and `acN_pos_diag_wH` (×`BakryEmery.mul_pos`) for `0 < M_wH`.  This
discharges the ENTIRE `w`-dependence algebraically, leaving exactly (★). -/
def crossRatioMonotoneToWorstcase {w : Q'} (hw0 : (0 : Q') ≤ w) (_hwWH : w ≤ wH)
    (star : CrossRatioMonotone w) : FiniteSMarginWorstcase w where
  reduce := fun s hwH => by
    have hMw : (0 : Q') ≤ acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1) :=
      Q'.mul_nonneg _ _ (acN_nonneg hw0 _ _) (acN_nonneg hw0 _ _)
    have hMwH : (0 : Q') < acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1) :=
      BakryEmery.mul_pos (acN_pos_diag_wH s) (acN_pos_diag_wH s)
    exact cancel3 hMw hMwH (star.cross s) hwH

/-! ## 5. Final wiring: (★) + `WHAllSMargin` ⟹ `FiniteSMargin`. -/

/-- **`finiteSMarginOfCrossRatio` — end-to-end.**  Composed with the existing
`finiteSMarginOfWorstcase`, a cross-ratio witness `CrossRatioMonotone w` (with `0 ≤ w ≤ wH`) and the
wH rational tail `WHAllSMargin` together inhabit `AcNReserveAnalytic.FiniteSMargin w`.  This
collapses the two-parameter `(w,s)` family to the single wH sequence, with the `w`-dependence
discharged and the sole residual factored into (★). -/
def finiteSMarginOfCrossRatio {w : Q'} (hw0 : (0 : Q') ≤ w) (hwWH : w ≤ wH)
    (star : CrossRatioMonotone w) (m : WHAllSMargin) : FiniteSMargin w :=
  finiteSMarginOfWorstcase (crossRatioMonotoneToWorstcase hw0 hwWH star) m

end YMGap.Continuum.FiniteSMarginWorstcase

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FiniteSMarginWorstcase.acN_pos_diag_wH
#print axioms YMGap.Continuum.FiniteSMarginWorstcase.cancel3
#print axioms YMGap.Continuum.FiniteSMarginWorstcase.crossRatioMonotoneToWorstcase
#print axioms YMGap.Continuum.FiniteSMarginWorstcase.finiteSMarginOfCrossRatio
