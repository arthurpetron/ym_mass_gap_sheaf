/-
Track A / R2 (track: 1-saddle) — CLOSING the one-sided windowed saddle floor `SaddleFloor` at the
worst coupling `w = wH = 1/2`, and re-pointing the general-`w` residual to the coefficient-array
`w`-monotone reduction `FiniteSMarginWorstcase`.

# What this module settles (read first — load-bearing honesty)

`AdjacentMLR.SaddleFloor w` is the one-sided Gaussian-saddle log-concavity floor in `ρ`-form,

    acN w (s+1) s · acN w (s+1) (s+2)  ≤  ρ · (acN w (s+1) (s+1) · acN w (s+1) (s+1)),
        ρ = rhoFloor = 22801/40000 ≈ 0.57025,   for every mode `s`.

Upstream it was left NAMED-OPEN, with only the FORWARD bridge proved
(`AdjacentMLR.finiteSMargin_of_saddleFloor : SaddleFloor w → FiniteSMargin w`, via `clearDenom`).
This module supplies the CONVERSE positive rescale and closes the worst case:

  * `rescaleDenom` — the pure-`Q'` CONVERSE bridge `40000·A ≤ 22801·B  ⟹  A ≤ ρ·B` (rescale by the
    positive factor `40000` and cancel; `40000·ρ ≃ 22801`).  Together with the in-tree `clearDenom`
    this gives `SaddleFloor w ⟺ FiniteSMargin w` — `SaddleFloor` is exactly a `ρ`-form wrapper of
    `AcNReserveAnalytic.FiniteSMargin`.
  * `saddleFloor_of_finiteSMargin` — the CONVERSE reduction `FiniteSMargin w → SaddleFloor w`.
  * `finiteSMarginWorstcase_wH` — at the worst case the `w`-monotone reduction
    `LaplaceMarginDeep.FiniteSMarginWorstcase wH` is inhabited by the IDENTITY (`reduce s = id`,
    since the target `w`-margin at `w = wH` is definitionally the source `wH`-margin).
  * `finiteSMargin_wH` — `AcNReserveAnalytic.FiniteSMargin wH`, obtained from the PROVED
    `WHTailCeilingsClose.whAllSMargin` (the two closed full-window θ-envelope ceilings) fed through
    `LaplaceMarginDeep.finiteSMarginOfWorstcase` with the identity worst-case witness.
  * `saddleFloor_wH` — **`AdjacentMLR.SaddleFloor wH` is CLOSED** (axiom-clean), the previously
    named-open one-sided saddle floor at the worst coupling.
  * `reserve_wH` — end-to-end: composing with `AdjacentMLR.reserveOfSaddleFloor`, the worst-case
    saddle floor yields the full `LeakGeoDecay.AcNDefectReserve wH` from proved inputs.
  * `saddleFloor_of_worstcase` — the general-`w` SHARP REDUCTION: `FiniteSMarginWorstcase w`
    (the `w`-monotone collapse to the wH sequence) is the SOLE remaining input needed for
    `SaddleFloor w` — everything else (the θ tail `whAllSMargin`, both denominator rescales) is
    proved.  This re-points the open node off the saddle/local-CLT estimate (which is closed at wH)
    and onto the coefficient-array TP₂/MLR `w`-monotonicity (`CrossRatioMonotone.ArrayMLR`), whose
    naive pointwise sufficient condition is separately refuted in `AdjacentMLR`.

# HONESTY — what is and is NOT closed

CLOSED here (axiom-clean, `[propext]` / `[propext, Quot.sound]`): `SaddleFloor wH`, hence
`FiniteSMargin wH`, hence `AcNDefectReserve wH` — the whole worst-case reserve chain, from the proved
θ-envelope ceilings.  No steepest-descent / Tate–Zelditch remainder control is needed; the folds are
exact rational algebra capped by the two decidable θ-ceilings `151/100` (even) and `16/15` (odd).

NAMED-OPEN (never `sorry`): `LaplaceMarginDeep.FiniteSMarginWorstcase w` for general `w ≤ wH` — the
`w`-monotone reduction of the two-parameter `(w,s)` margin family to the one-parameter wH sequence.
This is the coefficient-array TP₂ wall (`CrossRatioMonotone.ArrayMLR`), NOT a saddle estimate.  This
module does NOT inhabit it; it only shows it is the sole residual for `SaddleFloor w`.  This is a
structural closure of one box-level log-concavity sub-fact at the worst coupling; it is NOT a 4D
Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, `decide` only on closed concrete-rational facts, the reused `Q'`
order/`eqv` algebra with one positive left-cancellation, and the upstream PROVED
`whAllSMargin`/`finiteSMarginOfWorstcase`/`reserveOfSaddleFloor`.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `propext, Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.AdjacentMLR
import YMGap.Continuum.LaplaceMarginDeep
import YMGap.Continuum.WHTailCeilingsClose

namespace YMGap.Continuum.SaddleFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusionCoreStepRoundA

/-! ## 1. The pure-`Q'` CONVERSE denominator rescale -/

/-- **`rescaleDenom`** — the converse of `AdjacentMLR.clearDenom`.  From the cleared-denominator
margin `40000·A ≤ 22801·B` conclude the `ρ`-form floor `A ≤ ρ·B`, `ρ = 22801/40000`.  Rescale the
goal by the positive factor `40000` (`le_of_mul_le_mul_left_pos`) and use `40000·ρ ≃ 22801`.  No sign
hypothesis on `A`, `B` is needed. -/
theorem rescaleDenom {A B : Q'}
    (h : Q'.ofNat 40000 * A ≤ Q'.ofNat 22801 * B) :
    A ≤ AdjacentMLR.rhoFloor * B := by
  apply FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    (show (0 : Q') < Q'.ofNat 40000 by decide)
  -- goal: 40000·A ≤ 40000·(ρ·B)
  have heqv : (Q'.ofNat 22801 * B).eqv (Q'.ofNat 40000 * (AdjacentMLR.rhoFloor * B)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 22801)
        (Q'.ofNat 40000 * AdjacentMLR.rhoFloor) B (by decide))
      (Q'.mul_assoc_eqv (Q'.ofNat 40000) AdjacentMLR.rhoFloor B)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv heqv)

/-- **`saddleFloor_of_finiteSMargin`** — THE CONVERSE REDUCTION.  A `FiniteSMargin w` witness
inhabits `AdjacentMLR.SaddleFloor w` by the positive rescale `rescaleDenom` at each mode `s`.
Composed with the in-tree `AdjacentMLR.finiteSMargin_of_saddleFloor` this establishes the equivalence
`SaddleFloor w ⟺ FiniteSMargin w`. -/
def saddleFloor_of_finiteSMargin {w : Q'} (H : AcNReserveAnalytic.FiniteSMargin w) :
    AdjacentMLR.SaddleFloor w where
  floor := fun s => rescaleDenom (H.margin s)

/-! ## 2. The worst-case witnesses and the CLOSED `SaddleFloor wH` -/

/-- **`finiteSMarginWorstcase_wH`** — at `w = wH` the `w`-monotone reduction is the IDENTITY: the
target `w`-margin at mode `s` is definitionally the source `wH`-margin, so `reduce s` is `id`. -/
def finiteSMarginWorstcase_wH : LaplaceMarginDeep.FiniteSMarginWorstcase wH where
  reduce := fun _ h => h

/-- **`finiteSMargin_wH`** — `AcNReserveAnalytic.FiniteSMargin wH`, assembled from the PROVED
θ-envelope ceilings `WHTailCeilingsClose.whAllSMargin` fed through
`LaplaceMarginDeep.finiteSMarginOfWorstcase` with the identity worst-case witness. -/
def finiteSMargin_wH : AcNReserveAnalytic.FiniteSMargin wH :=
  LaplaceMarginDeep.finiteSMarginOfWorstcase finiteSMarginWorstcase_wH
    WHTailCeilingsClose.whAllSMargin

/-- **`saddleFloor_wH` — THE CLOSED WORST CASE.**  `AdjacentMLR.SaddleFloor wH` is inhabited: the
one-sided windowed saddle floor `S_s·S_{s+2} ≤ ρ·S_{s+1}²` holds for all `s` at the worst coupling
`w = wH = 1/2`, from the proved θ-envelope ceilings via `finiteSMargin_wH` and the `ρ`-form rescale.
No steepest-descent / local-CLT remainder control is used. -/
def saddleFloor_wH : AdjacentMLR.SaddleFloor wH :=
  saddleFloor_of_finiteSMargin finiteSMargin_wH

/-- **`reserve_wH` — end-to-end at the worst case.**  Composing the closed `saddleFloor_wH` with the
in-tree `AdjacentMLR.reserveOfSaddleFloor` (`0 ≤ wH`) yields the full `LeakGeoDecay.AcNDefectReserve
wH` — the whole autoconvolution log-concavity reserve closes at the worst coupling from proved
inputs. -/
def reserve_wH : LeakGeoDecay.AcNDefectReserve wH :=
  AdjacentMLR.reserveOfSaddleFloor (by decide) saddleFloor_wH

/-! ## 3. The general-`w` SHARP REDUCTION (re-pointing the open node) -/

/-- **`saddleFloor_of_worstcase` — THE SHARP REDUCTION for general `w`.**  Given ONLY the `w`-monotone
worst-case reduction `LaplaceMarginDeep.FiniteSMarginWorstcase w`, the full `AdjacentMLR.SaddleFloor
w` follows: feed the proved θ tail `whAllSMargin` through it (`finiteSMarginOfWorstcase`) and rescale
(`saddleFloor_of_finiteSMargin`).  So the SOLE residual for `SaddleFloor w` is
`FiniteSMarginWorstcase w` — the coefficient-array TP₂/MLR `w`-monotonicity
(`CrossRatioMonotone.ArrayMLR`), NOT any Gaussian saddle / local-CLT estimate (that piece is closed
at wH above). -/
def saddleFloor_of_worstcase {w : Q'}
    (r : LaplaceMarginDeep.FiniteSMarginWorstcase w) : AdjacentMLR.SaddleFloor w :=
  saddleFloor_of_finiteSMargin
    (LaplaceMarginDeep.finiteSMarginOfWorstcase r WHTailCeilingsClose.whAllSMargin)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `rescaleDenom` — the converse denominator rescale `40000·A ≤ 22801·B ⟹ A ≤ ρ·B`.
  * `saddleFloor_of_finiteSMargin` — the converse reduction `FiniteSMargin w ⟹ SaddleFloor w`
    (so `SaddleFloor w ⟺ FiniteSMargin w`).
  * `finiteSMarginWorstcase_wH` — the identity worst-case witness at `w = wH`.
  * `finiteSMargin_wH` — `FiniteSMargin wH` from the proved θ-envelope ceilings.
  * `saddleFloor_wH` — `SaddleFloor wH` CLOSED at the worst coupling.
  * `reserve_wH` — the full `AcNDefectReserve wH` end-to-end at the worst coupling.
  * `saddleFloor_of_worstcase` — the general-`w` reduction to `FiniteSMarginWorstcase w`.

NAMED OPEN (Type-level structure, never `sorry`; NOT re-declared here, lives upstream):
  * `LaplaceMarginDeep.FiniteSMarginWorstcase w` — the `w`-monotone reduction to the wH sequence,
    the coefficient-array TP₂/MLR wall (`CrossRatioMonotone.ArrayMLR`), the sole residual for
    `SaddleFloor w` at general `w`.

HONEST VERDICT.  The one-sided windowed saddle floor `SaddleFloor` is CLOSED at the worst coupling
`w = wH` (and with it `FiniteSMargin wH` and the reserve `AcNDefectReserve wH`), directly from the
proved θ-envelope ceilings — no steepest-descent / Tate–Zelditch estimate is required.  The remaining
open node for general `w` is re-pointed off the saddle and onto the coefficient-array `w`-monotone
reduction `FiniteSMarginWorstcase`.  This is a structural closure of one box-level log-concavity
sub-fact at the worst coupling; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.SaddleFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SaddleFloor.rescaleDenom
#print axioms YMGap.Continuum.SaddleFloor.saddleFloor_of_finiteSMargin
#print axioms YMGap.Continuum.SaddleFloor.finiteSMarginWorstcase_wH
#print axioms YMGap.Continuum.SaddleFloor.finiteSMargin_wH
#print axioms YMGap.Continuum.SaddleFloor.saddleFloor_wH
#print axioms YMGap.Continuum.SaddleFloor.reserve_wH
#print axioms YMGap.Continuum.SaddleFloor.saddleFloor_of_worstcase
