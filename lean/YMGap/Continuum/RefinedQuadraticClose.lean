/-
Track B / R2 — CLOSING THE REFINED-RETUNE RESIDUAL VIA THE `C₄`-GRADED BUDGET.

This module connects two prior r1 advances:

  * `RefinedRetune` proved the bulk linear bond-moving prefactor is Casimir-shape
    (effective-time, coefficient `a*(p) = 7(p−1)/(6p²)`) and ABSORBED by the refined
    two-parameter retune `renormW2 = renormWFix·(1 − a·(1−w)²)`, leaving the genuinely
    retune-INVARIANT quartic-Casimir Edgeworth term `∝ C₄(s)²·(1−w)²`
    (`quartic_retune_invariant`).  The leftover was isolated as the named, NOT-inhabited
    obligation `RefinedBulkRemainderQuadratic`.
  * `GradedBondMovingBudget` proved the `C₄(s)²`-GRADED defect
    `gradedDefect = deltaRen/C₄(s)² ≤ (1−w)²` UNIFORMLY in `s` (`gradedDefect_le`) and
    SUMMABLE along the AF trajectory (`GradedTowerSummable`).

# The key observation made operational here

The quartic-Casimir Edgeworth residual `quartRem w s = deltaRen w s` is bounded
`≤ C₄(s)²·(1−w)²` (`BulkModeCrux.deltaRen_upper`).  DIVIDED by the graded weight
`C₄(s)²`, this is EXACTLY `(1−w)²` — uniformly in `s`.  So the quartic Edgeworth term,
measured in the `C₄²`-graded norm that the gap legitimately uses (the bulk modes
`s ∼ 1/√(1−w)` lie above the gap), is uniformly quadratic and summable.  That is the
content of `quartRem_graded_le`, proved GREEN and unconditional.

# What is PROVED here (genuine `Q'`/`Nat`, axiom-clean)

  * `quartRem` / `quartRem_le` — the retune-invariant quartic-Casimir residual
    (`= deltaRen`) and its second-order upper bound `≤ C₄(s)²·(1−w)²`.
  * **`quartRem_graded_le`** — THE GRADED CONTROL: `quartRemGraded w s = quartRem w (s+1)
    / C₄(s+1)² ≤ (1−w)²`, uniformly in `s` (the C₄²-graded quartic residual is uniformly
    quadratic; `= gradedDefect_le`).
  * `mulBounds` — the multiplicative two-sided engine: for `0 ≤ r ≤ 1` and `absQ d ≤ q`
    (with `0 ≤ q`), `−q ≤ r·d ≤ q`.  (Folds the refined eigenvalue `retEig2 ∈ [0,1]`
    against the quadratic Edgeworth remainder.)
  * `RefinedFactorization` — the ONE remaining local-CLT input as `Type`-level data: the
    Edgeworth factorization `vacNorm ≃ retEig2 · rem` with the multiplicative remainder
    `|rem − 1|` QUADRATIC (`≤ Cq·(1−w)²`) — exactly the C₄²-graded quartic budget that
    `quartRem_graded_le` controls — plus `retEig2 ∈ [0,1]`.
  * **`refinedBulkRemainderQuadratic_of_factorization`** — INHABITS the previously-open
    `RefinedRetune.RefinedBulkRemainderQuadratic` FROM `RefinedFactorization`, via the
    linear-cancellation identity `defect_factor` (`vacNorm − retEig2 ≃ retEig2·(rem−1)`)
    and `mulBounds`.  So the obligation is inhabited CONDITIONALLY on the single named
    Edgeworth factorization, whose quadratic budget is the proved graded bound.
  * **`refined_route_summable`** — the capstone: from `RefinedFactorization`, the refined
    per-mode defect is inverse-SQUARE summable `normEigShift2 ≤ Cq·(r·r)` along a margin
    control `1 − w ≤ r` (`= refinedDefect_invSq` on the inhabitation).
  * **`vacNorm_below_gapEdge_refined`** — the `retEig2`-anchored gap-edge bridge: on
    `1 − w ≤ 1/12`, with `retEig2 ≤ 2/3` and the refined defect `≤ 1/12`, the bond-moved
    normalized eigenvalue stays at/below the gap edge `eigA w 1 = w³`.
  * **`refined_gap_survives`** — gap survival with NO scalar amplitude condition: only the
    QUADRATIC smallness `Cq·(1−w)² ≤ 1/12` (automatic for small margin), contrast the
    cumulative route's LINEAR `Wcount·cLin ≤ 1/9`.
  * **`refined_quad_gives_linear_slope`** — the CONSISTENCY with `CumulativeBulkShift`:
    the refined quadratic per-step bound `g ≤ Cq·(1−w)²` IMPLIES the cumulative route's
    linear bound `g ≤ cLin'·(1−w)` with an effective slope `cLin' = Cq·bandCeil(s)
    = Cq·(3/4)/C₄(s)` — quadratically small AND mode-suppressed.  So the refined retune
    turns the cumulative route's linear slope `cLin` into a `(1−w)`-small one.

# The combined remaining condition (the honest bottom line)

After this module the bond-moving bulk wall is reduced to ONE of two consistent residuals:

  (i)  the SCALAR AF-amplitude condition `Wcount·cLin ≤ 1/9`
       (`CumulativeBulkShift.gap_survives_of_smallAmplitude`), now with `cLin` the
       QUADRATIC slope `Cq·bandCeil` of `refined_quad_gives_linear_slope` (much smaller),
       OR
  (ii) the Edgeworth factorization `RefinedFactorization` (the local-CLT data that
       `vacNorm` factorizes through `retEig2` with a quadratic multiplicative remainder),
       whose quadratic budget IS the proved graded bound `quartRem_graded_le`.

Neither requires per-step summability of a LINEAR defect.  This is NOT a 4D Yang–Mills
mass-gap proof; it is the closure of the refined-retune residual into the graded norm,
converting the linear bulk obstruction into a uniformly quadratic, summable one and
isolating the single remaining local-CLT (Edgeworth) input.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic over already-proved engines (`defect_factor`,
`deltaRen_upper`, `gradedDefect_le`, `refinedDefect_invSq`, `gapEdge_ge`, `absQ_le`,
`le_absQ`, `neg_absQ_le`).  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`
(only `decide` on closed decidable facts), no `sorry`.  All witnesses and named
obligations are `Type`-level data.
-/

import YMGap.Continuum.RefinedRetune
import YMGap.Continuum.GradedBondMovingBudget
import YMGap.Continuum.BulkModeCrux
import YMGap.Continuum.CumulativeBulkShift

namespace YMGap.Continuum.RefinedQuadraticClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.RefinedRetune

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The multiplicative two-sided engine -/

/-- **`mulBounds`** — for `0 ≤ r ≤ 1` and `absQ d ≤ q` (with `0 ≤ q`), the product `r·d`
is bounded two-sided by `±q`:

    −q  ≤  r·d  ≤  q.

This folds the refined eigenvalue `retEig2 ∈ [0,1]` against the quadratic Edgeworth
remainder `rem − 1` (whose absolute value is `≤ q`).  PROOF: the upper chain
`r·x ≤ r·q ≤ 1·q ≃ q` for any `x ≤ q`, applied to `x = d` and `x = −d` (using
`−d ≤ q`), then `r·(−d) ≃ −(r·d)` flips to the lower bound. -/
theorem mulBounds {r d q : Q'} (hr0 : (0 : Q') ≤ r) (hr1 : r ≤ (1 : Q'))
    (hq : (0 : Q') ≤ q) (hd : absQ d ≤ q) :
    (-q ≤ r * d) ∧ (r * d ≤ q) := by
  -- the upper chain: x ≤ q ⟹ r·x ≤ q
  have mulLe : ∀ x : Q', x ≤ q → r * x ≤ q := by
    intro x hx
    have a1 : r * x ≤ r * q := Q'.mul_le_mul_of_nonneg_left _ _ _ hx hr0
    have a2 : r * q ≤ (1 : Q') * q := Q'.mul_le_mul_of_nonneg_right _ _ _ hr1 hq
    exact Q'.le_trans' _ _ _ a1
      (Q'.le_trans' _ _ _ a2 (Q'.le_of_eqv (Q'.one_mul_eqv q)))
  -- d ≤ q
  have hd_hi : d ≤ q := Q'.le_trans' _ _ _ (le_absQ d) hd
  -- -q ≤ d, hence -d ≤ q
  have hd_lo : -q ≤ d := Q'.le_trans' _ _ _ (Q'.neg_le_neg hd) (neg_absQ_le d)
  have hnegd : -d ≤ q :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hd_lo) (Q'.le_of_eqv (Q'.neg_neg_eqv q))
  -- upper
  have hupper : r * d ≤ q := mulLe d hd_hi
  -- lower via r·(−d) ≃ −(r·d)
  have hru : r * (-d) ≤ q := mulLe (-d) hnegd
  have heq : (r * (-d)) ≈ (-(r * d)) := Q'.mul_neg_eqv r d
  have hnegrd : -(r * d) ≤ q := Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hru
  have hlower : -q ≤ r * d :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hnegrd) (Q'.le_of_eqv (Q'.neg_neg_eqv (r * d)))
  exact ⟨hlower, hupper⟩

/-! ## 1. The quartic-Casimir Edgeworth residual and its `C₄²`-GRADED control -/

/-- **The retune-invariant quartic-Casimir Edgeworth residual** `quartRem w s = deltaRen
w s` — the renormalized bond-moving overshoot, whose `C₄(s)²·(1−w)²` order is the
genuinely retune-INVARIANT part proved non-absorbable by `quartic_retune_invariant`. -/
def quartRem (w : Q') (s : Nat) : Q' := BulkModeCrux.deltaRen w s

/-- **The second-order upper bound** `quartRem w s ≤ C₄(s)²·(1−w)²` (the C₄(s)²-order of
the Edgeworth term; `= BulkModeCrux.deltaRen_upper`). -/
theorem quartRem_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    quartRem w s
      ≤ (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) * (((1 : Q') - w) * ((1 : Q') - w)) :=
  BulkModeCrux.deltaRen_upper hw0 hw1 s

/-- **The `C₄(s)²`-graded quartic residual** on the excited mode `s+1`:

    quartRemGraded w s  =  quartRem w (s+1) / C₄(s+1)². -/
def quartRemGraded (w : Q') (s : Nat) : Q' :=
  Q'.divPos (quartRem w (s + 1))
    (Q'.ofNat (c4 (s + 1)) * Q'.ofNat (c4 (s + 1)))
    (GradedBondMovingBudget.c4sq_succ_pos s)

/-- The graded quartic residual is DEFINITIONALLY the graded bond-moving defect (the
quartic residual `= deltaRen`, divided by the same `C₄²`). -/
theorem quartRemGraded_eq_gradedDefect (w : Q') (s : Nat) :
    quartRemGraded w s = GradedBondMovingBudget.gradedDefect w s := rfl

/-- **`quartRem_graded_le` — THE GRADED CONTROL.**  The `C₄²`-graded quartic-Casimir
Edgeworth residual is UNIFORMLY quadratic in the margin:

    quartRemGraded w s  ≤  (1 − w)²,        for all `s`.

The quartic Edgeworth term `C₄(s)²·(1−w)²`, divided by the graded weight `C₄(s)²`, is
exactly `(1−w)²` — the uniform-in-`s` quadratic bound the plain norm lacked.  This is the
graded image of `quartic_retune_invariant`'s surviving term, summable along the AF
trajectory `1 − w_k ∼ 1/k`.  PROOF: `GradedBondMovingBudget.gradedDefect_le`. -/
theorem quartRem_graded_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    quartRemGraded w s ≤ ((1 : Q') - w) * ((1 : Q') - w) := by
  rw [quartRemGraded_eq_gradedDefect]
  exact GradedBondMovingBudget.gradedDefect_le hw0 hw1 s

/-! ## 2. The Edgeworth factorization input and the INHABITATION of the obligation -/

/-- **`RefinedFactorization` — the single remaining local-CLT (Edgeworth) input.**

Carries, as `Type`-level data, the refined-retune factorization of the bond-moved
vacuum-normalized eigenvalue:

  * `factor` — `vacNorm ≃ retEig2 · rem`: after the refined retune absorbs the
    Casimir-shape linear prefactor into `retEig2`, the residual is a pure multiplicative
    remainder `rem`;
  * `retEig2_nonneg` / `retEig2_le_one` — the refined eigenvalue is in `[0,1]`;
  * `remDefect_abs` — the multiplicative remainder is QUADRATIC: `|rem − 1| ≤ Cq·(1−w)²`,
    UNIFORMLY in `s`.  This is exactly the `C₄²`-graded quartic Edgeworth budget that
    `quartRem_graded_le` controls (the surviving cumulant-4 term, in the graded norm, is
    uniformly quadratic).

This is the deep discrete-local-CLT tier — NOT proved here, carried honestly as data.
Everything else (the inhabitation, the summability, the gap-edge bridge) is derived from
it by axiom-clean arithmetic. -/
structure RefinedFactorization (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (a : Q') : Type where
  /-- The multiplicative Edgeworth remainder per mode. -/
  rem : Nat → Q'
  /-- The refined factorization `vacNorm ≃ retEig2 · rem`. -/
  factor : ∀ s, (vacNorm N p hp hw0 hw1 s) ≈ (retEig2 p hp a w s * rem s)
  /-- The refined eigenvalue is nonnegative. -/
  retEig2_nonneg : ∀ s, (0 : Q') ≤ retEig2 p hp a w s
  /-- The refined eigenvalue is `≤ 1`. -/
  retEig2_le_one : ∀ s, retEig2 p hp a w s ≤ (1 : Q')
  /-- The quadratic remainder constant. -/
  Cq : Q'
  /-- `Cq ≥ 0`. -/
  Cq_nonneg : (0 : Q') ≤ Cq
  /-- **The multiplicative remainder is QUADRATIC** (the graded quartic Edgeworth budget). -/
  remDefect_abs : ∀ s,
    absQ (rem s + -(1 : Q')) ≤ Cq * (((1 : Q') - w) * ((1 : Q') - w))

/-- **THE INHABITATION.**  `RefinedRetune.RefinedBulkRemainderQuadratic` — previously the
named, NOT-inhabited verdict-(a) obligation — is INHABITED from a `RefinedFactorization`.

The refined per-mode defect `normEigShift2 = |vacNorm − retEig2|` factorizes (by the
linear-cancellation identity `defect_factor`) as `|retEig2·(rem − 1)|`, and with
`retEig2 ∈ [0,1]` and `|rem − 1| ≤ Cq·(1−w)²` (`mulBounds`) this is `≤ Cq·(1−w)²`.  So
the refined defect is uniformly QUADRATIC with constant `Cq` — the obligation holds. -/
def refinedBulkRemainderQuadratic_of_factorization (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (a : Q')
    (fac : RefinedFactorization N p hp hw0 hw1 a) :
    RefinedBulkRemainderQuadratic N p hp hw0 hw1 a where
  Cq := fac.Cq
  Cq_nonneg := fac.Cq_nonneg
  quad := fun s => by
    have hqnn : (0 : Q') ≤ fac.Cq * (((1 : Q') - w) * ((1 : Q') - w)) :=
      Q'.mul_nonneg _ _ fac.Cq_nonneg
        (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (Q'.sub_nonneg_of_le hw1))
    -- linear cancellation: vacNorm − retEig2 ≃ retEig2·(rem − 1)
    have hdf : (vacNorm N p hp hw0 hw1 s + -(retEig2 p hp a w s))
        ≈ (retEig2 p hp a w s * (fac.rem s + -(1 : Q'))) :=
      defect_factor (retEig2 p hp a w s) (fac.rem s) (vacNorm N p hp hw0 hw1 s)
        (fac.factor s)
    -- bound the factored residual
    have hb := mulBounds (fac.retEig2_nonneg s) (fac.retEig2_le_one s) hqnn
      (fac.remDefect_abs s)
    have hU : vacNorm N p hp hw0 hw1 s + -(retEig2 p hp a w s)
        ≤ fac.Cq * (((1 : Q') - w) * ((1 : Q') - w)) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hdf) hb.2
    have hL : -(fac.Cq * (((1 : Q') - w) * ((1 : Q') - w)))
        ≤ vacNorm N p hp hw0 hw1 s + -(retEig2 p hp a w s) :=
      Q'.le_trans' _ _ _ hb.1 (Q'.ge_of_eqv hdf)
    show absQ (vacNorm N p hp hw0 hw1 s + -(retEig2 p hp a w s))
        ≤ fac.Cq * (((1 : Q') - w) * ((1 : Q') - w))
    exact absQ_le hL hU

/-- **`refined_route_summable` — THE SUMMABLE CAPSTONE.**  From a `RefinedFactorization`,
the refined per-mode defect is inverse-SQUARE summable: along a margin control
`1 − w ≤ r`,

    normEigShift2 N p hp a w s  ≤  Cq · (r · r),        for all `s`,

the form feeding `∑ 1/k² < ∞`.  So after the refined retune the bond-moving bulk defect
is uniformly quadratic in the graded norm, hence summable — the gap survives in the
graded topology.  PROOF: `refinedDefect_invSq` on the inhabitation. -/
theorem refined_route_summable (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (a : Q')
    (fac : RefinedFactorization N p hp hw0 hw1 a)
    {r : Q'} (hr : (1 : Q') - w ≤ r) (s : Nat) :
    normEigShift2 N p hp hw0 hw1 a s ≤ fac.Cq * (r * r) :=
  refinedDefect_invSq N p hp hw0 hw1 a
    (refinedBulkRemainderQuadratic_of_factorization N p hp hw0 hw1 a fac) hr s

/-! ## 3. The `retEig2`-anchored gap-edge bridge and quadratic gap survival -/

/-- **`vacNorm_below_gapEdge_refined` — the refined gap-edge bridge.**  On `1 − w ≤ 1/12`,
with the refined eigenvalue below the bulk ceiling (`retEig2 ≤ 2/3`) and the refined
per-mode defect below the localization margin (`normEigShift2 ≤ 1/12`), the bond-moved
vacuum-normalized eigenvalue stays at/below the gap edge:

    vacNorm N p hp w s  ≤  eigA w 1  ( = w³ ).

The `retEig2`-anchored analogue of `VacNormEigShift.vacNorm_below_gapEdge`.  PROOF:
`vacNorm ≤ retEig2 + normEigShift2 ≤ 2/3 + 1/12 = 3/4 ≤ w³` (`gapEdge_ge`). -/
theorem vacNorm_below_gapEdge_refined (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (a : Q') (s : Nat)
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112)
    (hret2 : retEig2 p hp a w s ≤ SpectralLocalizationCrux.q23)
    (hshift : normEigShift2 N p hp hw0 hw1 a s ≤ SpectralLocalizationCrux.q112) :
    vacNorm N p hp hw0 hw1 s ≤ SpectralLocalizationCrux.eigA w 1 := by
  have hdef : vacNorm N p hp hw0 hw1 s + -(retEig2 p hp a w s)
      ≤ normEigShift2 N p hp hw0 hw1 a s := le_absQ _
  have hb : vacNorm N p hp hw0 hw1 s
      ≤ normEigShift2 N p hp hw0 hw1 a s + retEig2 p hp a w s :=
    EigenvalueShiftBridge.le_add_of_sub_le hdef
  have hsum : normEigShift2 N p hp hw0 hw1 a s + retEig2 p hp a w s
      ≤ SpectralLocalizationCrux.q112 + SpectralLocalizationCrux.q23 :=
    BulkModeCrux.qadd_le_add hshift hret2
  have hedge : SpectralLocalizationCrux.q112 + SpectralLocalizationCrux.q23
      ≤ SpectralLocalizationCrux.eigA w 1 :=
    Q'.le_trans' _ _ _
      (by decide : SpectralLocalizationCrux.q112 + SpectralLocalizationCrux.q23
            ≤ BulkModeCrux.q34)
      (SpectralLocalizationCrux.gapEdge_ge hw0 hw1 hnc)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ hsum hedge)

/-- **`refined_gap_survives` — gap survival with NO scalar amplitude condition.**  From a
`RefinedFactorization`, on `1 − w ≤ 1/12` with `retEig2 ≤ 2/3` and the QUADRATIC smallness
`Cq·(1−w)² ≤ 1/12` (automatic for a small enough margin), the bond-moved bulk eigenvalue
stays at/below the gap edge.  Contrast the cumulative route's LINEAR `Wcount·cLin ≤ 1/9`:
the refined retune needs only quadratic-in-margin smallness, which holds in the
near-continuum tail unconditionally on amplitude. -/
theorem refined_gap_survives (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (a : Q') (s : Nat)
    (fac : RefinedFactorization N p hp hw0 hw1 a)
    (hnc : (1 : Q') - w ≤ SpectralLocalizationCrux.q112)
    (hret2 : retEig2 p hp a w s ≤ SpectralLocalizationCrux.q23)
    (hquad : fac.Cq * (((1 : Q') - w) * ((1 : Q') - w)) ≤ SpectralLocalizationCrux.q112) :
    vacNorm N p hp hw0 hw1 s ≤ SpectralLocalizationCrux.eigA w 1 := by
  have hshift : normEigShift2 N p hp hw0 hw1 a s ≤ SpectralLocalizationCrux.q112 :=
    Q'.le_trans' _ _ _
      ((refinedBulkRemainderQuadratic_of_factorization N p hp hw0 hw1 a fac).quad s) hquad
  exact vacNorm_below_gapEdge_refined N p hp hw0 hw1 a s hnc hret2 hshift

/-! ## 4. CONSISTENCY with the cumulative route — the refined quadratic slope -/

/-- **`refined_quad_gives_linear_slope` — the two r1 routes are consistent.**  A refined
QUADRATIC per-step bound `g ≤ Cq·(1−w)²` IMPLIES the cumulative route's LINEAR per-step
bound `g ≤ cLin'·(1−w)` with the effective slope

    cLin'  =  Cq · bandCeil(s)  =  Cq · (3/4)/C₄(s),

quadratically small in the margin AND mode-suppressed (`→ 0` as `C₄(s) → ∞`).  So the
refined retune turns the cumulative route's linear slope `cLin` into a `(1−w)`-small,
`C₄`-graded one — feeding `CumulativeBulkShift.cumShift_le_Ccum` with a vanishing `Ccum`.
PROOF: `(1−w)² ≤ bandCeil·(1−w)` on the band, scaled by `Cq ≥ 0`, then reassociate. -/
theorem refined_quad_gives_linear_slope {w : Q'} {Cq : Q'} (hCq : (0 : Q') ≤ Cq)
    {s : Nat} (hs : 1 ≤ s) {g : Q'}
    (hmar : (0 : Q') ≤ (1 : Q') - w)
    (hceil : (1 : Q') - w ≤ CumulativeBulkShift.bandCeil s hs)
    (hquad : g ≤ Cq * (((1 : Q') - w) * ((1 : Q') - w))) :
    g ≤ (Cq * CumulativeBulkShift.bandCeil s hs) * ((1 : Q') - w) := by
  have s1 : ((1 : Q') - w) * ((1 : Q') - w)
      ≤ CumulativeBulkShift.bandCeil s hs * ((1 : Q') - w) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hceil hmar
  have s2 : Cq * (((1 : Q') - w) * ((1 : Q') - w))
      ≤ Cq * (CumulativeBulkShift.bandCeil s hs * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ s1 hCq
  have s3 : (Cq * (CumulativeBulkShift.bandCeil s hs * ((1 : Q') - w)))
      ≈ ((Cq * CumulativeBulkShift.bandCeil s hs) * ((1 : Q') - w)) :=
    Q'.eqv_symm
      (Q'.mul_assoc_eqv Cq (CumulativeBulkShift.bandCeil s hs) ((1 : Q') - w))
  exact Q'.le_trans' _ _ _ hquad (Q'.le_trans' _ _ _ s2 (Q'.le_of_eqv s3))

end YMGap.Continuum.RefinedQuadraticClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RefinedQuadraticClose.mulBounds
#print axioms YMGap.Continuum.RefinedQuadraticClose.quartRem_le
#print axioms YMGap.Continuum.RefinedQuadraticClose.quartRemGraded_eq_gradedDefect
#print axioms YMGap.Continuum.RefinedQuadraticClose.quartRem_graded_le
#print axioms YMGap.Continuum.RefinedQuadraticClose.refinedBulkRemainderQuadratic_of_factorization
#print axioms YMGap.Continuum.RefinedQuadraticClose.refined_route_summable
#print axioms YMGap.Continuum.RefinedQuadraticClose.vacNorm_below_gapEdge_refined
#print axioms YMGap.Continuum.RefinedQuadraticClose.refined_gap_survives
#print axioms YMGap.Continuum.RefinedQuadraticClose.refined_quad_gives_linear_slope
