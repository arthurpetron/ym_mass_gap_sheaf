/-
Track B / R2 — **THE FREE-QUADRATIC-DEFECT + RENORMALON-SUBDOMINANCE WINDOW TEST on the
sole remaining coupling window `[w*, 1)` (`w* = 2^{−1/3}`).**

# The crack being tested (read first)

`RenDefectQuadFactor` PROVED the free (single-plaquette, counterterm-subtracted) per-step
renormalized defect exactly:

    δ_free(w) = 2·(1 − w)²·(2 + w)          (`dfreeExpr`, `= bondMovingDeltaRen 1 1 w`)

and `CharFunCumulantDefect` records the model bound target `realδ ≤ 6·(1 − w)²`.  The
FREE SLACK — the room the interacting correction `Δ(w) := realδ(w) − δ_free(w)` may use
while keeping `realδ ≤ 6(1 − w)²` — is EXACTLY

    slack(w) = 6(1 − w)² − δ_free(w) = 2·(1 − w)³          (`slackExpr`, `dfree_add_slack_eqv_model`).

`FieldSpaceRenormalonZ1` PROVED the interacting activity's field-space (`g² = −log w`)
expansion is a FIXED-sign, zero-radius **renormalon**, whose non-perturbative ambiguity is
`∼ exp(−π²/g²)`.  The tested crack: on a window `[w₁, 1)` near `w = 1`, is the interacting
correction `Δ(w)` subdominant to the free slack `2(1 − w)³` — so that `realδ ≤ 6(1 − w)²`
there — and does `w₁ ≤ w*` (OVERLAP the character window `[0, w*)` ⟹ closure)?

# THE HONEST, ADVERSARIAL VERDICT (deliverable (iii) — NO closure; a real strip survives)

The crack FAILS, decisively, at BOTH ends of the window — and the failure is *not* a
smallness that the renormalon can rescue.  Two machine-checked obstructions:

## (1) The renormalon ambiguity is subdominant but is the WRONG object.
`exp(−π²/g²) < 2(1 − w)³` for every `w ∈ (0,1)` (mpmath dps 50: the ratio maxes at
`0.12` near `w = 0` and is `∼10⁻¹⁷` at `w*`, `∼10⁻⁴²¹` at `w = 0.99`).  So IF `Δ` were the
renormalon alone, `w₁ = 0` and the window would trivially close.  This is the SEDUCTIVE
FAKE: the renormalon `exp(−π²/g²)` is the *resummation AMBIGUITY* of the perturbative
field-space series — an irreducible non-perturbative UNCERTAINTY, a LOWER bound on the
non-perturbative content — **not an upper bound on the full interacting `Δ(w)`.**

## (2) THE DECISIVE ORDER-COUNTING OBSTRUCTION (the catch, machine-checked).
Writing `u = 1 − w`: `δ_free(u) = 6u² − 2u³` already **saturates the model bound `6u²` to
SECOND order**; the slack `slack(u) = 2u³` is purely THIRD order (`dfree_add_slack_eqv_model`).
Hence `realδ ≤ 6(1 − w)²` requires `Δ ≤ 2u³` — `Δ` must be genuinely THIRD order or smaller.
But the interacting correction has convergent multi-plaquette / higher-representation pieces
that are POLYNOMIAL and generically SECOND order, `Δ ∼ c·u²`.  A second-order correction
obeys `c·u² ≤ 2u³` only for `u ≥ c/2`, i.e. `w ≤ 1 − c/2` — it **VIOLATES on `(1 − c/2, 1)`**,
a neighbourhood of `w = 1`.  `secondOrder_exceeds_slack` / `secondOrder_breaks_model`
witness this at `w = 9/10, c = 1`: a unit second-order correction exceeds the cubic slack
(`10/1000 > 2/1000`) and pushes `δ_free + c·u²` past the model bound (`68/1000 > 60/1000`).
So the `w → 1` end is NOT auto-closed: the renormalon (exp-small) does not rescue it, because
the obstruction is a polynomial SECOND-order piece, not exp-small.  Whether `Δ` is truly
third order is EXACTLY the open `singleStep` content — not delivered by subdominance.

## (3) The rigorous a-priori bound fails already at `w ≈ 0.635 < w*`.
The only rigorous a-priori UPPER bound on the interacting off-diagonal is the character
activity `plaqActivity`; even its LEADING term `coeffW w 1 = 2w³` already EXCEEDS the Temple
threshold `6(1 − w)²(1 − w³)` at `w = 13/20 = 0.65` (`charLead_exceeds_threshold`,
`0.533 < 0.549`).  The full activity crosses at `w_cross ≈ 0.6348` (mpmath), BELOW the
Lean-proved character range `[0, 5/8]` endpoint's neighbour and below `w* = 0.7937`; and it
DIVERGES `∼ 1/(2(1 − w))` as `w → 1` (`z₁/threshold → ∞`), so the a-priori route is useless
at the `w → 1` end too.

**CONCLUSION.** The windows do NOT overlap.  The renormalon subdominance controls only the
exp-small resummation ambiguity — never the obstruction.  The residual is the honest strip
`[w_cross, 1) ≈ [0.635, 1)` (rigorously `[5/8, 1)`), and the renormalon crack supplies NO
`w₁ < 1` upper control.  This is a SHARP negative result (deliverable (iii)): the crack is
refuted by exact order-counting + a decidable a-priori-threshold failure.  It inhabits NO
guarded frontier type and produces NO `SingleStepDefectBound`; the 4D Yang–Mills mass gap
remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`.  The slack identity `dfree_add_slack_eqv_model` is a factor-out-`(1 − w)²`
`Q'.eqv` chain (no coefficient collection, the `RenDefectQuadFactor` methodology); the
order-counting and a-priori-failure facts are `decide` on closed concrete `Q'` rationals.
Every load-bearing declaration is `#print axioms`-gated to `propext`/`Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `ring`/`nlinarith`, no `sorry`.  All witnesses are
`Type`-level `Q'` data.
-/

import YMGap.Continuum.OffDiagonalActivityBound
import YMGap.Continuum.FieldSpaceRenormalonZ1

namespace YMGap.Continuum.SubdominanceWindow

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.OffDiagonalActivityBound

/-! ## 1. The free defect, the free slack, and the model bound (raw `Q'` expressions). -/

/-- `(1 − w)²` — the quadratic weak-coupling margin factor. -/
def oneSubWSq (w : Q') : Q' := ((1 : Q') - w) * ((1 : Q') - w)

/-- **`dfreeExpr w = 2·(1 − w)²·(2 + w)`** — the PROVED free (counterterm-subtracted)
renormalized per-step defect `δ_free` (`= bondMovingDeltaRen 1 1 w`, `dimQ 1 = 2`,
`RenDefectQuadFactor.renDefect_factor`). -/
def dfreeExpr (w : Q') : Q' := Q'.ofNat 2 * (oneSubWSq w * (Q'.ofNat 2 + w))

/-- **`slackExpr w = 2·(1 − w)²·(1 − w) = 2·(1 − w)³`** — the FREE SLACK, the budget the
interacting correction `Δ` may use.  Purely THIRD order in `u = 1 − w`. -/
def slackExpr (w : Q') : Q' := Q'.ofNat 2 * (oneSubWSq w * ((1 : Q') - w))

/-- **`modelExpr w = 6·(1 − w)²`** — the model per-step defect bound target `realδ ≤ 6(1−w)²`. -/
def modelExpr (w : Q') : Q' := Q'.ofNat 6 * oneSubWSq w

/-! ## 2. The exact free-margin decomposition `model = δ_free + slack`. -/

/-- **`const_collapse` — `(2 + w) + (1 − w) ≃ 3`.**  The linear terms cancel: `w + (−w) = 0`.
The one place the margin `w` drops out, leaving the constant `3` that turns `(1 − w)²·3` into
`6(1 − w)²`. -/
theorem const_collapse (w : Q') :
    ((Q'.ofNat 2 + w) + ((1 : Q') - w)).eqv (Q'.ofNat 3) := by
  -- (2 + w) + (1 + −w) ≃ 2 + (w + (1 + −w))
  have s1 : ((Q'.ofNat 2 + w) + ((1 : Q') - w)).eqv
      (Q'.ofNat 2 + (w + ((1 : Q') - w))) :=
    Q'.add_assoc_eqv (Q'.ofNat 2) w ((1 : Q') - w)
  -- w + (1 + −w) ≃ w + (−w + 1) ≃ (w + −w) + 1 ≃ 0 + 1 ≃ 1
  have s2 : (w + ((1 : Q') - w)).eqv (1 : Q') := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left w _ _ (Q'.add_comm_eqv (1 : Q') (-w))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv w (-w) (1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (1 : Q') (Q'.add_neg_self_eqv w)) ?_
    exact q_zero_add_eqv (1 : Q')
  refine Q'.eqv_trans _ _ _ s1 ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (Q'.ofNat 2) _ _ s2) ?_
  decide

/-- **`dfree_add_slack_eqv_model` — the EXACT free-margin decomposition.**

    δ_free(w) + slack(w)  =  2(1 − w)²(2 + w) + 2(1 − w)³  ≃  6(1 − w)²  =  model(w).

Equivalently `model − δ_free ≃ slack = 2(1 − w)³`: the free defect saturates the model bound
to second order in `u = 1 − w`, and the slack is purely third order — the decisive input to
the order-counting obstruction.  Proved by factoring out `2·(1 − w)²` (`const_collapse` gives
`(2 + w) + (1 − w) ≃ 3`), never by coefficient collection. -/
theorem dfree_add_slack_eqv_model (w : Q') :
    (dfreeExpr w + slackExpr w).eqv (modelExpr w) := by
  -- factor out ofNat 2
  have e1 : (dfreeExpr w + slackExpr w).eqv
      (Q'.ofNat 2 *
        (oneSubWSq w * (Q'.ofNat 2 + w) + oneSubWSq w * ((1 : Q') - w))) :=
    Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat 2)
      (oneSubWSq w * (Q'.ofNat 2 + w)) (oneSubWSq w * ((1 : Q') - w)))
  -- factor out (1 − w)²
  have e2 : (oneSubWSq w * (Q'.ofNat 2 + w) + oneSubWSq w * ((1 : Q') - w)).eqv
      (oneSubWSq w * ((Q'.ofNat 2 + w) + ((1 : Q') - w))) :=
    Q'.eqv_symm (Q'.mul_add_eqv (oneSubWSq w) (Q'.ofNat 2 + w) ((1 : Q') - w))
  -- constant collapse
  have e3 : (oneSubWSq w * ((Q'.ofNat 2 + w) + ((1 : Q') - w))).eqv
      (oneSubWSq w * Q'.ofNat 3) :=
    Q'.mul_eqv_congr_left (oneSubWSq w) _ _ (const_collapse w)
  -- (1 − w)²·3 ≃ 3·(1 − w)²
  have e4 : (oneSubWSq w * Q'.ofNat 3).eqv (Q'.ofNat 3 * oneSubWSq w) :=
    Q'.mul_comm_eqv (oneSubWSq w) (Q'.ofNat 3)
  have inner : (oneSubWSq w * (Q'.ofNat 2 + w) + oneSubWSq w * ((1 : Q') - w)).eqv
      (Q'.ofNat 3 * oneSubWSq w) :=
    Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 e4)
  -- 2·(3·(1 − w)²) ≃ (2·3)·(1 − w)² ≃ 6·(1 − w)²
  have e5 : (Q'.ofNat 2 *
        (oneSubWSq w * (Q'.ofNat 2 + w) + oneSubWSq w * ((1 : Q') - w))).eqv
      (Q'.ofNat 2 * (Q'.ofNat 3 * oneSubWSq w)) :=
    Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ inner
  have e6 : (Q'.ofNat 2 * (Q'.ofNat 3 * oneSubWSq w)).eqv
      ((Q'.ofNat 2 * Q'.ofNat 3) * oneSubWSq w) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 3) (oneSubWSq w))
  have e7 : ((Q'.ofNat 2 * Q'.ofNat 3) * oneSubWSq w).eqv (Q'.ofNat 6 * oneSubWSq w) :=
    Q'.mul_eqv_congr_right _ _ (oneSubWSq w) (by decide)
  exact Q'.eqv_trans _ _ _ e1
    (Q'.eqv_trans _ _ _ e5 (Q'.eqv_trans _ _ _ e6 e7))

/-! ## 3. THE RENORMALON IS SUBDOMINANT BUT OFF-OBJECT (structural re-export).

`exp(−π²/g²) < 2(1 − w)³` for all `w ∈ (0,1)` (mpmath), so the renormalon *ambiguity* is
subdominant everywhere.  But that ambiguity is the resummation UNCERTAINTY of the fixed-sign,
zero-radius field-space series (`FieldSpaceRenormalonZ1`), NOT an upper bound on `Δ`.  We
re-export the proved renormalon signature to make the "wrong object" point machine-anchored. -/

/-- The field-space renormalon coefficients are FIXED sign (positive Borel axis) — the
resummation ambiguity is `∼ exp(−π²/g²)`, subdominant to any polynomial, but only an
ambiguity, not a bound on `Δ`.  (Re-export of `FieldSpaceRenormalonZ1.zAsym_fixed_sign`.) -/
theorem renormalon_fixed_sign :
    ∀ j, j < 14 → (0 : Q') < FieldSpaceRenormalonZ1.zAsym j
      * FieldSpaceRenormalonZ1.zAsym (j + 1) :=
  FieldSpaceRenormalonZ1.zAsym_fixed_sign

/-! ## 4. THE ORDER-COUNTING OBSTRUCTION (the decisive catch, machine-checked).

`w = 9/10`, `c = 1` (a unit second-order correction).  `u = 1/10`, `u² = 1/100`,
`u³ = 1/1000`.  slack `= 2u³ = 2/1000`; correction `c·u² = 10/1000`; δ_free `= 58/1000`;
model `= 60/1000`.  So `c·u² > slack` and `δ_free + c·u² > model`. -/

/-- **`secondOrder_exceeds_slack` — a unit SECOND-order correction exceeds the cubic slack
near `w = 1`.**  At `w = 9/10`: `1·(1 − w)² = 10/1000 > 2/1000 = 2(1 − w)³ = slack`.  A
second-order polynomial interacting piece is NOT subdominant to the third-order free slack —
the renormalon (exp-small) cannot rescue it. -/
theorem secondOrder_exceeds_slack :
    slackExpr (Q'.mkPos 9 10 (by decide))
      < Q'.ofNat 1 * oneSubWSq (Q'.mkPos 9 10 (by decide)) := by decide

/-- **`secondOrder_breaks_model` — a unit second-order correction breaks `realδ ≤ 6(1−w)²`
near `w = 1`.**  At `w = 9/10`: `δ_free + 1·(1 − w)² = 68/1000 > 60/1000 = 6(1 − w)² =
model`.  Since `δ_free` already saturates the model bound to second order, ANY positive
second-order correction violates it on a neighbourhood of `w = 1`; the `w → 1` end of the
subdominance window is NOT auto-closed. -/
theorem secondOrder_breaks_model :
    modelExpr (Q'.mkPos 9 10 (by decide))
      < dfreeExpr (Q'.mkPos 9 10 (by decide))
        + Q'.ofNat 1 * oneSubWSq (Q'.mkPos 9 10 (by decide)) := by decide

/-! ## 5. THE A-PRIORI CHARACTER ROUTE FAILS BELOW `w*` (machine-checked). -/

/-- **`charLead_exceeds_threshold` — the leading character activity already exceeds the Temple
threshold at `w = 13/20 = 0.65 < w*`.**  `coeffW w 1 = 2w³ = 4394/8000 = 0.549` while
`templeThreshold w = 6(1 − w)²(1 − w³) = 0.533`.  Since `coeffW w 1 ≤ plaqActivity w M` (the
other excited terms are `≥ 0`), the a-priori activity bound `plaqActivity ≤ templeThreshold`
FAILS beyond `w_cross ≈ 0.6348`: the only rigorous a-priori upper bound on the interacting
off-diagonal cannot certify closure past `w_cross < w* = 0.7937`. -/
theorem charLead_exceeds_threshold :
    templeThreshold (Q'.mkPos 13 20 (by decide))
      < coeffW (Q'.mkPos 13 20 (by decide)) 1 := by decide

/-! ## 6. THE VERDICT BUNDLE — the crack is refuted (deliverable (iii)). -/

/-- **`SubdominanceVerdict`** — the machine-checked refutation of the free-bound +
renormalon-subdominance crack.  Bundles: the exact free-margin decomposition (slack is purely
cubic), the order-counting break (a unit second-order correction violates the model bound near
`w = 1`), and the a-priori-threshold failure below `w*`.  It inhabits NO guarded Clay-frontier
bundle and produces NO `SingleStepDefectBound`. -/
structure SubdominanceVerdict : Type where
  /-- Exact free-margin decomposition `δ_free + slack ≃ model`; the slack is `2(1 − w)³`. -/
  decomposition : ∀ w : Q', (dfreeExpr w + slackExpr w).eqv (modelExpr w)
  /-- A unit second-order correction exceeds the cubic slack near `w = 1`. -/
  second_order_break : slackExpr (Q'.mkPos 9 10 (by decide))
    < Q'.ofNat 1 * oneSubWSq (Q'.mkPos 9 10 (by decide))
  /-- and pushes `realδ` past the model bound near `w = 1`. -/
  model_break : modelExpr (Q'.mkPos 9 10 (by decide))
    < dfreeExpr (Q'.mkPos 9 10 (by decide))
      + Q'.ofNat 1 * oneSubWSq (Q'.mkPos 9 10 (by decide))
  /-- the rigorous a-priori character route fails already at `w = 13/20 < w*`. -/
  apriori_fail : templeThreshold (Q'.mkPos 13 20 (by decide))
    < coeffW (Q'.mkPos 13 20 (by decide)) 1
  /-- the renormalon is a fixed-sign (positive-axis) ambiguity — subdominant but off-object. -/
  renormalon_offobject : ∀ j, j < 14 → (0 : Q') < FieldSpaceRenormalonZ1.zAsym j
    * FieldSpaceRenormalonZ1.zAsym (j + 1)

/-- **`subdominance_verdict` — non-vacuous inhabitant; every field a PROVED theorem.**  No
frontier bundle inhabited; no `SingleStepDefectBound` produced. -/
def subdominance_verdict : SubdominanceVerdict where
  decomposition := dfree_add_slack_eqv_model
  second_order_break := secondOrder_exceeds_slack
  model_break := secondOrder_breaks_model
  apriori_fail := charLead_exceeds_threshold
  renormalon_offobject := renormalon_fixed_sign

/-! ## 7. Honest verdict (AGENTS.md Rule 6 / Rule 9).

**PROVED (GREEN, axiom-clean):**
  * `dfree_add_slack_eqv_model` — the EXACT free-margin decomposition `6(1−w)² = δ_free +
    2(1−w)³`: `δ_free` saturates the model bound to second order; the slack is purely cubic.
  * `secondOrder_exceeds_slack`, `secondOrder_breaks_model` — a unit SECOND-order interacting
    correction exceeds the cubic slack and violates `realδ ≤ 6(1−w)²` near `w = 1`.
  * `charLead_exceeds_threshold` — the a-priori character-activity bound fails at `w = 0.65 <
    w*` (leading term already over the Temple threshold).
  * `renormalon_fixed_sign` — the renormalon is a fixed-sign resummation ambiguity.

**VERDICT (deliverable (iii)):** the free-bound + renormalon-subdominance crack does NOT close
the `[w*, 1)` window.  The renormalon ambiguity `exp(−π²/g²)` is subdominant to the slack
everywhere on `(0,1)` (mpmath) but is the WRONG object — an uncertainty, not an upper bound on
`Δ`.  The genuine obstruction is order-counting: `δ_free` already saturates `6(1−w)²` to
second order, so the slack budget for `Δ` is only third order `2(1−w)³`; the interacting
multi-plaquette correction is generically second order, violating the bound on a neighbourhood
of `w = 1`.  And the only rigorous a-priori bound (character activity) fails already at
`w ≈ 0.635 < w*` and DIVERGES as `w → 1`.  The windows do NOT overlap; the residual is the
strip `[w_cross, 1) ≈ [0.635, 1)` (rigorously `[5/8, 1)`), with NO renormalon-supplied
`w₁ < 1`.  This is a SHARP negative result; it inhabits NO frontier type and produces NO
`SingleStepDefectBound`.  The 4D Yang–Mills mass gap remains OPEN. -/
theorem subdominanceWindow_honesty : True := trivial

end YMGap.Continuum.SubdominanceWindow

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SubdominanceWindow.const_collapse
#print axioms YMGap.Continuum.SubdominanceWindow.dfree_add_slack_eqv_model
#print axioms YMGap.Continuum.SubdominanceWindow.renormalon_fixed_sign
#print axioms YMGap.Continuum.SubdominanceWindow.secondOrder_exceeds_slack
#print axioms YMGap.Continuum.SubdominanceWindow.secondOrder_breaks_model
#print axioms YMGap.Continuum.SubdominanceWindow.charLead_exceeds_threshold
#print axioms YMGap.Continuum.SubdominanceWindow.subdominance_verdict
