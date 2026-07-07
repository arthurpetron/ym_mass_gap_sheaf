# Direct attack on the atomic core `SingleStepDefectBound` via the PROVED reconstructed transfer gap

**Date:** 2026-07-07.
**Deliverable Lean:** `lean/YMGap/Continuum/DirectSingleStepReconGap.lean` (new, imported in `YMGap.lean`).
**Result type:** ONE genuine NEW CONSTRUCTION lemma + a machine-checked OBSTRUCTION.
**NOT delivered:** no `:= SingleStepDefectBound` alias; `SingleStepDefectBound` inhabited NOWHERE.

---

## 1. The exact `SingleStepDefectBound` requirement (read from source)

`SingleStepDefectReduction.SingleStepDefectBound : Type` has fields:

- `afr : AFRateModulus` — supplies the PROVED model defect `δ_model_k = afDefectSeq afr k` (its `δ<1`, `≥0`, and summable product floor are all proved).
- `trueMargin : Nat → Q'` — a **FREE** sequence (the dimensionless margin `m_lat(a_k)/a_k`).
- `trueMargin0_pos : 0 < trueMargin 0` — a positive anchor.
- **`singleStep : ∀ k, (1 − afDefectSeq afr k) · trueMargin k ≤ trueMargin (k+1)`** — the ONE open per-step RG estimate (`realδ_k ≤ δ_model(w_k)` in recursion form).

A concrete inhabitant needs a concrete `trueMargin : Nat → Q'`, positive at `k=0`, satisfying the recursion for **every** `k`. `defectRecursion_of_singleStep` then fills every other `DefectGapRecursion` field from proved lemmas, and `fullFloor_of_singleStep` yields the entire positive continuum floor. So `singleStep` is the atomic Clay-continuum residual (`docs/adjudicate-2026-07-07.md`: `channel_feedback`/`real_defect_identification` are aliases; `F=1`).

## 2. The PROVED fixed-spacing content used

`MayerClustering.reconTransfer_located_gap M : LocatedSpectralGap (reconTransfer gw gw_nonneg (M+1))` at the strong-coupling anchor `w = gw = 1/6`, with `sep = rho gw = coeffW gw 1 = 2·(1/6)³ = 1/108`, margin `gapMargin = 1 − rho gw = 107/108`. Its clustering input is the REAL Wilson connected-correlator decay `wilsonG_decay` (transported through `wilsonG_eqv_reconTransfer_corr`) — genuine reconstruction content, not a model. Crucially this is proved at ONE fixed weight; and `reconTransfer_corr_decay`/`rho_lt_one` require `w ≤ 1/2`.

## 3. GENUINE CONSTRUCTION (new, from proved objects)

`reconTransfer_located_gap_general {w} (hwpos : 0<w) (hwh : w ≤ 1/2) (M) : LocatedSpectralGap (reconTransfer w (le_of_lt hwpos) (M+1))`, `sep = rho w = 2w³ < 1`.

This **generalizes `reconTransfer_located_gap` off the fixed anchor `w=1/6` to the entire strong-coupling window `w ∈ (0,1/2]`** — a real new object, not an alias/restatement. The clustering (`reconTransfer_corr_decay`) and rate (`rho_lt_one`) already hold for all `w ≤ 1/2`; the one genuinely new supporting lemma is the general excited-weight positivity `coeffW_pos {w} (0<w) : 0 < coeffW w (i+1)` (generalizing the anchor-only `coeffW_gw_pos`). It yields the per-scale candidate margin `reconMargin w := 1 − rho w = 1 − 2w³`, with:

- `reconTransfer_located_gap_general_margin` : the gap's margin **is** `reconMargin w` (`rfl`).
- `reconMargin_pos {w} (0<w) (w≤1/2) : 0 < reconMargin w` (via `rho_lt_one`).
- `reconMargin_anchor : reconMargin gw = 1 − rho gw` and `reconMargin_anchor_ge_half : 1/2 ≤ reconMargin gw` (= 107/108) — ties the construction to the proved anchor (non-vacuity).

## 4. MACHINE-CHECKED OBSTRUCTION — why this cannot inhabit `singleStep`

The AF/RG flow drives `w_k → 1` in the deep UV (asymptotic freedom). The direct route would set `trueMargin_k := reconMargin(w_k)`. But the reconstructed single-edge margin — the **only** margin the proved fixed-spacing located gap supplies — provably FAILS at weak coupling. Pinning the concrete deep-UV weight `wWeak = 9/10` (`> 1/2`):

- `rho_ge_one_at_weak : 1 ≤ rho wWeak` — `rho(9/10) = 2·(9/10)³ = 1458/1000 = 1.458 ≥ 1`. The located-gap separator requirement `sep < 1` is **unsatisfiable**.
- `reconMargin_neg_at_weak : reconMargin wWeak < 0` — `1 − 2w³` inverts for `w ≥ (1/2)^{1/3} ≈ 0.794`; **not a positive margin**.
- `no_located_gap_at_weak (M) : LocatedSpectralGap (reconTransfer wWeak _ (M+1)) → False` — a **hard impossibility**: any such gap forces `lam 0 = coeffW wWeak 1 = rho wWeak ≤ sep < 1`, contradicting `rho wWeak ≥ 1`.
- `direct_route_obstruction` — the three bundled as one axiom-clean certificate.

All `by decide` / proved, so genuinely true, not a proof weakness.

**Precise named missing object:** a located gap of the transfer operator at **weak coupling** `w_k → 1`. The single-edge strong-coupling reconstruction cannot supply it (its leading excited eigenvalue `rho = 2w³ → 2 > 1`, so the naive single-edge/strong-coupling-expansion transfer operator has no spectral gap there). Continuing the 107/108 gap from the strong-coupling anchor up the RG trajectory to the continuum requires the **interacting block-spin effective action at each scale** — precisely the unconstructed `a→0` object. This is not routed through any surrogate interacting measure; it is the exact identification of the object that is missing.

## 5. Adversarial self-check (mandatory)

- **Did I inhabit `SingleStepDefectBound`?** NO. It appears only in prose docstrings; there is no `def _ : SingleStepDefectBound` anywhere in the file.
- **Guard:** `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited` — the guard did **not** break (stays at 5). Per the task's criterion §4, guard-not-breaking = `singleStep` NOT inhabited. Correct and honest — the deliverable is a construction+obstruction, not a closure.
- **`#print axioms`** on all 10 load-bearing declarations: `propext` / `Quot.sound` only (5 are axiom-free). No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx`, no `ring`.
- **Non-vacuity:** `reconTransfer_located_gap_general` is a real inhabitant (instantiable at `w=1/6` to recover the proved anchor); `no_located_gap_at_weak` is a genuine impossibility (leading eigenvalue 1.458 > 1); the arithmetic is `decide`-verified.
- **Full `lake build`:** GREEN (exit 0).

## 6. HONEST VERDICT

The direct route **ADVANCED the construction** (fixed-anchor located gap generalized to the whole strong-coupling window `w ≤ 1/2` — a real new object with per-scale margin `1 − 2w³`) but **did NOT inhabit `SingleStepDefectBound`, and provably CANNOT via this object.** The machine-checked obstruction is that the reconstructed single-edge margin goes negative and its located gap ceases to exist exactly where `singleStep` bites (the deep UV `w_k → 1`). The specific unconstructed object blocking closure is the **weak-coupling located transfer gap / interacting block-spin effective action** — not the single-edge reconstruction. No new alias; `singleStep` remains the atomic open core (`F=1`), now with a sharper machine-checked reason why the direct fixed-spacing-gap route alone is insufficient.
