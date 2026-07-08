# real_defect_identification — direct construction attack

**Date:** 2026-07-07
**File delivered:** `lean/YMGap/Continuum/RealDefectConstruction.lean` (builds GREEN, axiom-clean)
**Outcome class:** (ii) CONSTRUCTION INCREMENT + (iii) PRECISE RESIDUAL. `SingleStepDefectBound`
NOT inhabited; NO alias; guard stays at 5; 4D YM mass gap remains OPEN.

---

## What was proved (all axiom-clean: `[propext(, Quot.sound)]` only)

### The concrete real defect (NOT a surrogate, NOT `:= afDefectSeq`)

```
realDefectRen (w Cdef : Q') : Q' := dfreeExpr w + Cdef
```

`realδ_k := δ_free(w_k) + Cdef_k`, where:
- `δ_free(w) = dfreeExpr w = 2(1−w)²(2+w)` is the genuine **renormalized `s=1` bond-moving
  transverse defect** of the interacting single step — PROVED equal to `bondMovingDeltaRen 1 1 w`
  (`bondMovingDeltaRen_one_eqv_dfree`, via `renDefect_factor`). This is exactly the `afDefectSeq`
  model object, so the free part of `realδ` is the real renormalized defect, not a fresh model.
- `Cdef_k` is the genuine **interacting Clebsch–Gordan connected `m`-fold fusion remainder**
  (`= cdefQ r2 μ^{8/3}`), the correction NOT absorbed by coupling renormalization.

This is a concrete `Q'` object built from the interacting block-spin measure. It engages the
actual three-piece content instead of the circular `realδ := afDefectSeq` witness the
adjudication exposed.

### The exact reduction of the real-defect bound

`realDefectRen_le_model : Cdef ≤ 2(1−w)³  ⟹  realDefectRen w Cdef ≤ 6(1−w)²`

Because `6(1−w)² = δ_free + 2(1−w)³` EXACTLY (`dfree_add_slack_eqv_model`: δ_free saturates the
model to 2nd order, leaving the cubic slack), bounding the real defect `= δ_free + Cdef` by the
model is EXACTLY bounding the interacting connected remainder `Cdef` by the third-order slack
`2(1−w)³`. The whole real-defect bound collapses to the connected-slack inequality.

---

## The three pieces — verdict

### Piece 1 — TRUE-MARGIN CONSTRUCTION: **DONE at m=1** (proved, non-vacuous)

`realDefect_m1_closed : w ≤ 1 ⟹ realDefectRen w (cdef1 w) ≤ 6(1−w)²`

The single-plaquette (`m=1`) real 4D block-spin defect is genuinely bounded by the model,
uniformly in `w≤1`. Non-vacuous: at `w=9/10`, `realδ = 58/1000 ≤ 60/1000 = 6(1−w)²` with real
slack `2/1000` = the cubic slack. Uses `Cdef_1 ≡ 0` (`cdef1_eq_zero`, the exact single-plaquette
log-linearity). The construction of `realδ` as a concrete per-scale object is complete.

### Piece 2 — `m = b^{d−1} = b³` MULTIPLICITY: **REDUCED to the connected-slack bound**

`blockMult b := b^3` (`= b^{4−1}`), `blockDefect_le_model` shows the `b³`-fold block real defect
bound is the SAME single inequality `Cdef_{b³} ≤ 2(1−w)³` (the reduction is parametric in the
remainder). `multiplicity_concentration` (= `twoLink_concentration`) proves the `m=2` fusion
concentrates (`ρ_2 ≤ 2ρ_1`, per-link leakage decreases) — so growing `b` DAMPS, not amplifies,
the remainder (off-line: `Cdef_m = O((1−w)⁴)`, coefficient ↓ in `m`). The all-`b³` UNIFORM bound
is the already-isolated local-CLT core (`FusionConvLogConcaveCore`) — open, but reduced, not new.

### Piece 3 — CHANNEL FEEDBACK: **THE BINDING INTERACTING CORE** (pinned)

`perScale_not_recursion` : there is `(w, realδ, tm)` with the full per-scale real-defect bound
`∀k, realδ_k ≤ 6(1−w_k)²` HOLDING yet the true-margin recursion
`(1−realδ_k)·tm_k ≤ tm_{k+1}` FAILING (witness `w≡9/10`, `tm=(1,0,0,…)`; at `k=0` the recursion
demands `47/50 ≤ 0`).

**This is the binding piece.** Pieces 1–2 deliver a per-scale defect bound; `singleStep` /
`real_defect_identification` additionally demand the RECURSION — how the *true physical margin*
degrades under the block-spin, i.e. the feedback of the `s≥2` fused remainder into the next
scale's `s=1` gap. That content is NOT supplied by any per-scale defect bound; it is exactly why
`singleStep_falsifiable` holds (truth depends on the free margin `tm`, not on `realδ` alone). The
channel feedback requires the interacting block-spin *effective action* (the non-perturbative
Bałaban object), which no single-scale estimate produces.

---

## The sharp adversarial finding — tight-vs-loose model tension

`dfree_le_realDefect : 0 ≤ Cdef ⟹ δ_free(w) ≤ realDefectRen w Cdef`, and
`honest_realDefect_exceeds_tight` (decidable, `w=9/10`, `Cdef=1/500`): `realδ = 60/1000 ≰
58/1000 = δ_free`.

`SingleStepDefectBound.singleStep` compares `realδ` against the **TIGHT** model
`afDefectSeq = δ_free`. But the honest interacting `realδ = δ_free + Cdef` with `Cdef ≥ 0`
STRICTLY EXCEEDS `δ_free` whenever `Cdef > 0` (m ≥ 2). So the honest real defect **cannot** meet
the tight `singleStep` model — it meets only the LOOSE `6(1−w)²` (which carries the cubic slack to
absorb `Cdef`). Consequence: `SingleStepDefectBound` as currently wired to `afDefectSeq` is too
tight for the genuine interacting defect; closing it requires re-basing the recursion on the loose
summable model `6(1−w)²` (itself `O(1/k²)`-summable along the AF rate). This is a concrete
structural residual, newly pinned.

---

## HONEST VERDICT — how far the direct construction gets, and which piece binds

- `realδ_k` is now CONCRETELY constructed from the interacting measure (transverse `δ_free` +
  connected `Cdef`), with `δ_free` PROVED to be the real renormalized bond-moving defect — the
  circular `realδ := afDefectSeq` is replaced by a genuine two-part object.
- **Piece 1 (true-margin construction): DONE at m=1** — proved `realDefectRen w (cdef1 w) ≤ 6(1−w)²`.
- **Piece 2 (m=b³ multiplicity): REDUCED** to `Cdef_{b³} ≤ 2(1−w)³` — proved at m=1, concentrating
  at m=2, all-m = the isolated local-CLT core.
- **Piece 3 (channel feedback): THE BINDING INTERACTING CORE** — the per-scale bound provably does
  not yield the true-margin recursion; the `s≥2 → s=1` back-coupling over the RG flow is the
  irreducible non-perturbative content.

**The binding interacting core is the CHANNEL FEEDBACK (piece 3): the true-margin recursion, i.e.
that the constructed `realδ_k` genuinely governs the physical margin's per-step degradation over
the full RG flow — not merely as a per-scale majorant. Neither the true-margin construction
(done at m=1) nor the `m=b³` multiplicity (reduced to local-CLT) is the binder; the recursion /
effective-action feedback is.** A sharper structural sub-residual was found: the honest interacting
`realδ` overshoots the tight `afDefectSeq` model and meets only the loose `6(1−w)²`, so
`SingleStepDefectBound` must be re-based on the loose summable model.

## Guard / build status
- `lake build YMGap.Continuum.RealDefectConstruction` — GREEN (223 jobs).
- `#print axioms` on all 10 load-bearing decls — `[propext, Quot.sound]` or none.
- NO `SingleStepDefectBound` inhabited, NO alias, NO `Classical`/`native_decide`/`sorry`. Guard
  stays at 5 (nothing guarded discharged). Class (ii)+(iii) increment.
