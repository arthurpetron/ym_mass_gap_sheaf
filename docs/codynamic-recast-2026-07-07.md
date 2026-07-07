# Codynamic reflection-unit recast of `singleStep` — adjudication

**Date:** 2026-07-07.
**Deliverable Lean:** `lean/YMGap/Continuum/CodynamicReflectionUnitRecast.lean` (new, imported in `YMGap.lean`).
**Source framework:** Arthur Petron, Codynamic Theory — `theorem5.tex` §"Metric Layer" (Def 4.15 exact soundness, Def 4.16 defect / error profile `ε(X,r)`, Lem 4.18 Lipschitz propagation, Prop 4.19 compositional law, Cor 4.20 n-step Grönwall, **Remark 4.20 "Moduli beyond multiplication"**) and the machine-verified Agda spec (`--safe --without-K`, zero postulates) `agda/Codynamic/{Metric,Trajectory}.agda`.
**Anti-loop status:** NO new `:= SingleStepDefectBound` alias. Delivers **(iii) a machine-checked COLLAPSE** with a sharper structural certificate.

---

## VERDICT (machine-checked)

**(B) / (iii) HONEST COLLAPSE — the codynamic nonlinear-modulus recast does NOT advance the frontier below `singleStep`.**

The recast SPLITS `singleStep` into two codynamic quantities (mirroring the verified Agda `Metric.agda`):
- the **monotone modulus** `scale` (`Lipschitz.lip`: `d(⟦bs⟧xs)(⟦bs⟧ys) ≤ scale(dAll xs ys)`) — the block-spin map's continuity on PAIRS;
- the **reflection-unit defect** `δ_k = d(⟦bs⟧ fine_k, coarse_k)` (`εX`, Agda `wdef`) — the discrepancy at the RECORDED point.

The nonlinear modulus genuinely dissolves the *propagation* obstruction but is **orthogonal** to the *defect*, and the defect bound `εX ≤ 6(1−w)²` pinned to the true margin **equi-inhabits `singleStep`** and requires the interacting a→0 measure. So the modulus recast produces {an independent, non-core-shrinking nonlinear modulus} + {the atomic per-step interacting defect ≡ `singleStep`}. No strictly-weaker computable F-node emerges.

This directly answers the coordinator's (A)/(B): the single-scale content that actually bites (`εX ≤ 6(1−w)²` on the true margin) is the DEFECT, which is **(B)** — collapses to `singleStep` / requires the interacting measure; the modulus half that was hoped to evade the `2w³→2` obstruction is **orthogonal** to the defect and cannot supply it.

---

## What is machine-checked (all `propext`/`Quot.sound` only; full `lake build` GREEN; guard OK at 5)

### 1. Composition is free & genuinely codynamic (Cor 4.20 + Remark 4.20)
Mirroring Agda `Trajectory.agda` `nBound`/`nstep-d` (the left fold `b_{k+1} = scale_k(b_k) + δ_k`):
- `codyFold` + `codyFold_bounds` — the n-step transition for ANY `MonotoneModulus` (no linearity consumed; same induction shape as `nstep-d`).
- `codyFloor` + `codyFloor_lb` — the lower-bound dual (multiplicative margin erosion `∏σ_k·m₀`), the codynamic derivation of the product floor.
- `fullFloor_of_codynamicRecast` — routes `CodynamicMarginRecast` into the EXISTING positive continuum floor (`fullFloor_of_singleStep` → `afFloorEps`/`DefectGapRecursion` product floor). Genuine, but this floor was already available; the codynamic account is cleaner, not new closure.

### 2. The propagation obstruction is a LINEAR-modulus artifact (Remark 4.20 payoff)
- `singleEdgeFactor_expansive_at_weak` : `2·(9/10)³ = 1458/1000 ≥ 1` — `DirectSingleStepReconGap`'s `2w³ → 2 > 1` failure, isolated as a statement about the LINEAR modulus (single-edge excited eigenvalue / Lipschitz constant).
- `singleEdge_matches_reconGap` : this IS `DirectSingleStepReconGap.rho_ge_one_at_weak` (non-vacuity cross-check).
- `contractiveModulus_nonexpansive` : a monotone modulus `scale(x)=x/2` with `scale(x) ≤ x` — non-expansive monotone moduli EXIST, so the fold CAN be bounded. The `2w³→2` obstruction was an artifact of insisting on the linear single-edge eigenvalue; the nonlinear degree of freedom is real.

### 3. THE CRUX — the DEFECT is ORTHOGONAL to the modulus (the collapse)
Two `ReflectionStep`s with the SAME (identity) modulus but DIFFERENT defects, over a decidable two-point metric:
- `orthoBig_defect_exceeds_bound` : the IDENTITY modulus (a valid, computable, nonlinear-general monotone modulus) has defect `2 > 6·(1−½)² = 3/2` — a modulus bound (even the tightest, the identity) does NOT imply `δ_k ≤ 6(1−w)²`.
- `modulus_underdetermines_defect` : `orthoStepBig.modulus = orthoStepZero.modulus ∧ orthoStepBig.defect ≠ orthoStepZero.defect` (`2 ≠ 0`). The reflection defect is NOT a function of the modulus. Hence "compute the block-spin monotone modulus `scale`" is INDEPENDENT of the defect bound — a genuine object but NOT core-shrinking (structurally parallel to `uniform_in_m`, `docs/adjudicate-2026-07-07.md`).

  *Why orthogonal:* in Agda `nBound` the modulus `scale` and the defect summand `d(stepF y, rec)` are SEPARATE additive fields. A map can be an isometry (`scale = id`, perfect continuity) yet have arbitrary defect `d(⟦bs⟧ fine, coarse)`; the modulus controls how the step SPREADS existing error, never the defect it INTRODUCES.

### 4. The single-scale DEFECT obligation EQUI-INHABITS `singleStep`
- `singleStep_of_codynamicRecast` : `CodynamicMarginRecast → SingleStepDefectBound` (PROVED via the fold: from `reflDefect_k ≤ δ_model_k` and `tm ≥ 0`, `(1−δ_model_k)tm_k ≤ (1−reflDefect_k)tm_k ≤ tm_{k+1}`). The reduction `newObligation → singleStep`.
- `codynamicRecast_of_singleStep` : the CONVERSE on `tm ≥ 0` (take `reflDefect := afDefectSeq`; (b) is `le_refl`, (a) is verbatim `singleStep`).
- Together ⟹ **equi-inhabitation (ALIAS)** on the physical domain: the reflection defect bound `εX ≤ 6(1−w)²` pinned to the TRUE margin is NOT strictly weaker; it is the atomic core, reproducing `real_defect_identification` of the prior adjudication. By Def 4.16 the defect `d(⟦bs⟧ fine, coarse)` requires the interacting block-spin map `⟦bs⟧` = the unconstructed a→0 measure.

---

## Adversarial self-check (mandatory)
- **Did I inhabit `SingleStepDefectBound`?** NO. It appears only as the codomain of the conditional producer `singleStep_of_codynamicRecast (R : CodynamicMarginRecast) → …` — an open hypothesis, not unconditional.
- **Did I inhabit `CodynamicMarginRecast`?** NO. Its only producer `codynamicRecast_of_singleStep` takes `S : SingleStepDefectBound` + `tm ≥ 0` (open). No 0-hypothesis inhabitant of either exists.
- **Guard:** `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`. Did NOT break — correct for a collapse (per the task criterion, guard-not-breaking = `singleStep` NOT inhabited).
- **No dodges:** the modulus is not `trivial` (identity + linear + contractive, all with real `mono`/`base`); the defect is not `0` (the counterexample defect is `2`); the metric is a genuine decidable two-point space; the reduction is a real inequality chain, not an alias.
- **`#print axioms`** on all 10 load-bearing declarations: `propext`/`Quot.sound` only (2 axiom-free: `singleEdgeFactor_expansive_at_weak`, `singleEdge_matches_reconGap`). No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx`, no `ring`.
- **Full `lake build`:** GREEN.

---

## Consequence for the solve path
The codynamic recast is a POSITIVE structural result — it cleanly separates `singleStep`'s two ingredients, proves the composition/propagation categorically for free, and shows the `2w³→2` obstruction is a linear-modulus artifact — but it does NOT advance `F` below `singleStep`. The residual is EXACTLY the per-step reflection-unit defect `δ_k = d(⟦block-spin⟧ fine_k, coarse_k) ≤ 6(1−w_k)²`, which is the interacting block-spin RG map evaluated on the true configuration (the a→0 object). The modulus is a new independent, non-core-shrinking object; attacks on it are provably not core-shrinking. The only non-loop attacks remain (a) the direct atomic per-step interacting defect (the true-margin construction + its recursion), or (b) a genuinely-new reduction below it — of which the nonlinear modulus is NOT one.
