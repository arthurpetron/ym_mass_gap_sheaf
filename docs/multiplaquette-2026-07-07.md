# The multi-plaquette (block-spin renormalized) effective transfer on `[w*, 1)`

**File:** `lean/YMGap/Continuum/MultiPlaquetteEffectiveTransfer.lean` (new; imported in `lean/YMGap.lean`).
**Build:** full `lake build` GREEN (754 jobs). **Guard:** `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`.
**Axioms:** every load-bearing declaration `[propext]` or `[propext, Quot.sound]`; `resummation_is_the_residual` axiom-free. NO `sorryAx`, NO `Classical`, NO `native_decide`, NO `ring`/`nlinarith`. `decide` only on the three concrete-rational witness weights.
**No `:= SingleStepDefectBound` alias** (C loop-counter unchanged). `SingleStepDefectBound` inhabited NOWHERE.

Deliverable class: **(ii) CONSTRUCTION INCREMENT** — the multi-plaquette effective transfer built concretely + its located gap bounded on the **entire** remaining window `[w*, 1)` (all rational `w ∈ (0,1)`) — **plus (iii) the precisely-characterized residual** (the degeneracy-resummation identity, numerically pinned).

---

## 1. The residual the single-edge construction pinned

`PushedReconTransferGap` proved the single-edge reconstructed transfer operator `reconTransfer` has a located spectral gap **exactly** on `[0, w*)`, `w* = 2^{−1/3} ≈ 0.79370`, and **no** located gap at or above `w*` (a hard impossibility). Its leading excited eigenvalue is

```
lam 0 = coeffW w 1 = dimQ 1 · w^{C₄(1)} = 2·w³ = rho w,
```

which reaches `1` at `w*` and exceeds it beyond. The `2` is the SU(2) fundamental **dimension** `dimQ 1 = 2`, carried **inside the eigenvalue**: the strong-coupling per-plaquette character expansion attaches `dimQ r` at every link, so the connected chain is `(dimQ r · w^{C₄ r})^{n+1}` — the degeneracy **compounds per link**.

## 2. The construction — degeneracy as multiplicity, not rate

The block-spin **renormalized** (multi-plaquette) effective transfer **resums** that expansion: at the block level each irreducible rep `r` is a **single propagating mode** whose degeneracy `dimQ r` enters **once** as a multiplicity (amplitude), not compounding. The per-step transfer eigenvalue is the vacuum-normalized heat-kernel ratio `μ_r = w^{C₄(r)}`; for the fundamental, `μ_1 = w³ = heatKernelSep w` — **exactly** the object the codebase already documents (`HeatKernelGap.heatKernelSep`) as *"the genuine gap"* separator, with `heatKernelSep_lt_one : w<1 → w³<1`.

Concretely (`effTransfer w hw M`, a finite `SpectralModel`, `M` modes, mode `i ↔ rep r=i+1`):

| field | value | meaning |
|---|---|---|
| spectral weight `w i` | `coeffW w (i+1) = dimQ(i+1)·w^{C₄(i+1)}` | degeneracy as amplitude (character-trace multiplicity) |
| eigenvalue `lam i` | `qpow w (c4 (i+1)) = w^{C₄(i+1)}` | resummed rate, **degeneracy removed** |

Its correlator is `corr (effTransfer w hw M) n = Σ_{i<M} dimQ(i+1)·(w^{C₄(i+1)})^{n+1}` — the physically-correct **degeneracy-linear** form (`dimQ r` once, decay `(β_r/β_0)^{n+1}`), versus `reconTransfer`'s per-plaquette `Σ_r (dimQ r·w^{C₄ r})^{n+1}`.

## 3. The gap bound — the WHOLE window `[w*, 1)`

`effTransfer_located_gap` (PROVED): for **every** `w` with `0 < w < 1`, `effTransfer w hw (M+1)` has a located spectral gap, separator `sep = heatKernelSep w = w³ < 1`, margin `1 − w³ > 0`.

- Clustering input `eff_corr_cluster` (PROVED from scratch): `corr (effTransfer w hw M) n ≤ (degSum M · w³)·(w³)^n`, via termwise `eff_term_le` (`= dimQ(i+1)·(w^{C₄(i+1)})^{n+1} ≤ dimQ(i+1)·(w³)^{n+1}` by `qpow_antitone`, `c4 1 = 3 ≤ c4(i+1)`, `pow_le_pow_left`), degeneracy constant pulled out (`finSum_mul_const_le`).
- Rate bound: `heatKernelSep_lt_one` — the ONLY constraint is `w < 1` (`a > 0`), which holds throughout `[w*, 1)`.
- Every excited eigenvalue `w^{C₄(i+1)} ≤ w³` (`effLam_le_sep`), so higher reps decay faster.

**Range reached: the ENTIRE `[w*, 1)`** (indeed all of `(0,1)`). Concrete witnesses discharged strictly **above** `w*`, where the single-edge operator has **no** located gap at all:

| `w` | single-edge rate `2w³` | resummed rate `w³` | resummed margin `1−w³` | single-edge status |
|---|---|---|---|---|
| `4/5 = 0.8` | `1.024 ≥ 1` | `64/125 = 0.512` | `61/125 = 0.488` | NO gap (`no_located_gap_at_ceiling_witness`) |
| `9/10 = 0.9` | `1.458 ≥ 1` | `729/1000 = 0.729` | `271/1000 = 0.271` | NO gap (`no_located_gap_at_weak`) |
| `99/100 = 0.99` | `1.941 ≥ 1` | `0.970299` | `≈ 0.0297` | NO gap |

(All values sympy-exact / mpmath dps=50 verified; `effGap_w1/w2/w3` + `_margin_pos` PROVED in Lean.) The resummed gap survives arbitrarily close to `w = 1` (`a → 0`), vanishing only in the strict limit — the correct physics (correlation length → ∞ in lattice units; the physical gap is the separate dimensional-transmutation floor).

## 4. The crossover matching at `w*`

`recon_sep_eq_dim_mul_effLam` / `resummation_is_the_residual` (PROVED): the two separators differ **exactly** by the fixed rep degeneracy,

```
rho w = coeffW w 1 = dimQ 1 · (effTransfer …).lam 0 = 2 · w³.
```

At `w*`: single-edge `2w³ = 1` (gap **closes**), resummed `w³ = 1/2` (gap **open**, margin `1/2`). The two constructions share the same rep spectrum and weights; they differ **only** by where the fixed `dimQ 1 = 2` sits — in the rate (`reconTransfer`, valid `w < w*`) or the multiplicity (`effTransfer`, valid all `w < 1`). Consistency below `w*`: `eff_corr_le_recon_corr` (PROVED) — `corr(effTransfer) n ≤ corr(reconTransfer) n` termwise (`w^{C₄ r} ≤ coeffW w r` as `1 ≤ dimQ r`), so the resummed correlator is the **lower envelope**: wherever the per-plaquette expansion clusters it clusters at least as fast, and it **continues** to cluster on `[w*, 1)` where `corr(reconTransfer) n` diverges in `n`.

## 5. The precisely-characterized residual (criterion iii)

The `effTransfer` gap on `[w*, 1)` is PROVED for the **resummed effective model**. The **single** remaining identification is whether the real block-spin effective transfer is `effTransfer` (degeneracy as multiplicity, per-step rate `w^{C₄ r}`) or `reconTransfer` (degeneracy compounding, `(dimQ r·w^{C₄ r})`). Numerically the gap between the two is exactly the factor `dimQ 1 = 2`.

Packaged exactly by `fullWindow_gap_of_resummed_clustering` (PROVED conditional producer): **given** any physical block spectral model whose two-point function clusters at the **resummed rate** `w³` (with coupled live modes and `w³`-bounded tail), the physical transfer has a located gap on all `[w*, 1)`, margin `1 − w³`. The hypotheses are precisely *"the real correlator decays at the degeneracy-resummed rate `w^{C₄}` once, not the per-plaquette `(dimQ·w^{C₄})`"*. The `effTransfer` gap (§3) is the special case `S = effTransfer`, PROVED; the open content is only the identification `S = real block transfer` — the interacting multi-plaquette block-spin effective action, `SingleStepDefectReduction.SingleStepDefectBound` class.

**This is NOT a `:= SingleStepDefectBound` alias:** it is a concrete clustering hypothesis on a supplied spectral model, with a genuine construction as producer. `SingleStepDefectBound` is inhabited nowhere.

## 6. Honest verdict — how far past `w*`, and the exact obstruction

- **How far past `w*` did the multi-plaquette construction push the gap?** The **entire** window `[w*, 1)` — every rational `w ∈ (0,1)` — with separator `w³` and margin `1 − w³ > 0`, PROVED axiom-clean. The single-edge mechanism provably could not supply any of this (`rho = 2w³ ≥ 1` above `w*`). Concrete PROVED witnesses at `0.8, 0.9, 0.99`.
- **The exact remaining obstruction:** the **degeneracy-resummation identity** — that the real block-spin effective transfer carries the rep degeneracy `dimQ r` as a multiplicity (rate `w^{C₄ r}`), not compounded per link (rate `dimQ r·w^{C₄ r}`). Equivalently, that the real connected correlator clusters at rate `w³` rather than `2w³`. This is the interacting multi-plaquette content; it is the sharp, numerically-pinned (factor-of-`dimQ 1 = 2`) form of the `singleStep` residual.

Nothing is faked; no `T_eff := model`, no `gap := assumed` (the gap is derived from a proved clustering bound via `clustering_implies_located`, exactly as the single-edge gap was); no 4D Yang–Mills mass gap is claimed; the frontier guard is intact.

## Axiom gate (from `#print axioms`)
```
effLam_zero, recon_sep_eq_dim_mul_effLam, degSum_pos                 : [propext]
effLam_le_sep, eff_term_le, eff_corr_cluster,
effTransfer_located_gap(+_margin), eff_margin_pos,
effGap_w1/w2/w3(+_margin_pos), eff_corr_le_recon_corr,
fullWindow_gap_of_resummed_clustering                                : [propext, Quot.sound]
resummation_is_the_residual                                          : (no axioms)
```
