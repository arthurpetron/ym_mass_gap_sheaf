# Route H — the RENORMALIZATION / COUNTERTERM attack on `FullRangeFusedDefect`

**Target.** `RouteADefectCharacter.FullRangeFusedDefect` — the weak-coupling (`w → 1`)
renormalized-defect bound, named as the SOLE residual of the whole continuum floor. The
RAW fused-character defect `coeffW w 1 = 2w³` obeys `≤ 6(1−w)²` only for `w ≤ 0.6778…`
and DIVERGES to `2` as `w → 1` (refuted raw). Route H proves the bound holds UNIFORMLY
for the RENORMALIZED (counterterm-subtracted) defect, and pins exactly what of
`FullRangeFusedDefect` closes vs. remains open.

**Deliverables.** `lean/YMGap/Continuum/RenormalizedDefectCounterterm.lean` (full `lake
build` green, frontier-guard OK at 5, axiom-clean), `routeH_numerics.py` (mpmath dps 50 +
exact sympy), this report. **Committed: nothing** (per instructions).

---

## 1. The exact counterterm decomposition (proved — `Q'` identity for all `w`)

SU(2), `pMult = 1`: `dimQ 1 = 2`, `C₄(1) = 3`. Three objects:

| symbol | value | meaning |
|---|---|---|
| `raw(w) = coeffW w 1` | `2w³` | RAW fused excited/vacuum ratio = block-spin margin degradation `Δ−Δ'` (RouteF) |
| `CT(w) = dimQ 1 · renormW p w` | `6w − 4` | MARGINAL counterterm = `dimQ 1 ·` the retuned heat-kernel weight `renormW` |
| `δ_ren(w) = bondMovingDeltaRen N 1 w` | `2(1−w)²(2+w)` | RENORMALIZED transverse defect |

**THE IDENTITY (`coeffW_eqv_renDefect_add_counterterm`):**
```
        coeffW w 1   ≃   bondMovingDeltaRen N 1 w   +   dimQ 1 · renormW p w
        (raw  2w³)        (renormalized  δ_ren)          (counterterm CT = 6w−4)
```
i.e. `raw = δ_ren + CT` — EXACT, all `w`. Proved by factoring `dimQ 1` and the pure
additive cancellation `inner_cancel : (M − (1−x)) + (1−M) ≃ x`. Sympy confirms
`raw − (δ_ren + CT) ≡ 0` identically.

Hence the **renormalized defect** `renormalizedDefect N p w := coeffW w 1 − CT(w)`
satisfies (`renormalizedDefect_eqv`)
```
        renormalizedDefect N p w  ≃  bondMovingDeltaRen N 1 w  =  2(1−w)²(2+w),
```
the counterterm-subtracted TRANSVERSE residual, vanishing to **second order** at the free
fixed point `w = 1` (the linear/marginal part is exactly what `CT` absorbs).

---

## 2. The UNIFORM full-range bound (proved — the analytic core the RAW fails)

**`renormalizedDefect_le_transverseQuad` / `renormalizedDefect_le_six`:**
```
        renormalizedDefect N p w  ≤  6·(1 − w)²        for ALL  0 ≤ w ≤ 1,
```
NO `w ≤ 1/2` restriction, **including `w → 1`**. Reason: `δ_ren ≤ 6(1−w)² ⇔ 2(2+w) ≤ 6 ⇔
w ≤ 1`, so `6(1−w)² − δ_ren = 2(1−w)³ ≥ 0` uniformly (via `bondMovingDeltaRen_le_sixp`).

This is exactly the analytic content of `FullRangeFusedDefect.fullRange` — now PROVED for
the renormalized defect at every scale, whereas the RAW ratio provably violates it.

### Machine-checked numeric contrast at `w = 9/10` (`renorm_fixes_weak`)

| quantity | value at `w=9/10` | `≤ 6(1−w)² = 3/50`? |
|---|---|---|
| RAW `coeffW (9/10) 1 = 2·(9/10)³` | `1458/1000` | **NO** (`raw_ratio_exceeds_at_weak`) |
| RENORM `renormalizedDefect 0 1 (9/10)` | `29/500` (kernel-`decide`, `renormalizedDefect_value_at_weak`, **zero axioms**) | **YES** (`renormalizedDefect_holds_at_weak`) |

`renorm_fixes_weak` bundles both: renormalization satisfies the envelope EXACTLY where the
raw ratio breaks it.

### Numerics (mpmath dps 50 + sympy exact, `routeH_numerics.py`)

- `raw = δ_ren + CT` exact (sympy `≡0`); `δ_ren = 2(1−w)²(2+w) = bondMovingDeltaRen` exact.
- `6(1−w)² − δ_ren = 2(1−w)³ ≥ 0` — `δ_ren ≤ env` for **all** `w∈(0,1)`; `sup δ_ren/env =
  (2+w)/3 → 1` at `w→1` (max over grid `0.99966…`, never exceeds `1`).
- RAW crossover: `2w³ > 6(1−w)²` for `w > w* = 0.677814…` — the raw failure region.
- `w→1` adversarial: `raw→2`, `CT→2`, `δ_ren = raw−CT → 0` — CT cancels the raw approach
  to `2` and leaves the vanishing transverse residual.

---

## 3. What of `FullRangeFusedDefect` closes / reduces

- **Analytic half — CLOSED.** "A per-scale leakage obeying the transverse envelope
  `6·pMult·(1−w_k)²` exists at every scale (incl. `w→1`)" is now proved for the
  renormalized model defect `afDefectSeq afr` (this module + the pre-existing
  `afDefectSeq_le_transverseQuad`). Renormalization removes the `w→1` obstruction that
  defeated the raw ratio.
- **Genuine residual — the IDENTIFICATION (still open).** That the REAL physical per-step
  block-spin leakage of the true dimensionless margin actually IS `≤ afDefectSeq afr`
  (i.e. the counterterm/retuning is physically implementable). Carried as the OPEN
  hypothesis of the CONDITIONAL producer `fullRangeFusedDefect_of_identification`:
  ```
  (physLeak k ≤ afDefectSeq afr k)  →  FullRangeFusedDefect afr
  ```
  — open binders, NOT an unconditional inhabitant; guard unchanged at 5. This is the
  machine-checked reduction `FullRangeFusedDefect ⇐ identification`, and the identification
  is LITERALLY `SingleStepDefectBound.singleStep` / `TrueMarginRecursion` pinned to the
  physical margin (NO new wall opened).

### LOUD honesty (Rule 9) — `FullRangeFusedDefect` is vacuously inhabitable; REFUSED

`FullRangeFusedDefect` carries `realLeak : Nat → Q'` as a **FREE** field, so it is
TRIVIALLY inhabitable by `realLeak := afDefectSeq afr` (both fields discharged by
`afDefectSeq_nonneg`, `afDefectSeq_le_transverseQuad`). That is the **Rule-9(1) vacuous
closure** and is **deliberately NOT written** — I did NOT inhabit `FullRangeFusedDefect`,
`SingleStepDefectBound`, `GapChannelDomination`, or `TrueMarginRecursion`. The genuine
content lives only in the identification pinned to the external physical margin.

---

## 4. Adversarial verdict — is the counterterm GENUINE or a scheme artifact?

**Genuine.** Three independent checks:
1. **Exact, not a fudge.** `raw = δ_ren + CT` is an EXACT `Q'` identity (proved +
   sympy). CT is not tuned to hide a divergence; it is `dimQ 1 · renormW`, the standard
   marginal heat-kernel-time retuning, with `renormW → 1` (identity retuning) at the
   continuum `w→1`.
2. **δ_ren is the scheme-INDEPENDENT part.** `δ_ren = 2(1−w)²(2+w)` vanishes to SECOND
   order at the fixed point; the linear/marginal (coordinate-on-coupling-space) term is
   precisely what CT absorbs. The transverse residual is the genuine deviation from
   self-similar scaling — the physically correct per-step gap defect (the free UV step is
   scale-exact, `freeEnd_defect_scaleExact`).
3. **Why the raw weight is the WRONG object.** `raw = 2w³ → 2` at `w→1` is the excited-mode
   POPULATION, not the margin DEGRADATION. At the free UV the theory is scale-invariant, so
   the dimensionless margin is preserved (defect `→0`) even though modes are fully
   populated. Bounding `raw` was the category error; bounding `δ_ren` is correct.

**The honest caveat (the residual).** Renormalization tells us WHAT the physical defect is
(`δ_ren`, transverse) and PROVES that quantity obeys the bound uniformly. It does NOT
prove the physical `realLeak` EQUALS `δ_ren` — that the retuning `renormW` is realizable at
the level of the actual coarse transfer operator. That identification is the open residual,
unchanged from `SingleStepDefectBound.singleStep`. The counterterm is a genuine physical
marginal renormalization, not a divergence-hiding artifact — but the physical identification
remains the wall.

---

## 5. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited across YMGap.*
Build completed successfully (689 jobs).
```
All 9 load-bearing decls `#print axioms` = `[propext]` or `[propext, Quot.sound]` — plus
`renormalizedDefect_value_at_weak` depends on **no axioms** (pure kernel `decide`). No
`Classical.*`, no `native_decide`, no `sorry`/`admit`. New file scanned clean.

---

## 6. HONEST VERDICT

Route H **PROVES** the exact counterterm decomposition `raw = δ_ren + CT`
(`coeffW_eqv_renDefect_add_counterterm`) and the **UNIFORM full-range bound**
`renormalizedDefect ≤ 6(1−w)²` for ALL `w∈[0,1]` including `w→1`
(`renormalizedDefect_le_six`), machine-verifying at `w=9/10` that renormalization
satisfies the transverse envelope EXACTLY where the raw ratio `2w³` violates it
(`renorm_fixes_weak`). This CLOSES the analytic half of `FullRangeFusedDefect`: the
renormalized defect genuinely obeys the bound at the deep-UV end that defeated the raw
defect. The counterterm subtraction is the PHYSICAL marginal renormalization (exact
identity, scheme-independent transverse residual vanishing to 2nd order at the fixed
point), NOT a divergence-hiding artifact.

The SOLE remaining open content is the **identification** `realLeak = δ_ren` (the physical
per-step margin defect equals the renormalized transverse defect / the counterterm is
implementable), carried guard-safe as the open hypothesis of the conditional producer
`fullRangeFusedDefect_of_identification` — this IS `SingleStepDefectBound.singleStep` /
`TrueMarginRecursion` and is **NOT inhabited**. `FullRangeFusedDefect` with its free
`realLeak` is vacuously inhabitable; that closure is refused (Rule 9(1)). **The 4D
Yang–Mills mass gap remains OPEN; nothing is faked; no free-field / `δ:=0` used; no guarded
bundle inhabited.**
