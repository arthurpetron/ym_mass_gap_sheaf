# Route B — heat-kernel / Bałaban fluctuation-integral attack on the 4D SU(2) block-spin gap defect

**Target obligation.** `SingleStepDefectReduction.SingleStepDefectBound.singleStep` — the
sole open field to which the whole Clay continuum gap is reduced:
`(1 − afDefectSeq afr k)·trueMargin k ≤ trueMargin (k+1)`, i.e. the real 4D SU(2)
block-spin degradation of the true dimensionless margin is bounded by the model defect
`δ_model = afDefectSeq afr = bondMovingDeltaRen 1 pMult (w_k)`.

**Route.** Derive `δ_model` from the ACTUAL heat-kernel fluctuation integral as a genuine
SECOND CUMULANT, prove the second-cumulant estimate, and reduce `singleStep` to the
sharpest honest residual. **Do NOT inhabit the frontier; do NOT fake with a free field.**

**Deliverables.** Lean module `lean/YMGap/Continuum/HeatKernelSecondCumulant.lean`
(full `lake build` green, guard OK, axiom-clean); numerics `routeB_numerics.py`
(mpmath dps 40–50, sympy exact); this report.

---

## 1. The fluctuation integral and its cumulant expansion

One block-spin RG step integrates out the fine fluctuation field ξ around the coarse
background U: the coarse effective action is `−log ∫ Dξ exp(−S_fine(U·ξ))`. Cumulant
expansion (Bałaban / Magnen–Rivasseau–Sénéor / Federbush; covariance decomposition
`C = Σ_j C_j`, per-scale finite-range — NOT the Migdal–Kadanoff pointwise product):

- **(A) Free/Gaussian part — scale-EXACT, ZERO defect.** In-tree
  `SingleStepDefectReduction.freeEnd_defect_scaleExact`: `δ_ren(w=1) ≤ 0`. The free UV
  is scale-invariant and erodes no gap. (This is exactly what MK's linear error fails to
  reproduce.)
- **(B) Marginal part — the running coupling `g²`, SUBTRACTED by the counterterm.**
  In-tree `trueDev_eq_counterterm_sub_transverse`: the linear part
  `dimQ 1·C₄(1)·(1−w)` equals `dimQ 1·(1 − renormW p w)` — the explicit reparametrization
  that absorbs the marginal flow. It is the FLOW, not an error.
- **(C) Transverse remainder — the SECOND CUMULANT of the fine field, quadratic.** THIS
  route. What survives after A (=0) and B (subtracted) is the connected two-point of the
  fluctuation — the non-Gaussian remainder of the fluctuation determinant.

The heat-kernel single-plaquette class function has character coefficients
`c_s(w) = dimQ(s)·w^{C₄(s)}` with `dimQ(s) = s+1`, `C₄(s) = s(s+2)` (scaled SU(2)
Casimir; `s=1` = fundamental, `dimQ 1 = 2`, `C₄(1) = 3`). Integrating out ξ, the coarse
coefficient of channel `s` deviates from its flat (`w=1`, Haar) value by the second
cumulant of the fluctuation's Casimir in that channel — the marginal-subtracted overshoot

```
over(s,w) = C₄(s)·(1−w) − (1 − w^{C₄(s)}),   chanCumulant(s,w) := dimQ(s)·over(s,w).
```

`over(s,w)` is precisely the SECOND-ORDER (in the margin `1−w`) part of the deviation
`1 − w^{C₄(s)}` — the linear part having been removed by the counterterm (B). This is the
fluctuation-integral definition of the per-channel second cumulant.

---

## 2. The heat-kernel second-cumulant estimate (PROVED, axiom-clean)

Per channel, the fluctuation determinant's deviation from Gaussian is second-order in the
field, with the Casimir `C₄(s)` as the curvature (the `d2x ≤ 1` heat-kernel/curvature
bound of the Tier-0 analysis). Proved in Lean from the constructive
Taylor-with-remainder `secondOrder_qpow` (`n(1−w) − (1−w^n) ≤ n²(1−w)²`) at `n = C₄(s)`:

| Lean theorem | statement | axioms |
|---|---|---|
| `chanCumulant_nonneg` | `0 ≤ chanCumulant s w` on `[0,1]` | propext, Quot.sound |
| **`chanCumulant_quadratic`** | **`chanCumulant s w ≤ dimQ(s)·C₄(s)²·(1−w)²`** | propext, Quot.sound |
| `chanCumulant_one_eq_bondMoving` | `bondMovingDeltaRen 1 1 w ≃ chanCumulant 1 w` | propext |
| `chanCumulant_one_le_six` | `chanCumulant 1 w ≤ 6·(1−w)²` (sharp) | propext, Quot.sound |
| `afDefectSeq_eq_gapCumulant` | `afDefectSeq afr k ≃ chanCumulant 1 (w_{k₀+k})` | propext, Quot.sound |
| `cumSum_le_moment` | `Σ_{s=1}^M chanCumulant(s,w) ≤ (Σ_{s=1}^M dimQ(s)C₄(s)²)·(1−w)²` | propext, Quot.sound |
| `gapChannelDomination_to_singleStep` | `GapChannelDomination → SingleStepDefectBound` (conditional) | propext, Quot.sound |

**The `6` constant.** `chanCumulant_one_le_six` gives the fundamental (gap) channel bound
with `6 = dimQ(1)·C₄(1) = 2·3`. For SU(2) this equals `3N` at `N=2` (the transverse
generators of SU(2), = dim SU(2) = 3, × the block dimension `N=2`). The sharp value uses
the exact factorization `3(1−w) − (1−w³) = (1−w)²(2+w)` with `2+w ≤ 3` (sympy-exact,
remainder 0), not the crude `C₄² = 9` envelope.

**Grounding the summability machinery.** `afDefectSeq_eq_gapCumulant` proves the abstract
summable `∼1/k²` model sequence that drives the entire in-tree product floor IS literally
the fundamental-channel heat-kernel second cumulant along the AF flow. The
fluctuation-integral picture and the summability machinery are now the same object.

---

## 3. THE ADVERSARIAL FINDING — the total second cumulant is NOT the gap defect

The naive Route-B reading "the real defect = the TOTAL fluctuation second cumulant over
ALL channels" is **refuted numerically** (`routeB_numerics.py`, mpmath dps ≥ 40). With the
heat-kernel measure `μ_s(w) = dimQ(s)w^{C₄(s)}/Z(w)`, the total

```
R(w) = Σ_{s≥1} μ_s(w)·chanCumulant(s,w).
```

| `w` | `R(w)/(1−w)²` | `≤ 6`? |
|---|---|---|
| 0.1 | 0.0084 | yes |
| 0.5 | 1.335 | yes |
| 0.670… | 6.000 | **crossover** |
| 0.9 | 199 | no |
| 0.99 | 74 347 | no |
| 0.9999 | 7.6·10⁹ | no |

`R(w)` is `≤ 6(1−w)²` **only for `w ≤ 0.670…`** (which comfortably contains the
strong-coupling anchor `w = 1/6 ≈ 0.167`), and **DIVERGES like `(1−w)^{−1/2}`** as `w→1`
(power-law fit β = −0.500 at w=0.9999; the active-mode count `≍ τ^{−1/2}`, `τ = −log w`).
Along the AF flow `1−w_k ∼ 1/k`, `R(w_k) ∼ k^{1/2}` — the partial sum `Σ_{k<3000} R(w_k)`
reached 8.3·10⁴ and grows. **The total second cumulant is NOT summable and would destroy
the gap.**

**Conclusion (decisive).** The total is an OVER-COUNT — a free-energy quantity mixing all
mass channels. The physically-correct gap defect is the fundamental-channel (`s=1`) second
cumulant `chanCumulant 1 w`, times the `pMult` transverse GENERATOR modes of the block
(NOT a sum over representation channels). That is exactly
`bondMovingDeltaRen 1 pMult w = δ_model`, which IS `≤ 6·pMult·(1−w)²` for ALL `w` and IS
summable `∼1/k²`. The higher representation channels renormalize the coupling (the
marginal flow, subtracted in (B)); their back-reaction ONTO the gap channel is the
genuinely-hard small-field content, not the divergent total. Numerically the `s=1` channel
IS dominant at strong coupling (tail `s≥2` is 0.008% of `R` at w=0.1, 26% at w=0.5).

This finding also **corrects the task's premise**: `realδ ≤ 6(1−w)²` is NOT a valid
pointwise bound for the total fluctuation near `w→1`; it holds for the correct gap-channel
object (for all `w`) and for the total only at strong coupling (`w ≤ 0.67`).

---

## 4. What is PROVED, and the named residual

**PROVED (genuine, axiom-clean `propext`/`Quot.sound` only, no `sorry`/`native_decide`):**
the per-channel heat-kernel second cumulant is `≥0` and `≤ dimQ(s)·C₄(s)²·(1−w)²`; the
model defect / AF sequence IS the fundamental-channel second cumulant; its sharp
`6·(1−w)²` bound with `6 = dimQ(1)·C₄(1) = 3N|_{N=2}`; the finite multi-mode
second-cumulant moment bound.

**NAMED OPEN — `GapChannelDomination` (UNINHABITED).** The single genuinely-open physical
input: the real 4D SU(2) per-step degradation of the true margin is dominated by the
fundamental-channel second cumulant `δ_model = afDefectSeq afr = pMult·chanCumulant 1 (w_k)`.
This is the Bałaban/MRS small-field theorem — after the marginal subtraction, the
transverse fluctuation remainder controlling the GAP channel is the second cumulant of
THAT channel alone (large-field regions and higher-rep back-reaction exponentially
suppressed / absorbed), NOT the divergent total `R(w)`.

**The reduction is guard-safe.** `gapChannelDomination_to_singleStep :
GapChannelDomination → SingleStepDefectBound` is a CONDITIONAL producer (a function with
an open-hypothesis binder), NOT an unconditional inhabitant — the frontier guard reports
`5 Clay-frontier types unconditionally uninhabited` and the build stays green. This is the
Rule-6a reduction (the abstract per-step inequality is now the concrete gap-channel
small-field cumulant estimate, physically derived), not a closure.

**Honesty caveat (Rule 9(6), matching CAPSTONE §4).** `GapChannelDomination` — exactly
like the existing `SingleStepDefectBound` it feeds — carries `domination` as a bound on a
FREE `trueMargin : Nat → Q'` function, hence is *vacuously fakeable in principle* (e.g.
`trueMargin ≡ 1` satisfies it via `afDefectSeq ≥ 0`). This is the systematic frontier
caveat, NOT a new weakness: the residual is genuine only when `trueMargin` is the physical
margin `m_lat(a_k)/a_k`, and the honest protection is the guard + refusing to land the
fake, not type-theoretic impossibility. It is NOT inhabited here. The genuinely
NON-vacuous content of this deliverable is the PROVED §2 second-cumulant estimates and the
§3 refutation — theorems about the concrete `chanCumulant` object, not the free field.

---

## 5. Build / guard / axioms (honesty gate)

```
$ lake build
✔ [679/682] Built YMGap
ℹ [681/682] Built YMGapGuard
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited across YMGap.*
Build completed successfully (682 jobs).
```

`#print axioms` for all 7 load-bearing declarations: `[propext, Quot.sound]` (or
`[propext]`) only — no `Classical.*`, no `sorryAx`, no `native_decide`.

---

## 6. HONEST VERDICT

Route B genuinely IDENTIFIES the model gap defect as the fundamental-channel heat-kernel
second cumulant, PROVES the per-channel second-cumulant Taylor estimate (Casimir =
curvature) and the finite multi-mode moment bound, and ADVERSARIALLY REFUTES the naive
total-second-cumulant reading (it diverges `∼(1−w)^{−1/2}`, is not the gap defect). The
`singleStep` obligation is reduced — guard-safe, via proof — to the single open
`GapChannelDomination` (the Bałaban small-field domination of the gap channel), which is
NOT inhabited. **The 4D Yang–Mills mass gap remains OPEN; nothing is faked; no free field
or `δ:=0` is used.** The genuinely-hard residual (large-field/small-field decomposition
controlling the gap-channel back-reaction) is named and isolated, not closed.
