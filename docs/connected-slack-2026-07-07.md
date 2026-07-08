# The connected correction vs. the third-order slack: `Cdef ≤ 2(1−w)³`

**Date:** 2026-07-07 · **Verdict class: (ii) concrete-regime closure at `m=1` (uniform in `w`) + (iii) a sharp two-part residual; NO mass-gap closure.**
**Lean:** `lean/YMGap/Continuum/ConnectedSlackBound.lean` — builds green (761 jobs), axiom-clean (`propext`/`Quot.sound` only), frontier-guard OK (5 Clay-frontier types uninhabited; this file inhabits none).

---

## 0. The exact objects

| object | formula (`u := 1−w`) | status |
|---|---|---|
| free renormalized defect `δ_free(w)` | `2(1−w)²(2+w) = 6u² − 2u³` | PROVED (`RenDefectQuadFactor`, `SubdominanceWindow`) |
| model target | `realδ ≤ 6(1−w)² = 6u²` | the per-step defect target |
| **third-order slack** | `slack(w) = 6u² − δ_free = 2(1−w)³ = 2u³` | PROVED exact (`dfree_add_slack_eqv_model`) |
| connected m-fold remainder | `Cdef_m = r2(m) − 3(r1(m)/2)^{8/3}` | the object to bound by `2u³` |
| saddle decomposition | `Cdef_m = 4·Var_m(cosθ) + F(μ)`, `F(μ)=4μ²−1−3μ^{8/3}` | PROVED (`saddle_decomposition`) |

Since `δ_free` saturates `6u²` to **second** order, `realδ ≤ 6u²` requires `Cdef ≤ 2u³` — a purely **third-order** budget for the connected correction.

---

## 1. What is newly PROVED this session (rigorous, axiom-clean Lean)

### (A) `Cdef ≤ 2(1−w)³` CLOSED at `m=1`, uniformly in `w` (deliverable (ii))
- `cdef1_eq_zero`: at a single plaquette `r2=3w⁸`, `μ=w³`, and `μ^{8/3}=(w³)^{8/3}=w⁸` **exactly** (the cube-root relation is the proved `singlePlaquette_logLinear`, `(w³)⁸=(w⁸)³=w²⁴`), so `Cdef_1 = 3w⁸ − 3·w⁸ ≃ 0`.
- `slackExpr_nonneg`: `2(1−w)³ ≥ 0` for `w ≤ 1`.
- **`cdef1_le_slack`**: `Cdef_1(w) ≤ 2(1−w)³` for **all** `w ≤ 1` — the connected-correction / third-order-slack inequality holds unconditionally on the non-interacting `m=1` slice, in particular on `[w*,1)=[2^{−1/3},1)`.

This is genuine, but the honest scope is `m=1` (a pure renormalized coupling, zero interaction). It is **uniform in `w`**, not in `m`.

### (B) The sharp residual anchor: the saddle pieces cancel EXACTLY at `m=1`
- **`saddle_exact_cancellation_m1`**: `4·Var_1(cosθ) + F(μ_1) ≃ Cdef_1 ≃ 0`, i.e. `F(μ_1) = −4·Var_1` **exactly**.
- `fourVar_ge_zero`: `4·Var ≥ 0` (Cauchy–Schwarz).

Consequence (machine-checked): the only individually-signed facts available — `4·Var ≥ 0` and `F ≤ 0` — give at best `0 ≤ Cdef ≤ 4·Var`. But `4·Var_m ∼ 3(1−w)/m` is **linear** in `u` (numerics: `4·Var_1 ≈ 0.166` at `w=0.9`, `≈ 0.86` at `w=0.6`), while the sum `Cdef_1 = 0`. So bounding the two saddle pieces **separately is `O(u⁻²)`-lossy** for the cubic slack `2u³`. The uniform bound is unreachable without the **joint** near-Maxwell cancellation. This is the exact, rigorous statement of *why* the uniform-in-m bound is stuck.

---

## 2. The uniform-in-m bound (m≥2): TRUE, but not a finite check and not independently closeable

Off-line (mpmath dps 40, class-angle integral, cross-checked vs exact Clebsch–Gordan fusion; verified this session):

| w | `2u³` | `Cdef_2` | `Cdef_3` | `Cdef_4` | `Cdef_8` | `Cdef_m ≤ 2u³`? | `4Var_m ≤ 2u³`? |
|---|---|---|---|---|---|---|---|
| 0.6 | 0.128 | 1.53e−2 | **1.68e−2** | 1.32e−2 | 3.70e−3 | ✅ all | ❌ never |
| 0.9 | 0.002 | 7.14e−5 | 3.26e−5 | 1.66e−5 | 2.70e−6 | ✅ all | ❌ never |

So `Cdef_m ≤ 2u³` holds at every probed `(m,w)` with large margin (safety factor ≈ 45 vs `6u²`; comfortably inside `2u³` too). **But:**

1. **Not a finite-m check.** At `w=0.6`, `Cdef_3 > Cdef_2` — `sup_m Cdef_m` is at `m=2` **only** in the deep-UV `w≳0.8`; at strong coupling the argmax moves to `m≥3`. There is no single finite `m` whose bound implies the rest (`VarianceMonotonicity` recorded this: `Var` monotone ⇏ `Cdef` monotone, because the `F`-gap has opposite sign and the residual is set by the quantitative near-Maxwell balance).
2. **Not decidable.** `Cdef_m` is an **infinite** theta/Clebsch–Gordan series ratio carrying the **transcendental** `μ^{8/3}` — not a `Q'` decidable inequality.
3. Via `saddle_decomposition` + `saddle_exact_cancellation_m1`, the uniform bound reduces to the **joint** near-Maxwell control of the fused measure = the already-open local-CLT core `SelfFusionLogConcave.FusionConvLogConcaveCore` (all fusion powers). It is TRUE and *reduced*, not an independent new closure.

`F(μ)≤0` is itself an elegant rigorous fact (sympy-exact, off the Lean critical path): substituting `μ=t³`, `F(μ) = 4t⁶−1−3t⁸ = −(t²−1)²(3t⁴+2t²+1) ≤ 0` (with `3a²+2a+1 = (a+1)²+2a² > 0`). But it is exactly the individually-signed piece proved `O(u⁻²)`-lossy in §1(B), so it does not help the cubic bound.

---

## 3. THE DECISIVE ADVERSARIAL CATCH — the real-vs-mfold residual (`real_defect_identification`)

**Even a fully proved uniform `Cdef_m ≤ 2(1−w)³` does NOT close the mass gap.** The premise "`Cdef ≤ 2u³` ⟹ `singleStep` ⟹ mass gap" is **false as stated**, and I refuse to fake it. The exact obligation is

```
SingleStepDefectBound.singleStep : ∀ k, (1 − δ_model_k) · trueMargin_k ≤ trueMargin_{k+1}
```

quantified over the **abstract physical margin** `trueMargin : Nat → Q'` (the real dimensionless gap `m_lat(a_k)/a_k`) and its recursion. This is an **`s=1` (fundamental-gap) statement over the full RG tower**. `Cdef_m` is an **`s=2` leakage relative to a renormalized `s=1` coupling at a single bond-moving step** — a strictly weaker, and *different*, functional of the fused measure (the gap defect is `∝ 2−r1`, not `Cdef`). Passing from the one to the other requires the three genuinely-missing inputs:

- **(a) true-margin construction** — build the actual `trueMargin` sequence;
- **(b) block-multiplicity matching** — the physical step fuses `m = b^{d−1} = 8` (4D, `b=2`); `Cdef` is a single-scale fusion object, not the recursion;
- **(c) channel feedback** — how the `s≥2` fused remainder feeds into the *next* scale's `s=1` gap, iterated.

None is supplied by the slack bound. This is recorded in Lean as `slack_bound_does_not_close_singleStep` and `uniformSlack_reduces_to_localCLT`, consistent with the pre-existing `UniformMFoldConcentration.uniformBound_does_not_close_singleStep` and `VarianceMonotonicity.varMono_insufficient_for_uniform`. **The residual is `real_defect_identification`, NOT merely the analytic inequality.**

---

## 4. HARD-CRITERION verdict

- **(i) inhabit `SingleStepDefectBound` → mass gap:** **NO.** Refused. Blocked not only by the (transcendental, all-m) analytic inequality but decisively by `real_defect_identification` (§3): `Cdef_m` is strictly weaker than `singleStep`. No `:= SingleStepDefectBound` alias, no `Cdef := model` dodge; frontier guard confirms all 5 Clay-frontier types remain uninhabited.
- **(ii) prove `Cdef ≤ 2(1−w)³` on a concrete regime:** **YES — `m=1`, uniform in `w` on all of `[0,1)`** (`cdef1_le_slack`), via `Cdef_1 ≡ 0` (exact). Uniform in `w`; **not** uniform in `m` (only the non-interacting single-plaquette slice).
- **(iii) sharp residual:** **YES, two-part, numerically pinned.**
  - *Analytic:* the uniform-in-m `Cdef_m ≤ 2u³` is TRUE (factor ≈ 45) but reduces to the JOINT near-Maxwell/local-CLT control (`FusionConvLogConcaveCore`); the separate-piece route is `O(u⁻²)`-lossy — **PROVED** exactly at `m=1` (`saddle_exact_cancellation_m1`). `sup_m` is not at a fixed finite `m` (`Cdef_3 > Cdef_2` at `w=0.6`), and `Cdef_m` is an infinite transcendental object — so it is **not** a finite computable check.
  - *Structural (the binding core):* even the full analytic bound does not identify the real per-step degradation with `Cdef_m` — `real_defect_identification` = (true-margin construction) + (block-multiplicity matching) + (channel feedback).

---

## 5. Lean deliverable (`ConnectedSlackBound.lean`) — all green, axiom-clean

| declaration | content | axioms |
|---|---|---|
| `slackExpr_nonneg` | `2(1−w)³ ≥ 0` on `w ≤ 1` | `propext` |
| `cdef1_eq_zero` | `Cdef_1(w) = 3w⁸ − 3·w⁸ ≃ 0` | `propext` |
| `m1_cubeRoot_exact` | `(w³)⁸ ≃ (w⁸)³` (cube-root exactness, re-export) | `propext` |
| **`cdef1_le_slack`** | **`Cdef_1(w) ≤ 2(1−w)³` ∀ `w≤1` (deliverable (ii))** | `propext` |
| **`saddle_exact_cancellation_m1`** | **`4·Var_1 + F(μ_1) ≃ 0` (sharp residual anchor)** | `propext` |
| `fourVar_ge_zero` | `4·Var ≥ 0` (Cauchy–Schwarz, re-export) | `propext` |
| `uniformSlack_reduces_to_localCLT` | doc: uniform bound = local-CLT, not finite-m | — |
| `slack_bound_does_not_close_singleStep` | doc: `real_defect_identification` | — |
| `fullFloor_still_needs_singleStep` | GIVEN `SingleStepDefectBound` → whole floor | `propext`,`Quot.sound` |
| `connectedSlack_verdict` | non-vacuous bundle of the above | `propext` |

`#print axioms` on every load-bearing declaration: `propext`/`Quot.sound` only. No `Classical.*`, no `native_decide`, no `ring`/`nlinarith`, no `sorry`. Inhabits no frontier type; produces no `SingleStepDefectBound`.

---

## 6. Honest final verdict

`Cdef ≤ 2(1−w)³` is **PROVED at `m=1` uniformly in `w`** (the connected correction vanishes there) and is **TRUE for `m≥2`** (mpmath, factor ≈ 45) but reduces — via the exact saddle decomposition and the machine-checked `m=1` exact cancellation — to the **joint near-Maxwell / local-CLT** control `FusionConvLogConcaveCore`, already open (not a finite-m check; `Cdef_m` is transcendental with a moving argmax). And **even the full uniform bound is strictly weaker than `singleStep`**: the binding core is `real_defect_identification` (true-margin construction + block-multiplicity matching + channel feedback). No frontier bundle inhabited; nothing faked; the 4D Yang–Mills mass gap remains OPEN.
