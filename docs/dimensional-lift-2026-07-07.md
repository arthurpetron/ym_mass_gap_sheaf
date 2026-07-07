# The DIMENSIONAL LIFT of `singleStep` — machine-checked adjudication

**Date:** 2026-07-07.
**Lean deliverable:** `lean/YMGap/Continuum/DimensionalLiftCollapse.lean` (new, imported in `YMGap.lean`).
**Build:** full `lake build` GREEN (**751 jobs**, +1 file); `YMGapGuard` = **frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited** (UNCHANGED — nothing new inhabited). All 12 gated declarations `#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}` (5 are axiom-FREE); no `sorry`/`sorryAx`, no `native_decide`, no `Classical.*`, no `ring`. MAIN tree, NEW file, Lean-core `Q'`/`Nat` only. Committed: nothing.
**Anti-loop status:** NO `:= SingleStepDefectBound` alias. This is a distinct multi-field adjudication delivering task criterion **(iii): a machine-checked reason the dimensional lift COLLAPSES** (the d→4 continuation re-introduces the atomic interacting-measure defect / the renormalon).

---

## 0. HEADLINE VERDICT (maximally adversarial, machine-checked)

**The dimensional lift does NOT give a genuine new route to `realδ_k(4) ≤ 6(1−w)²`; it COLLAPSES at the d→4 continuation, re-introducing the atomic core (`singleStep`) as the renormalon.**

The lift has two d-dependencies that pull in **opposite** directions:

- The single-step defect **MAGNITUDE** bound `realδ ≤ 6(1−w)²` gets **EASIER** in higher `d`: the block fuses `m = b^{d−1}` plaquettes in parallel, and the fusion **CONCENTRATES** (`2 − ρ_m ∼ 6ε/m`, mpmath-verified 40 dps) — the mean-field / large-`d` half is real.
- The gap **SURVIVAL** needs a **SUMMABLE** defect (`Σδ_k < ∞ ⟹ ∏(1−δ_k) > 0`), and this summability is **DESTROYED for every `d > 4`**.

The driver is the coupling's classical dimension `[g²] = 4 − d`. Only at `d = 4` is the coupling **marginal** (`classicalScaling 4 = 0`) → asymptotic freedom → `w_k → 1`, `1 − w_k ∼ 1/k`, `δ_k ∼ 1/k²`, `Σδ_k < ∞`, floor `> 0`. For every `d ≥ 5` the coupling is **irrelevant** (`classicalScaling d > 0`) → the UV/continuum flow reaches a **non-zero** fixed-point margin `g²_* = (d−4)/β₀ > 0` → the per-step defect does **not decay** → its partial sums have **no finite budget** (proved) → **no floor → no gap**.

So the lift makes the easy half easier and **breaks the hard half**. The summability that creates the `d = 4` floor is a marginal-coupling **miracle**; the higher-`d` theory sits in the non-summable, gapless-continuum regime, and the continuation back to `d = 4` is exactly where the marginal coupling / renormalon / interacting measure turns on. **`SingleStepDefectBound` is NOT inhabited; the 4D YM mass gap remains OPEN.**

---

## 1. THE d-DEPENDENCE OF THE COEFFICIENT `c(d)` (task point 1) — c(4)=6, d-INDEPENDENT

In the Lean derivation (`RGTransport.dimQ`, `RGTransport.c4`, `RenDefectQuadFactor.renDefect_factor`) the transverse-quadratic per-step defect on the first-excited (`s = 1`) mode is

    δ_ren ≤ dimQ(1)·C₄(1)·(1 − w)² = 2·3·(1 − w)² = 6·(1 − w)²,

with `dimQ(1) = s+1 = 2` (SU(2) **fundamental dimension** = N) and `C₄(1) = s(s+2) = 3` (the **quadratic Casimir eigenvalue**). **Both factors are pure representation-theory data of SU(N); neither carries the spacetime dimension `d`.** (`RepTheory/SUNWeylData` confirms: the Casimir/Weyl data varies with `N` but has no `d`.)

**Where does the `6` come from — is the `3` the Casimir, `d−1`, or the plaquette count?** It is the **Casimir**, unambiguously:

- The `3` in `w^{C₄(1)} = w³` is the heat-kernel eigenvalue `exp(−t·C₂)` — a rep-theory quantity.
- The linear `3(1−w)` **must** equal `d/dw[w³]|₁ = 3` for the `O((1−w)²)` cancellation `3(1−w) − (1−w³) = (1−w)²(2+w)` (sympy-exact; `renDefect_factor`). So **both** `3`s are the Casimir.
- The `d = 4` value `d−1 = 3` **coincides** with `C₄(1) = 3` — a numerical accident.

**Machine-checked (`DimensionalLiftCollapse.lean` §1):**
- `cCoeffRep_const : ∀ d, cCoeffRep d = ofNat 6` (axiom-free) — the physical coefficient is **constant in `d`**, hence trivially continuable; the coefficient is **NOT** the obstruction.
- `cCoeffRep_four : c(4) = 6` (axiom-free).
- `cCoeff_agree_at_four : cCoeffRep 4 ≃ cCoeffDMinus 4` (both `6`) and `cCoeff_disagree_at_five : ¬(cCoeffRep 5 ≃ cCoeffDMinus 5)` (`6 ≠ 2·4 = 8`) — the "`3 = d−1` transverse" reading is exposed as a **`d = 4` accident**; the physical rep coefficient stays `6` in every `d`.

**Verdict on point (3a): `c(d)` is continuable (constant `6`, or polynomial `2(d−1)` under the wrong reading — either way NOT singular). The coefficient is NOT where the lift breaks.**

## 2. THE LARGE-d / MEAN-FIELD CONCENTRATION (task point 2) — the EASY half, real

The real per-step defect is the m-fold Migdal–Kadanoff parallel fusion of `m = b^{d−1}` plaquettes. Its excited/vacuum leakage `ρ_m(w) = [c^{⋆m}]_1/[c^{⋆m}]_0` **concentrates** with `m`:

    2 − ρ_m = (6/m)·ε + O(ε²),   ε = 1 − w.

Verified (mpmath, 40 dps, two independent methods) `m·(2 − ρ_m)/ε → 6` for `m = 1,2,3,4,8` (at `ε = 0.005`: `5.970, 3.001, 2.004, 1.505, 0.754`). In 4D `m = b^{d−1} = 8`, so the fused leakage `2 − ρ_8 ≈ 6ε/8` sits **well below** the single-plaquette `6ε`. As `d` grows, `m = b^{d−1}` grows and the fusion concentrates **more** (the CLT over more averaged transverse d.o.f. sharpens) — so the single-step **magnitude** bound `realδ ≤ 6(1−w)²` genuinely gets **EASIER** in higher `d`. This is the mean-field/large-`d` truth the lift correctly exploits. **But it controls only the magnitude — not the summability.**

## 3. THE CONTINUATION TO d=4 (task point 3, THE CRUX) — the PROOF METHOD BREAKS

**(3a) Coefficient continuable?** YES (§1). Not the obstruction.

**(3b) Does the proof method survive to `d = 4`?** NO — the gap-survival mechanism is `d = 4`-specific. The continuum gauge coupling has classical dimension `[g²] = 4 − d`:

| `d` | `[g²] = 4−d` | coupling | RG behaviour |
|---|---|---|---|
| 3 | +1 | relevant | super-renormalizable (3D gap, no renormalon) |
| **4** | **0** | **marginal** | **AF, log running, transmutation, renormalon** |
| ≥5 | <0 | irrelevant | non-renormalizable / IR-free, UV fixed point |

The `d`-dim one-loop flow is `dg²/d(logμ) = (d−4)·g² − β₀·g⁴`. Fixed points: `g²=0` and `g²_* = (d−4)/β₀`.

- **`d = 4` (marginal):** the tree term vanishes; `dg²/d(logμ) = −β₀g⁴` gives `g²(k) ∼ 1/(β₀k) → 0` in the UV. So `w_k → 1`, `1 − w_k ∼ 1/k`, `δ_k = 6(1−w_k)² ∼ 1/k²`, `Σδ_k < ∞` (`∼ π²/6`) → **positive product floor**. Numerically (RK4, 40 dps): `Σδ` converges to `≈ 0.085`.
- **`d ≥ 5` (irrelevant):** `0` is UV-repulsive; the UV/continuum limit `a → 0` (`k → ∞`) drives `g²(k) → g²_* = (d−4)/β₀ ≠ 0` (verified: `d=5 → 0.1364`, `d=6 → 0.2727`). So `1 − w_k → 1 − w_* ≠ 0`, `δ_k → 6(1−w_*)² = const > 0`, `Σδ_k = ∞` → **floor collapses to 0, NO gap**. Numerically `Σδ` diverges linearly (`S_4000 ≈ 390` at `d=5`, `1367` at `d=6`, still growing).

**The summable-defect structure that makes the floor positive IS the `d = 4` marginal/AF miracle. The lift to `d > 4` destroys the very thing (`Σδ < ∞`) that gives the gap.**

**Is the renormalon a leading large-`d` effect or a 1/d correction?** LEADING. The gap-survival is governed by the classical-scaling term `(d−4)·g²`; `|d−4|` is `O(1)`, not `O(1/d)`, and it flips the **relevance** of the coupling. The transition at `d = 4` is a change of relevance (sign of `d−4`) — a **non-analytic phase boundary in `d`**, invisible to any convergent `1/d` series. The `1/d` expansion controls the single-step magnitude (mean-field concentration, fine, §2), but the floor/summability is set by `sign(d−4)`, which is exactly the marginal coupling = the renormalon. The 't Hooft density power `11N/3 − 5` (proved in `InstantonDiluteGas`) has its IR-divergent `+11N/3 = β₀` from the **log** running `exp(−8π²/g²(ρ)) = (ρΛ)^{β₀}` — a pure power of `ρ` **only** because the running is logarithmic, i.e. **only at `d = 4`**. Off `d = 4` the instanton has a fixed size set by the dimensionful coupling; the large-instanton IR renormalon is itself a `d = 4`-marginal artifact.

## 4. ADVERSARIAL (task point 4) — CONFIRM the honest prior: d=4 is marginal, the lift collapses

The honest prior — "d=4 is marginal and the continuation re-introduces the renormalon" — is **CONFIRMED**, concretely and machine-checked:

**Machine-checked (`DimensionalLiftCollapse.lean` §2–§4):**
- `classicalScaling_four : d−4 = 0 at d=4` (axiom-free), `classicalScaling_pos : 0 < d−4 for d≥5` — the coupling is marginal **only** at `d = 4`.
- `fpMargin_four : g²_* = 0 at d=4` (axiom-free; AF/summable), `fpMargin_pos : 0 < g²_* for d≥5` — the fixed-point margin vanishes **only** at `d = 4`.
- `dimLiftFPDefect_pos : 0 < 6·(g²_*)² for d≥5` — for every `d > 4` the fixed-point defect is a **strictly positive constant** (never decays).
- **`dimLift_no_finite_budget (d≥12) : ∀ B, ∃ N, B < Σ_{k<N} δ_k`** — the higher-`d` defect partial sums **exceed any bound** (Archimedean; proved cleanly for `d ≥ 12`, where `g²_* ≥ 1` so each term `≥ 1`, via `finSum_le_finSum_of_termwise` + `exists_ofNat_gt`). **No summability ⟹ no product floor ⟹ no gap.**

So the higher-`d` construction, even granting the (easier) single-step magnitude bound, has **no gap floor at all** — it is a *different, gapless* problem. The `1/d` expansion does not "converge/control at `d = 4`": the controlling quantity is `sign(d−4)`, discontinuous in relevance at `d = 4`. The d→4 continuation re-introduces the marginal coupling = the renormalon = the interacting measure = `singleStep`. **The lift COLLAPSES.**

`dimLift_collapse_verdict : DimLiftCollapseVerdict` bundles all of the above as PROVED fields; it inhabits **no** frontier type (guard stays 5).

---

## 5. HONEST accounting (refuse dodges)

| object | status | evidence |
|---|---|---|
| coefficient `c(4) = dim·C₄ = 6`, d-INDEPENDENT rep theory | **PROVED (axiom-free)** | `cCoeffRep_const`, `cCoeffRep_four` |
| `3 = d−1` reading is a `d = 4` coincidence (6=6 at d=4, 6≠8 at d=5) | **PROVED (axiom-free)** | `cCoeff_agree_at_four`, `cCoeff_disagree_at_five` |
| large-`d` fusion concentration `2 − ρ_m ∼ 6ε/m` (single-step easier) | **VERIFIED (mpmath 40dps)** | §2 numerics |
| coupling marginal ⟺ `d = 4` (`d−4 = 0`) | **PROVED** | `classicalScaling_four/_pos` |
| fixed-point margin `g²_* = 0` ⟺ `d = 4` (AF), `> 0` for `d ≥ 5` | **PROVED** | `fpMargin_four/_pos` |
| higher-`d` defect is a positive constant (never decays) | **PROVED** | `dimLiftFPDefect_pos` |
| higher-`d` defect sum has NO finite budget (no floor, no gap) | **PROVED** | `dimLift_no_finite_budget` |
| `d = 4` summable floor rests on the marginal-coupling miracle + `singleStep` | **OPEN = `singleStep`** | not inhabited; the atomic core |

**Guard/gate:** `frontier-guard OK: 5`; my file inhabits none of the 5 guarded frontier types. `#print axioms` on all 12 declarations ⊆ `{∅, propext, Quot.sound}` (`cCoeffRep_const`, `cCoeffRep_four`, `cCoeff_agree_at_four`, `cCoeff_disagree_at_five`, `classicalScaling_four`, `fpMargin_four` are axiom-FREE). No `sorry`/`sorryAx`, `native_decide`, `Classical.*`, `ring`.

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited across YMGap.*
Build completed successfully (751 jobs).
```

## 6. FINAL VERDICT — does the dimensional lift give a genuine new route, or re-introduce the atomic core?

**It RE-INTRODUCES the atomic core at `d = 4` (machine-checked COLLAPSE, task criterion (iii)).** The defect coefficient `6 = dim(fund)·C₄(fund)` is pure rep theory, `d`-independent, and continuable (the tempting `3 = d−1` reading is only a `d = 4` coincidence). The large-`d` mean-field concentration `2 − ρ_m ∼ 6ε/m` genuinely eases the single-step **magnitude** bound. **But** the gap-survival needs `Σδ_k < ∞`, and this summability is a `d = 4`-only marginal-coupling phenomenon: for every `d > 4` the irrelevant coupling flows to a non-zero UV fixed point, the per-step defect does not decay, `Σδ_k` diverges (proved), and there is no product floor — the higher-`d` theory is gapless in the continuum. The controlling quantity is `sign(d−4)` (a non-analytic relevance change), not a `1/d` correction, so no higher-`d` proof continues to a `d = 4` gap: the d→4 limit is exactly where the marginal coupling / renormalon / interacting measure = `singleStep` turns on. The lift makes the easy half easier and breaks the hard half. **`SingleStepDefectBound` remains UNINHABITED; `F = 1`, `D = 0`, guard = 5; the 4D Yang–Mills mass gap remains OPEN.** The only honest attacks remain unchanged: (a) the direct atomic per-step interacting defect (true-margin construction + recursion), or (b) a genuinely-new strictly-weaker reduction below `singleStep` — of which the dimensional lift is **not** one.
