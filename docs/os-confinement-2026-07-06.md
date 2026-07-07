# The OS-reconstruction / CONFINEMENT (area-law) route to `singleStep` — does it close the continuum gap, confirm the non-perturbative core (4th route), or is it orthogonal?

**Sole open field under attack.** `SingleStepDefectReduction.SingleStepDefectBound.singleStep`:
`(1 − δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}`, i.e. `realδ_k ≤ δ_model_k` — the
spacing-uniform continuum gap-survival. Three prior routes (block-spin, interacting-measure/Borel,
curvature) confirmed this is the non-perturbative condensate positivity
`Λ = a·exp(−1/2β₀g²) ≠ 0` (the renormalon), irreducible. This is the **last major untried
mechanism**: the OS reconstruction (via the PROVED OS2) + the strong-coupling area law
(confinement / string tension √σ).

---

## HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The OS/confinement route does NOT give `singleStep` directly, and does NOT avoid the
renormalon. It splits into a "does-not-bypass" half and a "4th-confirmation / separate-premise"
half:**

1. **The OS mechanism does NOT bypass the continuum limit — it reduces to the SAME open input.**
   OS2 (PROVED, `reflectionPositiveSchwinger_holds`) gives the reconstructed Hilbert space +
   transfer operator; the mass gap = the transfer-operator gap = `−log`(correlator decay rate).
   The **fixed-spacing** OS gap is genuinely PROVED (`reconTransfer_located_gap`, `1−sep = 107/108`).
   But the **continuum** (`a→0`) OS gap is *exactly* the spacing-uniform correlator decay
   `UniformPhysicalCorrelationDecay` — the already-named primary open input, which the repo already
   reduces to `singleStep` (`trueMargin_of_correlationDecay`). The OS route re-derives the same
   reduction; it does **not** give `singleStep` from the OS spectrum for free.

2. **The confinement string tension is a 4th confirmation of the SAME essential singularity —
   via a different physical quantity, NOT a more tractable one.** The **fixed-spacing**
   (strong-coupling) area law is genuine: the per-plaquette Wilson activity is `≤ 1/2 < 1` at the
   anchor `w = 1/2` (`strongCoupling_confinement_suppression`), a strictly-suppressive factor =
   positive fixed-spacing string tension `σa² = −log(activity) ≥ log 2 > 0` (the confinement analog
   of the proved `107/108` gap). But the **continuum** string tension is
   `√σ_phys = Λ = (1/a)·exp(−1/2β₀g²)` — dimensional transmutation — the SAME essential-singularity
   condensate scale as the fluctuation route (`stringTension_is_condensate_scale`, `rfl`:
   `continuumStringTensionScale k = condensateCReal k`). String tension vs fluctuation defect is a
   different observable, but the continuum non-perturbative input is identical: `exp(−c/β₀g²)`.

3. **Confinement is ORTHOGONAL to the mass gap (separate premise, no bridge).** Per the project
   principle `mass gap ≠ area law`, `WilsonAreaLaw` carries the continuum area law
   `ScaleCovariantWilsonAreaLaw` as an INDEPENDENT premise with NO map either way
   (`areaLaw_massGap_independence`, re-exported as `confinement_gap_independent`). Even a full
   continuum area law does not, by itself, yield the mass gap here — so the confinement route
   cannot *close* `singleStep` even if √σ > 0 were proved.

**No inhabitant of `SingleStepDefectBound`, `MassGap`, or `ScaleCovariantWilsonAreaLaw` is
produced. Nothing is faked. The 4D Yang–Mills mass gap remains OPEN.**

---

## 1. THE OS MECHANISM (task point 1) — reconstruction gives the gap = decay rate, and its continuum survival IS the uniform decay

OS2 reflection positivity is PROVED unconditionally by Schur diagonalization
(`ReflectionPositivity.reflectionPositiveSchwinger_holds`): the reflection Schwinger form
`R_t(c) = Σ_λ e^{−t·C₂(λ)}·c_λ²` is a weighted sum of squares, `≥ 0` for **every** real coefficient
vector — no `P_N`/Gram-PSD input, no pointwise heat-kernel positivity. This is the exact input the OS
reconstruction consumes to build the GNS Hilbert space and the transfer operator `T`. The mass gap is
then the spectral gap of `T`, equivalently `m = −log`(the connected-correlator decay rate).

- **Fixed spacing — PROVED.** `reconTransfer_located_gap` gives the located gap of the *actual*
  reconstructed transfer operator, `1 − sep = 107/108 > 0`. This IS the OS-reconstructed
  fixed-spacing gap. So the OS mechanism genuinely delivers the fixed-spacing gap — matching the
  three other routes' fixed-spacing anchor.

- **Continuum — reduces to the SAME open input.** The `a→0` OS gap is the requirement that the
  reconstructed decay rate `m₋` stays positive and *uniform* as the spacing shrinks — which is
  precisely `UniformCorrelationDecay.UniformPhysicalCorrelationDecay` (correlation length
  `ξ = 1/m₋` finite and bounded as `a→0`). The repo already PROVES
  `uniformPhysicalCorrelationDecay_imp_massGap` (the uniform decay rate IS the gap) and
  `trueMargin_of_correlationDecay` (uniform decay ⟹ `TrueMarginRecursion` ⟹ `singleStep`).
  **`osContinuumGap_of_uniformDecay` re-exports the former.** So the OS route does not resolve
  `singleStep` from the OS spectrum — the a→0 uniformity of that spectrum *is* `singleStep`.

**Answer to point 1:** the OS reconstruction gives the gap = the OS-reconstructed decay rate, but
the *continuum* gap reduces to the a→0 correlator decay — the same continuum limit. Not a bypass.

## 2. THE CONFINEMENT / AREA-LAW (task point 2) — fixed-spacing √σ > 0 genuine; continuum √σ = the essential singularity

**Fixed-spacing string tension is genuine and positive** (verified, `string_tension_numerics.py`,
mpmath dps 50). For the SU(2) fundamental Wilson loop the leading strong-coupling character
expansion gives `⟨W(C)⟩ = (I₂(β)/I₁(β))^{Area}`, so `σa² = −log(I₂/I₁) > 0` at every finite β:

| β | I₂/I₁ | σa² = −log(I₂/I₁) |
|---|---|---|
| 0.1 | 0.0250 | 3.689 |
| 0.5 | 0.1237 | 2.090 |
| 1.0 | 0.2402 | 1.426 |
| 2.0 | 0.4331 | 0.837 |
| 4.0 | 0.6580 | 0.418 |

The Lean analog is exact and rational: the per-plaquette Wilson activity is
`≤ 4w³ = 1/2 < 1` at the strong-coupling anchor `w = 1/2`
(`strongCoupling_confinement_suppression`, reusing the PROVED `PlaquetteActivity.plaqActivity_le`).
A per-plaquette factor strictly below 1 is a positive fixed-spacing string tension — the confinement
side of the fixed-spacing physics, the analog of the proved `107/108` gap.

**Continuum string tension = the essential singularity.** To take `a→0` at fixed physical σ, one
runs β→∞ (g→0) along the asymptotic-freedom trajectory. Dimensional transmutation gives
`a·Λ = (β₀g²)^{−β₁/2β₀²}·exp(−1/2β₀g²)`, hence `√σ_phys = c_σ·Λ = (1/a)·exp(−1/2β₀g²)·poly`:

| g² | a·Λ | exp(−1/2β₀g²) |
|---|---|---|
| 1.00 | 7.69e-5 | 2.11e-5 |
| 0.50 | 2.17e-9 | 4.45e-10 |
| 0.20 | 3.00e-23 | 4.17e-24 |
| 0.10 | 1.67e-46 | 1.74e-47 |
| 0.05 | 3.90e-93 | 3.02e-94 |

`a·Λ → 0` like `exp(−1/2β₀g²)` — an **essential singularity** at `g²=0`. And `√σ = Λ` is the SAME
non-perturbative scale as the condensate route: `sqrt(σ_phys) = Λ`, `σ_phys = Λ²`. The Lean file pins
this: `continuumStringTensionScale k := CondensateGeometric.condensateCReal k`, with
`stringTension_is_condensate_scale : continuumStringTensionScale k = condensateCReal k` (`rfl`).

**Answer to point 2:** the strong-coupling area law + AF gives a continuum `√σ` that is the SAME
essential singularity `exp(−c/β₀g²)` — the same dimensional transmutation, the same non-perturbative
core, exactly as the task's most-adversarial branch anticipated.

## 3. THE DECISIVE CHECK (task point 3) — does it give `singleStep` directly, or reduce to the same core?

**It reduces to the same core — on both sub-routes, and cannot close `singleStep`.**

- **OS route:** the continuum OS gap = `UniformPhysicalCorrelationDecay` ⟹ `TrueMarginRecursion`
  ⟹ `singleStep`. Same reduction. Not direct.
- **Confinement route:** the continuum √σ = `Λ = exp(−c/β₀g²)` = the condensate scale. Same
  essential singularity. String tension is a *condensate-type* quantity (`σ ~ Λ²`), so it inherits
  the renormalon obstruction, not a more tractable form.

**The essential-singularity obstruction (the renormalon), machine-corroborated.** `exp(−1/2β₀g²)`
divided by any polynomial `g^{2n}` still `→ 0` as `g²→0`:

| g² | exp(−1/2β₀g²) | ratio/g² | ratio/g⁶ |
|---|---|---|---|
| 0.20 | 4.17e-24 | 2.08e-23 | 5.21e-22 |
| 0.10 | 1.74e-47 | 1.74e-46 | 1.74e-44 |
| 0.05 | 3.02e-94 | 6.05e-93 | 2.42e-90 |
| 0.02 | 1.59e-234 | 7.94e-233 | 1.99e-229 |

So the continuum string tension is invisible to any analytic/polynomial (strong-coupling-continued)
bound — identical to the curvature-route obstruction. A fixed-spacing (analytic-in-β) proof of
`σa² > 0` does **not** continue to the continuum `√σ > 0` without controlling the a→0 essential
singularity — the SAME non-perturbative input.

## 4. ASSESS (task point 4) — is √σ more tractable, or the same non-perturbative input?

**The same, on all three counts:**

1. **Same object.** `√σ = Λ` (`stringTension_is_condensate_scale`, `rfl`) — the confinement scale is
   the condensate scale.
2. **Same obstruction.** `√σ = exp(−c/β₀g²)`, non-perturbative, essential singularity, invisible to
   polynomial/analytic bounds (§3, mpmath).
3. **Easy direction only, like the condensate.** `√σ_k` is geometric, summable, anchor-dominated
   (`continuumStringTension_anchorDominated`, `Σ ≤ 1/40 < 3/10 ≤ m_phys`) — but this is an UPPER
   bound (small erosion = good). The mass gap needs the scale GENERATED nonzero (the opposite,
   harder direction), which is the open non-perturbative generation, not constructed.

**And even if √σ > 0 were proved, it would not close the gap:** confinement is a SEPARATE premise
(`areaLaw_massGap_independence` / `confinement_gap_independent`) — no bridge `area law ⟹ gap`.

## 5. MAXIMAL SCRUTINY (task point 5) — did it close and cascade? NO

The STOP-and-audit condition triggers only if the route inhabits a guarded frontier bundle. **It
does not.** Field-by-field:

| claim | status | Lean |
|---|---|---|
| OS2 reflection positivity (all orders, all real c) | **PROVED** | `os2_reflection_positivity_holds` ⟵ `reflectionPositiveSchwinger_holds` |
| fixed-spacing OS gap `107/108` | **PROVED** (upstream) | `reconTransfer_located_gap` |
| continuum OS gap = spacing-uniform decay (not a bypass) | **PROVED reduction** | `osContinuumGap_of_uniformDecay` ⟵ `uniformPhysicalCorrelationDecay_imp_massGap` |
| fixed-spacing confinement suppression `< 1` (σa²>0) | **PROVED** | `strongCoupling_confinement_suppression` (activity ≤ 1/2 at w=1/2) |
| continuum √σ = condensate scale `exp(−c/β₀g²)` | **PROVED identification** | `stringTension_is_condensate_scale` (`rfl`) |
| √σ ≥ 0 (trivial), √σ summable/anchor-dominated | **PROVED** (easy direction) | `continuumStringTension_nonneg`, `continuumStringTension_anchorDominated` |
| confinement ⊥ mass gap (separate premise) | **PROVED** | `confinement_gap_independent` ⟵ `areaLaw_massGap_independence` |
| **`singleStep` (`realδ ≤ δ_model`)** | **OPEN** | `SingleStepDefectBound` UNINHABITED |
| **continuum `√σ > 0` (generated)** | **OPEN** | `ScaleCovariantWilsonAreaLaw` UNINHABITED |

Nothing inhabits `SingleStepDefectBound`, `MassGap`, `ScaleCovariantWilsonAreaLaw`, or any of the
5 guarded frontier types. The verdict bundle `os_confinement_verdict : OSConfinementVerdict` collects
only PROVED conditional facts / re-exports.

## 6. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (721 jobs).
```

New file `lean/YMGap/Continuum/OSConfinementAssessment.lean` (wired into `YMGap.lean`), Lean-core
only (`Q'`/`Nat` + reused `CReal`/`ExpNeg`), no Mathlib/`ring`/`native_decide`/`Classical`/`sorry`.
`#print axioms` on all 8 load-bearing decls ⊆ `{∅, [propext], [propext, Quot.sound]}`:

```
os2_reflection_positivity_holds            : [propext, Quot.sound]
osContinuumGap_of_uniformDecay             : [propext, Quot.sound]
strongCoupling_confinement_suppression     : [propext, Quot.sound]
stringTension_is_condensate_scale          : [propext, Quot.sound]
continuumStringTension_nonneg              : [propext, Quot.sound]
continuumStringTension_anchorDominated     : (none)
confinement_gap_independent                : [propext, Quot.sound]
os_confinement_verdict                     : [propext, Quot.sound]
```
Numerics: `string_tension_numerics.py` (mpmath dps 50, exact `fractions`/Bessel). Committed: nothing.

## 7. HONEST FINAL VERDICT

The OS/confinement route — the last major untried mechanism — is a genuine gap mechanism at fixed
spacing (OS2 PROVED, fixed-spacing OS gap `107/108` PROVED, fixed-spacing string tension `σa² > 0`
PROVED-analog), but on the sole open field `singleStep` it **neither closes it directly nor is more
tractable nor bridges to it**:

- **Does NOT give `singleStep` directly.** The OS mechanism reduces the continuum gap to the SAME
  spacing-uniform correlator decay `UniformPhysicalCorrelationDecay` (⟹ `singleStep`) — the a→0
  uniformity of the OS spectrum IS the open input.
- **Confirms the SAME non-perturbative core (4th route), via a different quantity.** The continuum
  string tension `√σ = Λ = exp(−c/β₀g²)` is DEFINITIONALLY the same essential-singularity condensate
  scale (`stringTension_is_condensate_scale`, `rfl`); string tension vs fluctuation defect is a
  different observable but NOT a more tractable one — same renormalon obstruction (mpmath),
  same easy-direction-only summability.
- **Orthogonal / separate premise.** `mass gap ≠ area law`: confinement is carried as an INDEPENDENT
  premise with no bridge (`confinement_gap_independent`), so even a proven continuum √σ > 0 would not
  close the mass gap.

This is the **4th independent confirmation** that the binding obstruction is the non-perturbative
condensate positivity `Λ = exp(−1/2β₀g²) ≠ 0` (block-spin, Borel, curvature, and now OS/confinement
all land on it). The confinement route sees it through the string tension `√σ = Λ`, a genuinely
different physical quantity, but the same irreducible input. No guarded frontier bundle is inhabited;
nothing is faked; the 4D Yang–Mills mass gap remains **OPEN** — and the next attack is still the
interacting per-step fluctuation bound (`singleStep` / fusion-local-CLT), not the area law.
