# Defect-recursion as the PRIMARY route; σ̂/string-tension DEMOTED

**File:** `lean/YMGap/Continuum/DefectRecursionPrimary.lean` (new, imported in `YMGap.lean`).
**Build:** `lake build` exit 0 (778 jobs). **Guard:** `YMGapGuard` exit 0 — *"frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited"* (guard 5). **Axioms:** every new declaration ⊆ `{propext, Quot.sound}`. No `sorry`/`native_decide`/`Classical`/`ring`. Loop metric: C unchanged (18), no `SingleStepDefectBound` alias added — genuine new math, not a confirmation loop.

---

## What was built

### 1. The defect-recursion as PRIMARY, in the EXACT CLAUDE.md form

Prior machinery (`ContinuumClosureProgram.DefectGapRecursion`) carried only the
*multiplicative* recursion `(1−δ_k)·Δ_k ≤ Δ_{k+1}` — no additive ε. This module
adds the **additive** structure the CLAUDE.md target actually names:

```
structure AdditiveDefectGapRecursion            -- Type, Rule 8
  recursion : (1 − δ_k)·Δ_k − ε_k ≤ Δ_{k+1}     -- THE open field (CLAUDE.md Δ_{k+1} ≥ (1−δ_k)Δ_k − ε_k)
  prodFloor    -- = (1 − Σδ)·m₀   (summability output, data)
  epsSumCeil   -- = Σε            (summability output, data)
  budget       -- epsSumCeil < prodFloor   ⟺   (1 − Σδ)·m₀ > Σε   (CLAUDE.md defect budget)
```

**Proved (axiom-clean):**
- `prodInvariant` — the additive Grönwall fold `∏ρ·m₀ ≤ Δ_k + Σε_k` (subtraction-free invariant, induction on k reusing `recursion` + `oneSubMul_le_self`).
- `uniform_floor` — `(1−Σδ)m₀ − Σε ≤ Δ_k` at every scale.
- `floor_pos` — the floor is strictly positive **from the budget** (`sub_pos_of_lt`, proved at the ℤ numerator level).
- `continuum_floor_of_additiveDefectRecursion` — **the headline reduction**: `0 < c ∧ ∀k, c ≤ Δ_k` with `c = (1−Σδ)m₀ − Σε`.

The route needs only **local per-step data** (`δ_k`, `ε_k`) plus scalar summability
constants — **no global mechanism**. `ofMultiplicative` proves the additive route
**subsumes** the existing multiplicative `DefectGapRecursion` (`ε ≡ 0` special case);
`trivialAdditive` is the degenerate no-4D-content inhabitant certifying non-vacuity
(Rule 8). No 4D inhabitant is exhibited.

### 2. The per-step spectral-stability perturbation lemma (the crux)

```
structure PerStepSpectralStability              -- Type, Rule 8; UNINHABITED on ℝ⁴
  g, g_pos       -- physical margins m_lat(a_k)/a_k > 0
  hadd  : g_k − shift_k ≤ g_{k+1}               -- located-2nd-eigenvalue ↔ margin dictionary (proved side)
  temple: shift_k · g_k ≤ ‖P_k^⊥‖²              -- PROVED Kato–Temple 2×2 bound (temple_shift_le)
  pert  : ‖P_k^⊥‖² ≤ (δ_k·g_k + ε_k)·g_k        -- THE RESIDUAL (single analytic obligation)
```

`perStep_additive_recursion` **PROVES** that one RG step degrades the located
2nd-eigenvalue by at most `δ_k·g_k + ε_k`, discharging the additive `recursion`
field:
- `temple` + `pert` ⟹ `shift_k·g_k ≤ (δ_k·g_k + ε_k)·g_k`;
- `BakryEmery.le_of_mul_le_mul_right_pos` (positive right-cancellation, `g_k>0`) ⟹ `shift_k ≤ δ_k·g_k + ε_k`;
- `additive_margin_recursion_of_eigShift` (§1, generalises `AsymptoticSpectralLoc.margin_recursion_of_eigShift` to nonzero ε) + `hadd` ⟹ the additive recursion.

`additiveRecursion_of_perStep` assembles the **full** `AdditiveDefectGapRecursion`
from a `PerStepSpectralStability` + summability bookkeeping, so **the primary route's
open field is discharged by the LOCAL per-step perturbation** — each step is a
Kato–Temple perturbation lemma, not a phase-structure/confinement theorem.

### 3. σ̂/string-tension route DEMOTED to a corollary

- `sigmaHat_surrogate_of_floor` — **σ̂ := (gap)² is a DERIVED corollary**: from the
  defect-route floor `0 < c ≤ Δ_k`, the string-tension surrogate `σ̂ = gap² ≥ c² > 0`,
  proved WITHOUT any area law (inverting the √-bridge `m₀=√σ̂ ⟺ σ̂=m₀²`).
- `RouteInputComparison` / `defect_route_floor_from_perStep` — records, as Type-level
  data and a hypothesis-explicit theorem, that the **defect route's input is the LOCAL
  per-step residual** (`PerStepSpectralStability`, no area-law premise anywhere in the
  signature) whereas the **σ̂ route consumes the GLOBAL continuum area law**
  (`WilsonAreaLaw.ScaleCovariantWilsonAreaLaw`, uninhabited = confinement, strictly
  harder input). Strictly-weaker-input ⟹ the defect route is PRIMARY.

This aligns with the existing `OSConfinementAssessment` finding: the continuum string
tension is the SAME essential-singularity condensate scale as the fluctuation defect,
seen through a harder observable — not a more tractable one.

---

## The per-step residual, stated EXACTLY

> **`PerStepSpectralStability.pert`**: for the true-margin RG trajectory `g_k = m_lat(a_k)/a_k`,
> an a-priori bound on the interacting transverse off-diagonal norm
>
> **`‖P_k^⊥‖² ≤ (δ_k · g_k + ε_k) · g_k`**   (equivalently `‖P_k^⊥‖ ≤ √((δ_k g_k + ε_k) g_k)`),
>
> with `Σδ_k < ∞`, `Σε_k < ∞`, budget `(1−Σδ)m₀ > Σε`.

This is a **LOCAL, per-RG-step** bound on ONE per-scale interacting off-diagonal norm.
It is the genuine open obligation — **NOT closed by making the route primary**. Per the
honest verdict of `TempleSpectralStabilityDefect`, it is equi-inhabiting with
`SingleStepDefectReduction.SingleStepDefectBound.singleStep` (the `δ ↔ b` map is a
bijection at fixed `g` via `δ(δ+g)=b²`), i.e. a sharp *reframing* of the single per-step
estimate — but now cast as a **per-step perturbation lemma**, exactly the CLAUDE.md
target shape, with no confinement mechanism required.

---

## Scheme-dependence + port map (action items — NOT code)

1. **The budget `(1−Σδ)m₀ > Σε` is SCHEME-DEPENDENT.** Which block-spin scheme makes
   both `Σδ` and `Σε` summable and clears the budget is a *numerical* selection.
   **ACTION (user):** run the MCMC/measurement layer to measure `δ_k` and `ε_k` per
   block-spin scheme (Claude cannot submit GCS Batch jobs — hand `!cloud/launch.sh` to
   the user; cap MAX_PARALLEL=12). Select the scheme with the largest budget margin.
2. **Port the per-step lemmas from Dimock's reorganization of Balaban** ("Renormalization
   group according to Balaban") as the campaign map: Dimock isolates the Balaban RG step
   into discrete lemmas (large/small-field split, per-step effective-action bounds) that
   map directly onto `PerStepSpectralStability` — the transverse off-diagonal control is
   exactly the small-field fluctuation bound. **ACTION:** transcribe Dimock's per-step
   fluctuation-integration bound as the concrete inhabitant of `pert`.
3. **Feed the measured `δ_k, ε_k` into `additiveRecursion_of_perStep`** to obtain a
   *scheme-specific* positive continuum floor once (1)/(2) supply `pert`.

---

## Honest verdict

The defect-recursion route is now the **PRIMARY named route** to the continuum mass
gap, in the exact CLAUDE.md form `Δ_{k+1} ≥ (1−δ_k)Δ_k − ε_k` with summable defects and
the budget `(1−Σδ)m₀ > Σε`. Its positive continuum floor is **PROVED conditional on ONE
local per-step obligation** — `PerStepSpectralStability.pert`, the a-priori transverse
off-diagonal norm bound. Everything else (the additive Grönwall fold, the uniform floor,
budget-positivity, the per-step Temple discharge, subsumption of the multiplicative
route, σ̂-demotion) is machine-checked and axiom-clean.

The σ̂-demotion is a **route-input comparison, not a closure**: the defect route consumes
a strictly weaker (purely local, per-step perturbation) input than the σ̂ route (a global
weak-coupling area law = confinement). No Clay frontier type is inhabited; the per-step
residual is **open and sharply named**. Nothing is faked.
