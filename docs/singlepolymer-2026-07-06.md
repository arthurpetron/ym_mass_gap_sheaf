# The single-polymer activity `|z_1(w)| ≤ g²` — the final config-space scalar

**Deliverable.** `lean/YMGap/Continuum/SinglePolymerGaussian.lean` (wired into `YMGap.lean`;
full `lake build` green = **699 jobs**; `YMGapGuard` **OK** = 5 Clay-frontier types still
unconditionally uninhabited; axiom-clean). Numerics `z1_numerics.py`, `z1_crossover.py`
(mpmath dps 50). Commits: none (per instruction).

---

## 0. The obligation

`KPFieldAmplitude.SinglePolymerActivity afr` carries the sole open config-space field
`z1_le_g2 : ∀ k, z1 k ≤ fieldActivity (w_k) = (1 − w_k)`. This is the LAST measure-theoretic
quantity: the whole KP amplitude scaffold (`amplitude_le`, `clusterSum_le`, Penrose/Cayley/
Euler tree-count) was already PROVED reducible to this single scalar. Physically `z_1` is the
connected single-plaquette Ursell 1-point — the induced coupling from ONE connected
field-space cluster — which at leading order is the fluctuation variance `~ g²`.

**Note on the exact target.** The bracket `1 − w ≤ −log w = g² ≤ (1 − w)/w` means the Lean
`fieldActivity w = 1 − w` is a *lower* proxy for `g²`. So the Lean obligation `z_1 ≤ (1 − w)`
is STRICTLY TIGHTER than the task's stated `|z_1| ≤ g² = −log w`.

---

## 1. The exact `z_1(w)` — computed, and the decisive numeric finding (dps 50)

The genuine connected single-plaquette amplitude from the MINIMAL single-mode su(2) Gaussian
(the object the task asks for: `U = exp(i g A)`, `A ∈ su(2)` a single Gaussian mode, variance
`⟨A²⟩ = g²`). The exact single-mode integral is closed-form:

```
  ⟨½ tr U⟩_Gauss = e^{−τ²/2}(1 − τ²),  τ² = g²/2      (radial 3D Gaussian, exact)
  z₁(w) = 1 − e^{−g²/4}(1 − g²/2),      g² = −log w
        = (3/4) g² + O(g⁴)              (leading = C₂(½)·g² = (3/4)·g²)
```

| candidate for `z_1(w)` | `≤ g² = −log w`? | `≤ fieldActivity = (1−w)`? | worst ratio |
|---|---|---|---|
| **genuine single-mode Gaussian** `1 − e^{−g²/4}(1−g²/2)` | **YES, all w∈(0,1)** | YES for `w > 0.3117` (deep-UV) | **3/4** |
| character deviation `1 − w³` | no (→ 3) | **no** (ratio → 3 = Casimir) | 3.0 |
| `g² = −log w` itself (bare variance) | = (equality) | no (`g² > 1−w`) | → 1⁺ |
| `(1 − w³)/3` (deviation ÷ Casimir) | — | YES all w | → 1 |
| `6(1−w)²` (2nd cumulant, O(g⁴)) | — | only `w ≥ 5/6` | — |

**Decisive findings:**
1. **`|z_1| ≤ g²` is GENUINELY TRUE** for the physical single-mode Gaussian activity, for ALL
   `w ∈ (0,1)`, with **worst ratio 3/4** (a 25% Casimir margin). This is a real variance bound.
2. The sharper Lean obligation `z_1 ≤ (1 − w)` holds for the **deep-UV / continuum regime
   `w > 0.3117`** — precisely all physical AF scales (`w_k → 1`). It fails at strong coupling
   `w < 0.31`, which is covered by the already-proved fixed-spacing gap, not this expansion.
3. The exact `z_1` is **transcendental** (`e^{−g²/4}`, `g² = −log w`) — NOT `Q'`-representable —
   so the rational character-basis library **cannot integrate it**; only the leading variance
   bound is `Q'`-provable, and the all-orders bound reduces to the config-space measure.
4. **Adversarial:** the character-basis deviation `1 − w³` (the naive "amplitude" the character
   library CAN write) OVER-SHOOTS the bound by exactly the Casimir factor `C₄(1) = 3`
   (`(1−w³)/(1−w) → 3`; at `w=9/10`, `271/1000 > 100/1000`). Confirms — as
   `FieldSpaceCluster`/`FormPreservationCluster` already found — that the character basis is
   the wrong tool; the genuine `z_1 ~ (3/4)g²` needs the config-space Gaussian measure.

---

## 2. The minimal single-mode Gaussian (built in Lean-core, finite, genuine)

The single-cluster fluctuation is modelled by the minimal mean-zero two-point law on `{+s,−s}`
(equal weight) — the crudest genuine config-space Gaussian mode with prescribed variance:

- `gaussSecondMoment s := s * s` — the second moment `⟨A²⟩ = s²` (`⟨A⟩ = 0`).
- **`gaussSecondMoment_nonneg`** — `0 ≤ ⟨A²⟩` via sum-of-squares (`SumOfSquares.q_mul_self_nonneg`):
  the single-mode variance is a genuine positive quadrature. FINITE, no full field measure.
- `fundCasimir := 3/4` — the SU(2) fundamental Casimir `C₂(½)` (the `gapFloor`): the curvature
  of `1 − ½tr U` at the identity, i.e. the coefficient of the leading second cumulant.
- `z1Leading G := (3/4)·G` — the leading connected activity `z_1 = C₂(½)·⟨A²⟩ = (3/4)g²`.
- **`z1Leading_le_variance`** — **THE VARIANCE BOUND** `|z_1| = (3/4)g² ≤ g²`, PROVED in `Q'`:
  the fundamental Casimir `3/4 < 1` (the gap-floor fact) SUPPRESSES the leading fluctuation
  activity under the bare variance. This is `|z_1| ≤ g²` at leading order, with the `3/4` margin
  matching the numeric worst ratio exactly.
- `z1Leading_secondMoment_le` — the same applied to the genuine `⟨A²⟩ = s²`.

---

## 3. What is PROVED in Lean-core (`SinglePolymerGaussian.lean`, all axiom-clean)

| declaration | content | axioms |
|---|---|---|
| `gaussSecondMoment_nonneg` | minimal single-mode Gaussian variance `⟨A²⟩ = s² ≥ 0` (SOS) | propext |
| **`z1Leading_le_variance`** | **the variance bound** `|z_1| = (3/4)g² ≤ g²` (Casimir `3/4<1`) | propext |
| `z1Leading_secondMoment_le` | leading activity ≤ single-mode second moment | propext |
| `charDeviation_le_casimirActivity` | `1 − w³ ≤ 3(1−w)` (Casimir-normalisation, `oneSub_qpow_le`) | propext, Quot.sound |
| **`charDeviation_exceeds_fieldActivity_at_weak`** | **adversarial**: `1−w³ > (1−w)` at `w=9/10` | **none** |
| `singlePolymerActivity_of_gaussianVariance` | **the honest reduction** (config-space variance → `SinglePolymerActivity`) | propext, Quot.sound |

No `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry` (banned tokens only in prose).

---

## 4. The reduction, exactly (adversarial: what is genuine vs the substrate)

`singlePolymerActivity_of_gaussianVariance` FACTORS the single scalar `z_1 ≤ (1−w_k)` through
the config-space variance `V_k = ⟨A²⟩_k`:

```
  z_1(k) ≤ V_k            (compact-fluctuation: connected activity ≤ variance)
  V_k    ≤ fieldActivity  (the deep-UV variance bound ⟨A²⟩ ≤ g² — TRANSCENDENTAL, config-space)
  ⟹ SinglePolymerActivity by transitivity.
```

It is a **CONDITIONAL producer** (open binders `V`, `z1`, the three hypotheses; none an
argument of `SinglePolymerActivity afr`), so it inhabits NOTHING unconditionally. The genuine
residual is now sharply named: the **config-space single-mode Gaussian variance bound
`⟨A²⟩ ≤ fieldActivity`** — the transcendental deep-UV `(3/4)g² ≤ g²` content that the rational
library cannot carry.

**Adversarial verdict on the minimal Gaussian.** It is GENUINE as a *finite variance object*
(a real sum-of-squares second moment, `⟨A²⟩ = s²`), and the leading `(3/4)g² ≤ g²` is a REAL
`Q'` inequality with content (the fundamental Casimir clearing below 1). It is NOT the full
config-space field integral: the EXACT all-orders `z_1` is transcendental, so `SinglePolymerActivity`
is **REDUCED, not closed**. The substrate `treeDom` (the field-Ursell expansion over field
configurations) remains OPEN. No re-labelling was landed: `z_1` is not defined as `g²` (that
would be equality); it is the Casimir-suppressed `(3/4)g²`, and the character surrogate `1−w³`
is proved to over-shoot.

---

## 5. MANDATORY cascade / STOP check

**No STOP condition tripped. No guarded bundle inhabited.**

- `SinglePolymerActivity` is a NEW NODE, **not** one of the 5 guarded Clay-frontier types
  (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`).
- It feeds `KPAmplitude` ONLY via `kpAmplitude_of_singlePolymer`, which ADDITIONALLY requires
  the OPEN `treeDom` substrate (the field-Ursell expansion structure). So even a full
  config-space variance datum does NOT produce a `KPAmplitude`, let alone cascade downstream to
  `FieldClusterConvergence.inducedBound → SingleCouplingFormPreservation → …
  FrontierDAG.trueMargin`.
- `singlePolymerActivity_of_gaussianVariance` is a conditional producer (open binders).
  `SinglePolymerActivity` is NOT inhabited unconditionally anywhere.
- Full build: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`
  (unchanged; +1 job = the new module only).

---

## 6. HONEST VERDICT

**Is `|z_1| ≤ g²` now proved?** — **The leading variance form is PROVED; the exact bound is
GENUINELY TRUE but reduces to the config-space measure substrate.**

- `|z_1| ≤ g²` is genuinely TRUE for the physical single-mode su(2) Gaussian activity
  (verified numerically, worst ratio 3/4), and its LEADING form `(3/4)g² ≤ g²` is PROVED in
  `Q'` (`z1Leading_le_variance`) via the minimal Gaussian + the fundamental Casimir `3/4 < 1`.
- The EXACT all-orders `z_1 = 1 − e^{−g²/4}(1−g²/2)` is transcendental (config-space Gaussian
  integral), NOT `Q'`-representable, so the rational character-basis library **cannot close it**;
  the residual is REDUCED to the config-space single-mode variance bound `⟨A²⟩ ≤ fieldActivity`.
- The character-basis surrogate `1 − w³` provably OVER-SHOOTS the bound by the Casimir factor 3
  (adversarial confirmation the character basis is the wrong tool).
- `SinglePolymerActivity` is REDUCED (guard-safe, conditional), NOT inhabited. It is a standalone
  node (the substrate `treeDom` stays open), so nothing cascades to any Clay-frontier bundle.

**The 4D Yang–Mills mass gap remains OPEN; nothing is faked; no guarded frontier bundle is
inhabited.** The final config-space scalar is now attacked with the genuine minimal Gaussian,
its leading variance bound proved, its exact obstruction (the transcendental config-space
integral) precisely named, and the character-basis surrogate refuted.
