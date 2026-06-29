# Continuum-closure research map (R2): the RG-contraction wall, decomposed

Date: 2026-06-27. Scope: a rigorous, honest research map of the 4D continuum
(`a → 0`) Clay mass-gap wall (R2), an assessment of the renormalization-group
"control-the-dynamics-across-scales" strategy as the closure vehicle, and the
single most tractable genuine reduction to attempt next. **This is OPEN
mathematics.** Nothing below claims R2 is solved or closeable by engineering.
Every claim is tagged PROVED / REDUCIBLE / GENUINELY-OPEN.

---

## 0. What "the continuum limit" actually is (two limits, not one)

The lattice→continuum problem is **two** limits, and conflating them is the most
common error:

1. **Λ → ∞ (thermodynamic / infinite volume), at FIXED spacing `a`.**
   In this development this is essentially constructive and DONE: a genuine
   Kolmogorov-consistent inverse-limit Wilson functional
   (`WilsonRGTower.lean`, multi-edge non-stationary tower with a proved
   consistency theorem), the fixed-spacing strong-coupling cluster bound
   (`GenuineClusterBound` / `NonSaturatedFloor.mFiducial > 0`), and the
   finite-volume located spectral gap (`LocatedSpectralGap`, `CompactTransferGNS`).

2. **`a → 0` (scaling / ultraviolet), with the PHYSICAL scale held fixed.**
   This is R2 proper, and it is GENUINELY-OPEN. The object is a positive
   functional (not a measure on a fixed space — the spaces change with `a`), and
   the gap is the persistence of a positive **physical** mass `Δ(a) = m_lat(a)/a`
   as `a → 0`.

The codebase is scrupulously honest about this split: `RGGapPersistence.lean`'s
own docstring states the anchor (`a₀ = 1`, fixed spacing) rung is PROVED and the
only open content is PERSISTENCE as `a → 0`.

---

## 1. Survey of the existing RG / continuum machinery

For each module: what it GIVES, and what it LACKS.

| Module | Gives (PROVED) | Lacks / NAMED-open |
|---|---|---|
| `RG/BlockSpin.lean` | Refined per-step block-spin type `StepTypeWithBudget` and the four decomposed obligations (S1–S4 sf/lf/cap/σ̂) as `Type`-level Σ′; witnesses closed at `V = Q'` as the **identity step** (all budgets = 0). | The Q'-closures are the *identity* inductive step (budgets 0, certs reused). Quantitatively EMPTY by design — the analytic content lives in `computations/`, not Lean. It is a *shape* certificate, not a contraction. |
| `Continuum/PerScaleContraction.lean` | The EXACT single-link SU(2) heat-semigroup gap `C₂(½)=3/4` and per-block multiplier `ρ=1−3/4=1/4 ∈ (0,1)` — a genuine PROVED inhabitant (Peter–Weyl). | The multi-link / block-spin COMPOSITION uniform in volume: that one single-scale `3/4` contraction survives a block step. Named, NOT inhabited (`rhoOfPerScale` docstring). **This is the central wall.** |
| `Continuum/O4DecayFromMargin.lean` (DimensionalScaling) | PROVED: the irrelevant-operator contraction rate `ρ=blockRatio^{degreeMargin} ≤ 1/4 ≤ 1/2` is EARNED from the proved 24-cell margin `d−4 ≥ 2` + `blockRatio ≤ 1/2`; hence `RotationRestored` follows from `DimensionalScaling`. | The per-step dimensional-scaling law `scale_step` (`breakCoeff(k+1) ≤ blockRatio^{d−4}·breakCoeff k`) itself is the one named input — standard RG-irrelevance content, not derived. |
| `Continuum/SpectralGapGrowth.lean` | PROVED, fully: the geometric-domination kernel `pow_dominates` (`∃n, C·μⁿ < w·λⁿ`) and `gap_of_decay` (clustering ⇒ every populated mode ≤ μ) at FINITE volume. Axiom-clean, no hypotheses. | Nothing missing *here*; it is a finite-volume converse. It does not address `a → 0`. |
| `Continuum/RGGapPersistence.lean` | The whole reduction chain: `RGGapPersistence` (uniform physical floor `c ≤ m_lat(a_j)/a_j`) ⇒ `RegScalingBand` ⇒ `physGapMin > 0` ⇒ `band_gap_survives`. Per-block form `RGBlockPersistence` (recursion `ρ_k·Δ_k ≤ Δ_{k+1}` + product floor) ⇒ uniform, via the PROVED product induction `prodPrefix_anchor_le_physGap`. Anchor rung PROVED. | The `physFloor` field (uniform `c>0` surviving `a→0`) — NO inhabitant for 4D YM. THE open inequality. |
| `Continuum/ContinuumGapLimit.lean` | `ContinuumGapPersistence` interface; PROVED that uniform floor `δ>0` + persistence ⇒ `continuum_mass_isPositive`; `withGap_of_persistence` wires constructed `m_∞` into the existence datum. | Two open fields: `converges` (Λ→∞ thermodynamic limit with explicit modulus) and `floor_persists` (tightness). |
| `Continuum/SigmaHatLimit.lean` | PROVED (UV pilot): uniform positive lower bound `σ̂_N ≥ ε > 0` for the σ̂-budget sequence, framework form. | The pilot is the trivial `η ≡ 0` trajectory (ε=1). A genuine `σ̂_∞ : CReal` limit and a non-trivial η are deferred. Framework precursor only. |
| `Continuum/DynamicToStaticGap.lean` | PROVED: the QUALITATIVE Helffer–Sjöstrand transfer `λ>0 ⇒ m>0` with a located separator `sep<1`, plugging into `decay_of_spectralGap_corr0`. | The SHARP rate `m ≍ √λ` (Combes–Thomas) is NOT encoded (`m:=λ` is a positivity carrier). The SPACING-UNIFORM dynamic gap is the named frontier. |
| `Continuum/GapStability.lean` | PROVED: topological gap PROTECTION — `belowCount` integer invariant, no-crossing ⇒ located gap transports along the flow. Honest caveat `belowCount_blind_to_margin`. | STABILITY ONLY. Presupposes a gap, protects a FIXED separator, and is provably BLIND to the margin shrinking. Cannot deliver a magnitude. Strictly weaker than the quantitative route. |
| `Continuum/HierarchicalGap.lean` | PROVED, UNCONDITIONAL: a positive AND finite continuum gap `physGapMin = cτ/(2a₀) > 0` on the EXACT heat-kernel decimation line (δ=0). | It is NOT 4D YM: decimation is dimension-agnostic and commutes exactly with the heat semigroup. The genuine 4D content is the bond-moving residual `δ`, NOT addressed here. |
| `Continuum/BondMovingQuadratic.lean` | PROVED: the renormalized transverse bond-moving defect is QUADRATIC, `δ_ren(w) ≤ 18p·(1−w)²` (dominant `s=1` mode), hence `≤ C·A²/(k+B)² ∼ 1/k²` along an AF rate — SUMMABLE. | DOMINANT MODE ONLY (`s=1`); full-mode (all `s`) quadratic bound OPEN. |
| `Continuum/AFRateCalibration.lean` | PROVED NEGATIVE diagnostic: `harmonic_diverges` ⇒ the LINEAR defect `∑ 6p(1−w_k) ∼ ∑1/k` can NEVER be summable. Sharp "which estimate can work" result. | `AFRateModulus` (`1−w_k ≤ A/(k+B)`, two-loop AF rate) is a NAMED input, not derived. |
| `Continuum/SummabilityCapstone.lean` | PROVED COMPOSITION: AF rate + renormalized quadratic defect ⇒ inverse-square per-step ⇒ summable ⇒ exponential product floor `∏(1−δ_k) ≥ e^{−2R} > 0` on the tail; UNCONDITIONAL on the canonical AF inhabitant. The floor is on `RGGapPersistence.prodPrefix` of the tail renormalized rates. | DOMINANT MODE + RENORMALIZED + tail `k≥k₀`; full-mode + genuine 4D AF trajectory OPEN. **Crucially the floor is NOT yet wired into `RGBlockPersistence.recursion`** — i.e. the product floor is on the *defect rates*, not yet identified with the *gap-margin* recursion. |

### Synthesis of the survey

The machinery is in remarkably good shape and HONEST. Three independent
"per-scale → uniform" devices exist and are proved:

* **product induction** (`prodPrefix_anchor_le_physGap`) — turns a per-block
  recursion + product floor into a uniform floor;
* **exponential product floor** (`SummabilityCapstone`) — turns a summable
  per-step defect into a positive `∏(1−δ_k)`;
* **geometric domination** (`SpectralGapGrowth`) — finite-volume clustering ⇒ gap.

And the analytic crux is *isolated to one sign-of-the-exponent question* that is
ALSO resolved in principle: the linear defect diverges (`AFRateCalibration`), the
renormalized **quadratic** defect converges (`BondMovingQuadratic`). The marginal
coupling drift is reparametrized away; only the genuine transverse `O((1−w)²)`
residual remains, and `∑1/k² < ∞`.

What is missing is the **JOIN**: nobody has proved that the bond-moving defect
`δ_k` actually *is* the per-step gap-margin degradation multiplier. The product
floor lives on the defect rates; the persistence layer wants it on the gap
recursion. Identifying the two is the open non-abelian block-spin composition step.

---

## 2. R2 decomposed into genuine sub-walls

| Sub-wall | Statement | Status |
|---|---|---|
| **R2a — existence** | Tightness/compactness of lattice Wilson functionals as `a→0` (infinite-dim Prokhorov; d=4 just-renormalizable = hardest). | GENUINELY-OPEN. The codebase deliberately routes around subsequence extraction via a DIRECT Cauchy/modulus (`ContinuumGapLimit.converges`, route-(ii) KP `crealOfGeoIncrement`). Tightness (Conj 7.4) flagged as the *true* analytic blocker. |
| **R2b — O(4) restoration** | Continuous rotational symmetry restored in the limit. | REDUCIBLE (best-developed sub-wall). `O4DecayFromMargin` PROVES restoration FROM one named input (`scale_step`, per-step dimensional scaling), with the rate `≤1/4` EARNED from the proved 24-cell margin `d−4≥2`. Remaining input is the single transparent irrelevant-operator estimate. The 24-cell degree-6 precursor reaches genuinely far. |
| **R2c — uniform gap floor** | `∃ c>0, ∀ a, c ≤ Δ(a) = m_lat(a)/a` along the AF trajectory. | GENUINELY-OPEN (THE central wall). REDUCED, with full reduction chain proved, to one inequality (`RGGapPersistence.physFloor`) and further to the per-step recursion (`ContinuumClosureProgram.DefectGapRecursion.recursion`). Anchor rung PROVED. |
| **R2d — OS / RP survival** | Reflection positivity survives the limit. | LARGELY-REDUCIBLE. Lattice OS2/RP is PROVED unconditionally (Osterwalder–Seiler/Schur, `ReflectionPositivity.lean`); RP is preserved under the (positive, RP-respecting) limit if the limit exists. So R2d is essentially a corollary of R2a — it is not an independent obstruction provided the limit is constructed as a limit of RP lattice theories. |

**Ranking of the four:** R2d ⊏ R2b ⊏ {R2a, R2c}. R2a and R2c are the two genuine
frontiers; R2c is where the RG-contraction strategy bites and where the codebase
is closest to a clean named reduction.

---

## 3. Assessment of the RG-contraction strategy

**Is it the right vehicle? YES — it is the only one of the three that addresses
the right object, the right dimension, and yields a gap MAGNITUDE.**

* Stochastic quantization / regularity structures (Chandra–Chevyrev–Hairer–Shen)
  reaches only 2D/3D and constructs a Markov process on gauge orbits, NOT an OS
  measure and NOT a mass gap. Wrong target, wrong dimension.
* Bałaban's rigorous 4D RG + Magnen–Rivasseau–Sénéor controls the UV problem
  ONLY (SU(2), 4D, trivial sector, small-field approximation), with a fixed IR
  cutoff they deliberately never remove — explicitly because removing it "would
  lead to large coupling … confinement … out of the realm of our constructive
  methods." They achieve UV ultraviolet stability / control of the effective
  action flow down to a fixed scale; they do NOT obtain the mass gap, the IR /
  thermodynamic limit, O(4) restoration, or the full OS axioms. The gap to a
  constructive gap proof is exactly the IR direction they cut off.
* The RG-contraction route is the legitimate constructive form of "faithfully
  model the dynamics across scales": run the block-spin flow as a sequence of
  per-scale contractions and multiply the per-block gap multipliers up.

**Is there a per-scale recursion `m_{k+1} ≥ F(m_k)` with a positive fixed point?**
YES, and it is already formalized in two compatible shapes:

* `RGBlockPersistence.recursion`: `ρ_k · Δ_k ≤ Δ_{k+1}` with uniform product
  floor ⇒ uniform `Δ_k ≥ c > 0` (PROVED reduction).
* `ContinuumClosureProgram.DefectGapRecursion.recursion`:
  `(1 − δ_k) · Δ_k ≤ Δ_{k+1}` with product floor ⇒ uniform floor (PROVED,
  this run). The multiplier is `ρ_k = 1 − δ_k` and the fixed point is positive
  precisely when `∑ δ_k < ∞`.

**The single missing analytic ingredient.** It is NOT the contraction constant
per se (the per-scale `3/4` Casimir gap is exact and proved; the quadratic-defect
summability is proved on the dominant mode). It is the **identification of the
bond-moving transverse defect `δ_k` with the per-step gap-margin degradation
multiplier** — i.e. proving the field

> `(1 − δ_k) · Δ_k ≤ Δ_{k+1}`  (one 4D non-abelian block-spin step)

This is the multi-link composition step: under a block-spin transformation
adjacent links couple, and one must show the single-link heat-semigroup
contraction dominates that coupling uniformly, with the residual being exactly
the (summable, quadratic, renormalized) `δ_k`. Until this is proved, the
summability product floor (`SummabilityCapstone`) sits on the *defect rates* and
the persistence layer wants it on the *gap recursion*; the two are not yet
connected.

**What the codebase already provides toward it:** the exact per-scale gap (`3/4`),
the quadratic defect modulus, the summability endpoint, the exponential product
floor, the product induction, and now the named join (`DefectGapRecursion`) with
its conditional reduction proved. Everything *except* the recursion field itself.

---

## 4. The central obstruction (asymptotic freedom / the flow)

Asymptotic freedom means the continuum (UV) limit of 4D Yang–Mills is reached at
**weak bare coupling** `g → 0`, with the physical scale fixed by dimensional
transmutation `Λ_phys = a^{-1} · f(g(a))`, `f` exponentially small in `1/g²`.
This is the **opposite end** of the coupling axis from the strong-coupling regime
where the lattice mass gap is rigorously proved (Osterwalder–Seiler / Shen–Zhu–Zhu):
strong coupling gives confinement and a gap, but at fixed coarse spacing, NOT in
the scaling limit. The strong-coupling gap therefore does NOT directly give the
continuum gap — they live at different ends of the flow, separated by an
intermediate-coupling region where **neither** the strong-coupling character
expansion **nor** the weak-coupling perturbative expansion converges. Controlling
the flow means propagating a positive *physical* gap across that intermediate
region as `a → 0`, which is exactly the uniform-in-`a` floor R2c — and the reason
no expansion alone suffices is precisely that the convergent expansions live only
at the two endpoints.

---

## 5. The ONE ranked next reduction to attempt

**Target: prove `DefectGapRecursion.recursion` for the dominant-mode renormalized
flow at fixed spacing, conditional on the proved single-link `3/4` contraction and
the proved quadratic defect — i.e. close the JOIN between `SummabilityCapstone`'s
product floor and `RGBlockPersistence`'s gap recursion on the `s=1` mode.**

Concretely, the next genuine Lean step is to PROVE the per-step inequality

> `(1 − δ_ren(w_k)) · gapMargin_k ≤ gapMargin_{k+1}`

for the single-edge / dominant-mode heat-kernel separator, where `gapMargin_k`
is the located margin `1 − sep_k` of `PerScaleContraction`/`LocatedSpectralGap`
at scale `k`, `sep_k` is the heat-kernel `s=1` separator at spacing `a_k`, and
`δ_ren` is the proved renormalized quadratic defect of `BondMovingQuadratic`.
This is one decimation-then-bond-moving block step on the EXACTLY tracked
dominant mode — the same orbit `HierarchicalGap` solves on the decimation line,
now WITH the `δ`-residual reinstated and bounded by the quadratic modulus.

**Why this is genuine progress, not theater.**

* It consumes ONLY proved inputs (`su2PerScale` `3/4` gap; `decimation_step`
  exact separator relation; `bondMovingDeltaRen_quadratic`) plus the *single*
  honest open identification (defect = margin-loss). If it goes through, it
  populates `DefectGapRecursion.recursion` for the dominant mode and — composed
  with `SummabilityCapstone`'s already-proved product floor and the product
  induction — yields an UNCONDITIONAL positive continuum gap floor *on the
  dominant `s=1` mode of the renormalized decimation+bond-moving flow*. That is a
  real, citable theorem (a genuine extension of `HierarchicalGap` off the exact
  decimation line), even though it is not yet 4D YM (full-mode still open).
* It is FALSIFIABLE in the `InternalConnRefines` sense: if `δ_ren` turns out NOT
  to bound the actual gap-margin loss (e.g. because the bond-moving step also
  shifts the *vacuum* eigenvalue, not just the excited one), the recursion will
  fail to close and the formulation will need the right margin definition. That
  is exactly the self-correcting test a named obligation should pass.

**What would be theater (explicitly avoided):**

* Inhabiting `DefectGapRecursion` for 4D YM with a hand-set `δ_k` and no
  derivation — vacuous.
* Setting `δ_k = 0` and declaring victory — that is the `trivialDefectGapRecursion`
  degenerate witness, included ONLY to certify non-vacuity, and labelled as
  carrying no 4D content.
* Wiring the CReal exponential product floor through without the recursion field
  — it would still leave the floor on the defect rates, not the gap.

**Second-ranked (parallel, lower coupling risk):** the full-mode (all `s`)
renormalized quadratic-defect bound, generalizing `bondMovingDeltaRen_quadratic`
from `s=1` to a summable-over-`s` envelope. This removes the "dominant mode only"
scope caveat from `SummabilityCapstone` but does NOT by itself produce a gap
recursion — so it is necessary but not sufficient, hence ranked below the JOIN.

**Explicitly NOT recommended next:** attacking R2a (tightness) head-on
(genuine open math, highest risk, no clean Lean reduction), or the
topological-protection route (`GapStability`, provably cannot deliver a
magnitude), or formalizing Bałaban's effective-action flow (highest cost, does
not reach the gap).

---

## 6. Lean artifact added this run

`lean/YMGap/Continuum/ContinuumClosureProgram.lean` (imported in `YMGap.lean`),
axiom-clean (`[propext]` only, no `sorryAx`, no `Quot.sound`; full library builds,
334 jobs):

* `DefectGapRecursion` — the named open join: a per-scale gap `Δ_k`, a defect
  `δ_k ∈ [0,1]`, the OPEN per-step recursion `(1−δ_k)·Δ_k ≤ Δ_{k+1}`, and a
  uniform product floor. The `recursion` field IS the open content; no 4D
  inhabitant is constructed.
* `DefectGapRecursion.prodPrefix_le_physGap`, `.uniform_floor`, `.physGap_pos`,
  `continuum_floor_of_defectRecursion` — the PROVED reduction:
  `DefectGapRecursion ⇒ uniform positive floor ⇒ continuum gap floor`, reusing
  the product-induction pattern.
* `trivialDefectGapRecursion` — the degenerate (zero-defect) inhabitant,
  certifying non-vacuity, carrying NO 4D content (so labelled).

This module does NOT close any open problem. It isolates the entire R2c continuum
closure into the single `recursion` field and proves everything downstream of it,
so the next attack (Section 5) has a precise, falsifiable Lean target.

## External strategy review — adopted refinements & pushbacks (2026-06-27)

Reviewed an external "ℝ_c-as-base-field" strategy proposal (ladder C0–C10 + a residual-debt
metric). VERDICT: strong INDEPENDENT CONVERGENT VALIDATION of the existing architecture, and a
3rd independent confirmation that the **RG-landing certificate is THE central wall** (cf. the
audited Coq repo's admitted Balaban hypothesis, and our own `DefectGapRecursion`). Most of the
ladder already exists here, often more concretely — so the net is two refinements, not a pivot.

ALREADY HAVE (map of the proposal's ladder onto our code):
- C0 ℝ_c scalar base + axiom-audit invariant  = `CReal` + `make lean-audit` (propext/Quot.sound only).
- C5 finite-lattice reflection positivity       = `ReflectionPositivity` (OS2 proved unconditionally).
- C6 strong-coupling cluster expansion, rational β₀/m = `GenuineKP.genuineKP_sum_le_two`
  (threshold 4/9 ≤ 1/2), `KPCriterion`, `PinnedCluster`, `MultiPlaquetteMayer` (tree clustering).
- C7 transfer-operator gap as SEMIGROUP/power decay, NOT H = −a⁻¹log T = `LocatedSpectralGap` +
  `reconTransfer_located_gap`. (The proposal's C7 instinct — avoid the operator log — CONFIRMS our
  existing choice; we already never build H.)
- C8 RG as certified contraction records        = `DefectGapRecursion` / `PerScaleContraction`.
- C9 continuum limit as Cauchy data with moduli  = `ContinuumGapLimit` / `crealOfGeoIncrement`.

ADOPT (refinements worth taking):
1. **Sharpen the RG-landing TARGET SHAPE to a dimensionless RATIONAL certificate**
   `Σ (q : ℚ_{>0}), ofRat q ≤ m / Λ_YM` — i.e. land the gap as a rational lower bound on the
   dimensionless ratio m/Λ_YM, connecting `DefectGapRecursion.prodFloor` ↔ `DimensionlessRatio`
   (Δ/√σ̂). Cleaner and more machine-checkable than a bare positive floor. STAYS OPEN (it is the wall).
2. **Promote the two-layer scalar discipline ℚ ↪ ℝ_c to a STATED invariant**: `CReal` for semantic
   objects (S_n, expectations, e^{−mr}, m), `Q'` for extracted certificates (q>0, ρ<1, β₀, floors).
   We already practice this; make it explicit project policy and a scorecard expectation.

PUSH BACK (do NOT adopt):
A. **C1 full SU(N)-as-Σ-type matrix-group construction** — DIVERGES from our PROVED worst-case
   reduction (`mass_gap_simple_group`: group-dependence already collapsed to SU(2)). Building
   concrete matrix groups = more work for less generality. Keep the reduction.
B. **C9/C10 "formalize the full continuum objects directly" (constructive Hilbert completion +
   operator semigroup over ℝ_c)** — the proposal's premise OVERESTIMATES our `CReal` stack: we have
   constructive arithmetic / elementary functions / completeness / series, but NO measure-theoretic
   integration, normed-space, or operator/spectral framework. Our finite/located route (located
   2nd-eigenvalue of the COMPACT finite transfer op; continuum as Cauchy data with moduli) is LEANER
   and is a CONSIDERED verdict (R2 frontier: avoid Stone/unbounded). The operator-NORM gap form
   ‖P_Ω⊥ T_t P_Ω⊥‖ ≤ C e^{−mt} belongs in the CLASSICAL EXPORT layer (which the proposal itself
   concedes); our `ClayScorecard.RubricSpectralGap`/`RubricClustering` already carry the constructive
   content. The residual-debt metric ε(r) is rhetorical, not actionable.

BOTTOM LINE: no architectural change. Net adopted = (1) reshape the landing target to the
dimensionless rational certificate q ≤ m/Λ_YM, (2) state the ℚ↪ℝ_c certificate discipline as an
invariant. The wall is unchanged and now triply-confirmed: the asymptotically-free UV flow landing
in a massive IR basin (`RGLandingCertificate`), to be named, isolated, and attacked directly.
