# ε-summability linchpin — verdict

**Target.** Is the Migdal–Kadanoff transverse-bond-moving generated-interaction
leakage `ε_k` SUMMABLE (`Σε_k < ∞`), so the primary defect-recursion budget
`(1 − Σδ)·m₀ > Σε` (`DefectRecursionPrimary.AdditiveDefectGapRecursion`) can close?
The committed numerics (`docs/delta-eps-scheme-select-2026-07-08.md`) selected the MK
`λ ≈ 0.5` scheme but found `ε_k` PLATEAUS at `≈ 0.12–0.15` in the crossover window and
does not visibly decay — flagging possible NON-summability.

**Deliverable.** `lean/YMGap/Continuum/EpsilonSummability.lean` (new, registered in
`YMGap.lean`). `lake build` exit 0 (783 jobs); frontier guard `lake build YMGapGuard`
prints "frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited"; every
load-bearing decl `#print axioms ⊆ {propext, Quot.sound}` (no `sorryAx`, no `Classical`,
no `native_decide`, no `ring`). The two `plateau_matches_*` witnesses depend on NO axioms.

---

## 1. The concrete `ε_k` for MK `λ ≈ 0.5` (identified)

One MK step is `bond-moving ∘ decimation`; bond-moving `p = b³` parallel plaquettes is
the `p`-fold Clebsch–Gordan fusion convolution of the heat-kernel coefficients. `ε_k` =
the deviation of that fused sequence from single-plaquette heat-kernel form = the
numerics' `|√χ_blk(2,2) − √χ_fine(2,2)(β_p)|` — the ADDITIVE defect, distinct from the
multiplicative gap-degradation `δ_k` (physical, scheme-independent). Two faithful
coefficient-level measures, formalized:

- `epsBare afr p k := bondMovingDelta (w_k) p` — BARE (un-renormalized), PROVED
  `≤ 6p·(1 − w_k)` **LINEAR** (`epsBare_le_lin`, via `bondMovingDelta_to_zero`).
- `epsRen afr p k := bondMovingDeltaRen 1 p (w_k)` — RENORMALIZED (marginal
  running-coupling counterterm `renormW` subtracted), PROVED `≤ 6p·(1 − w_k)²`
  **QUADRATIC** (`epsRen_le_quad`, via `bondMovingDeltaRen_le_sixp`; residual
  `3(1−w) − (1−w³) = (1−w)²(2+w)`).

## 2. The summability DICHOTOMY (both halves PROVED, axiom-clean)

Along AF `1 − w_k ∼ 1/k` (`AFRateModulus`, `A'/(k+B) ≤ 1−w_k ≤ A/(k+B)`):

- **LINEAR ⟹ `Σε = ∞` (budget FAILS).** `linearLeakage_partial_unbounded`: any leakage
  with a linear lower bound `c·(1 − w_k) ≤ ε_k` (`c>0`) has UNBOUNDED partial sums — for
  every `R`, `∃ N, R < Σ_{k<N} ε_k`. Reuses the PROVED `AFRateCalibration.harmonic_diverges`
  via a general engine `harmonicLower_partial_unbounded` (`c·A'/(k+B) ≤ ε_k` ⟹ scaled
  harmonic divergence). **A genuinely plateauing/linearly-non-decaying `ε_k` provably
  kills the budget.**
- **QUADRATIC ⟹ `Σε < ∞` (budget CAN close).** `realEpsQuadratic_summable`: given
  `ε_k ≤ 6p·(1 − w_k)²`, every tail window is bounded by `D·1/(N+1)` (uniformly bounded
  partial sums). Reuses the PROVED `FullModeAssembly.fmDefect_summable` (the `Σ 1/k²`
  closure). `epsSumCeil_of_quadraticControl` wires this into the additive budget's
  `epsSumCeil` slot.

So **`ε`-summability ⟺ `ε_k` decays QUADRATICALLY (p≥2), not linearly (p=1).**

The RENORMALIZED MODEL `epsRen` IS quadratic ⟹ `modelEps_summable`: the model leakage is
**UNCONDITIONALLY summable** (pure algebra, no open hypothesis). This closes the MODEL
side of the dichotomy.

## 3. Reduction check (adversarial): equi-inhabits `singleStep`

`RealEpsQuadraticControl` carries exactly the open hypothesis `realEps_k ≤ 6p(1−w_k)²`.
That IS the counterterm-subtracted renormalized-defect bound `δ_model = bondMovingDeltaRen
≤ 6p(1−w)²` asserted by `SingleStepDefectReduction.SingleStepDefectBound.singleStep`.
`EpsQuadraticObligation := SingleStepDefectBound` (Rule-9.8 def-alias, `epsQuadraticObligation_eq`
by `rfl`; `epsObligation_of_singleStep` the identity coercion). **`ε`-summability does NOT
open a new wall — it equi-inhabits `singleStep`**, the campaign's core (and the sharper
`GradedBondMovingBudget.SpectralLocalization`). Both structures are left UNINHABITED for
the real 4D flow.

## 4. Reconciliation with the numerics plateau (crossover artifact)

The plateau `ε ≈ 0.12–0.15` at `β = 2.3–2.5` is a CROSSOVER measurement where
`1 − w ∼ O(1)` (`w ∼ 0.55–0.7`); there quadratic `6(1−w)²` and linear `c(1−w)` are the
same order and numerically INDISTINGUISHABLE. Formalized (decidable, axiom-free):
- `plateau_matches_quadratic`: `6·(3/20)² = 54/400 = 0.135 ∈ [0.12, 0.15]` (quadratic,
  crossover margin `1−w = 0.15`).
- `plateau_matches_linear`: `(3/10)·(9/20) = 54/400 = 0.135 ∈ [0.12, 0.15]` (linear slope
  0.3, crossover margin `1−w = 0.45`).

Both reproduce the plateau. So the plateau is **consistent with, but does not establish,
either branch**: a crossover artifact, NOT proof of non-summability — but NOT proof of
summability either. It FLAGS a genuine RISK. The decisive test (`ε_k` at `β ≥ 2.6`,
`1−w ≪ 1`) is what the numerics doc defers to the cloud, and is exactly `singleStep`.

## 5. HONEST VERDICT

`ε`-summability is the **binding OPEN obligation**, and is **equi-inhabiting
`SingleStepDefectBound`** (NOT a new/separate wall).

- PROVED unconditionally: the renormalized MODEL leakage `epsRen` is summable (quadratic).
- PROVED unconditionally: ANY linearly-lower-bounded leakage is NON-summable (budget fails).
- OPEN (= `singleStep`): whether the REAL 4D `ε_k` obeys the RENORMALIZED quadratic bound
  (marginal counterterm legitimate for the gap) or only the BARE linear one.
- The numerics plateau neither confirms nor refutes summability (crossover artifact), but
  it does SIGNAL a real non-summability RISK — if the real `ε_k` is only linear, the budget
  provably never closes.

The route is **de-risked on the model side and sharply localized** (ε-summability collapses
onto the single existing `singleStep` residual, adding no new wall), but the budget is
**NOT claimed to close**: the real-vs-renormalized quadratic control is unproven. No Clay
frontier type is inhabited; nothing is papered over.

**Guard status:** guard 5 OK (5 frontier types uninhabited). **Axioms:** all new decls
`⊆ {propext, Quot.sound}`; `plateau_matches_*` axiom-free. Build green (783 jobs).
Nothing committed.
