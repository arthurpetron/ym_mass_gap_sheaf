# AUDIT: convenience constants in strong-coupling guards, rates and thresholds (2026-11-16, base c29e1688)

**Label: audit only. Nothing is fixed. No Lean edits or runs.** Scope: the strong-coupling seed chain behind `uniformRate_of_guards`, plus closely related activity interfaces.
A constant is listed as **LOOSE (verified)** only where I read the proof and found the tighter value already constructed or supported by an existing parametric lemma.
Otherwise it is marked **SUSPECTED** or **NOT LOOSE**.
Reach is the largest nome w for which the uniform-rate guard holds, using the exact guard formula with A(δ) = (2δ+δ²)(1−δ)^(−48), evaluated in floating point (box python).
Baseline: δ = 128w³, the 625 guard, **w ≤ 1/55.0** (`inv55`).
All reach gains are in the abelian-valid strong-coupling regime, so **none is non-abelian evidence**. Not chart closure.

## Ranked by reach gained (alone from baseline; "+A" = combined with item A)
| rank | item | status | reach alone (625) | with A (384) | fix cost (import closure) |
|---|---|---|---|---|---|
| 1 | E: sharp face character cap n+1 | SUSPECTED | 1/17.3 | 1/14.8 | ≥ 2856 modules plus new SOS math |
| 2 | B: n = 1 character cap 32 → 5 | **LOOSE (verified)** | 1/23.5 | **1/20.1** | 2856 modules (`QuaternionHaarCharacterInterval` closure) |
| 3 | D: fixed time rate 1/4 (`comparisonCoreRate` = 1/384) vs any rate < 1 | **LOOSE (verified)**, with a w-dependent rate | 1/31.1 (96·A < 1) | (with B: 1/13.3) | 62+ modules plus every `timeRate` consumer (Robust3 budgets) |
| 4 | C: geometric tail factor 2 → 1/(1−32w³) | **LOOSE (verified)** (subsumed by B) | 1/43.6 | 1/37.4 | 2856 modules |
| 5 | A: 625 guard → 384 guard in the descent chain | **LOOSE (verified)** | — | **1/47.1** (instance 1/48) | **64 modules** (see PLAN-FIX-625) |
| 6 | G: collar exponent 48 in `adjustedCoreRate` | SUSPECTED (unchecked) | ≈ 1/46.6 even at 24 (with A) | ~1 % | 1761 modules |
| — | F: 625 DFS animal degree in the older chain | SUSPECTED | no effect on seed reach | — | 9164 modules |
| — | J: `strongCoupling_areaLaw` constant 4 on w ≤ 1/2 | **LOOSE (verified)** | interface only (no TM reach) | — | small |
| — | H, I: pilot nome 1/1024; `wH = 1/100000` | NOT LOOSE (instances / design choices) | — | — | — |

## Items
**A. 625 guard in the descent seed chain.** `RG/StrongCouplingNomeThreshold.lean:53` (`SCGuards`), :61 (`threshold`), and the hypotheses at `BF4ExactSlabDescentDistanceDecay.lean:160`, `BF4ExactSlabDescentSelectedCovariance.lean:65,113`,
`BF4WilsonDescentUniformConnectedDecay.lean:95`, `BF4WilsonAllNomeStrongCouplingUniformRate.lean:230,286,345,359,373,385`.
- The proof uses only `adjustedCoreRate ≤ 1/384` (`oldGuard_coreRate_le` :77, `comparisonCoreRate` :70), and the real count is 96 (:49).
- Tight value: 384·adjustedCoreRate ≤ 1. w = 1/48 gives 0.940; 1/47 gives 1.005.
- Cost: 8 files, about 14 statements, 64-module rebuild. Full plan in `PLAN-FIX-625-GUARD-IN-PLACE-2026-11-16.md`.

**B. n = 1 character interval cap.** `Continuum/QuaternionHaarCharacterInterval.lean:74–76`: `characterInterval := (Interval.ofSquare (character_squareBound P n)).weaken (characterCap_le n)`.
- The un-weakened interval already has cap `characterBound n + 1` (`Interval.ofSquare` gives c+1, `QuaternionHaarPolynomialInterval.lean`, `ofSquare`). `characterBound 1 = (2·2)·1 = 4`
  (`QuaternionHaarPolynomialSquareBound.lean:196–199`), so the constructed n = 1 cap is **5**, while `heatTermBound w 1 = coeffW w 1 · 2·16 = 64w³` uses **32** (:78, :68).
- Proposed: δ′ = coeffW w 1 · 5 + 2·heatTermBound w 2 = 10w³ + 3072w⁸. The tail is restarted at n = 2 with the same `heatTermBound_step`/geometric argument (:97, :109) under `heatRatio ≤ 1/2`.
  The 3072w⁸ term is ≈ 1e-7 at w = 1/20, negligible.
- Reach: 625 guard 1/23.5; 384 guard **1/20.1**; 96 guard 1/13.3.
- Cost: `heatRemainderBound` (:82) is a definition used by 305 files. The closure of `QuaternionHaarCharacterInterval` is **2856 modules**. `heatRemainderBound_eq` (the literal 128) is used in 6 files, which need re-proving.
  Pointwise `decide` facts at fixed nomes stay true (δ′ ≤ δ) but re-run.

**C. Tail factor 2.** `heatPositiveLabels_bound` (:118–129) sums the positive labels with ratio `HalfPow.half`, so the factor is 2.
- `geoTailBase_series_le` (`HeatKernelConvGen.lean:401`) takes any ratio 0 < r < 1, so r = heatRatio w = 32w³ is supported, giving δ = 64w³/(1−32w³).
- Reach 1/43.6 (625) and 1/37.4 (384). Subsumed by B. Same cost as B.

**D. Fixed time rate 1/4.** `timeRate = entropyRate 96 comparisonCoreRate` (`BF4WilsonDescentUniformConnectedDecay.lean:45`).
- `connectedNumerator_distance_bound` (`BF4ExactSlabDescentDistanceDecay.lean:145`) already proves decay at rate 96·adjustedCoreRate under 96·adjustedCoreRate < 1, so a w-dependent rate is supported.
- Reach 1/31.1 (with B, 1/13.3). The rate then tends to 1 at the edge of the range.
- Cost: `timeRate` is a global constant consumed by `uniformSeedGap_of_guards` (budget < timeRate), the crossover instances and the Robust3 `relativeRate timeRate capDelta` budgets. Those budgets may fail with a weaker rate. Large; it needs its own scope.

**E. Sharp |χ_n| ≤ n+1 on faces (SUSPECTED).** The SOS defect identity `(s+1)² − U_s² ≅ 4(1−x²)Σ…` exists, and `character_square_haar_le` (`SU2CharacterHaarBound.lean:221`) gives H(χ_s²) ≤ (s+1)² for a single link.
- But (i) its docstring marks the plaquette radius multiplicativity **OPEN**, and (ii) `Interval.ofSquare` turns a square cap c into an interval cap c+1, not √c. For n = 1 a square cap of 4 still yields 5, the same as B.
- An interval cap of n+1 needs a linear certificate. That is not verified. Ideal reach 1/17.3 (625) and 1/14.8 (384).

**F. 625 as a genuine DFS animal degree (SUSPECTED).** K = (24+1)² = 625 (`ClusterCount4DProgress.lean:44,300`), used as an actual rate `entropyRate 625 (adjustedCoreRate …)` in 239 files.
- Examples: `BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.lean:73–79,156–164`; `BF4ExactSlabCovarianceAmplitudeDyadicScale.lean:39–48`.
- The descent recoding to 96 is proved only for the connecting-core family. Applying it elsewhere is unverified.
- Not on the seed `uniformRate_of_guards` path once A is applied. Closure: 9164 modules.

**G. Collar exponents (SUSPECTED, unchecked).** `adjustedCoreRate = pairedHeatRate w · inverseFaceFloor⁴⁸` and `probePrefactor = inverseFaceFloor^(12·links)` (`BF4ExactSlabCollarAdjustedRate.lean:44–48`).
- I did not verify which geometric count 48 represents. The reach effect is tiny anyway: (1−δ)^(−48) ≈ 1.06 at δ = 1.2e-3, and halving the exponent moves 1/47.1 to 1/46.6.

**J. Area-law activity interface.** `StrongCouplingPlaquetteActivity` / `strongCoupling_areaLaw` (`WilsonAreaLaw.lean:204,220`) fix `4w³` on `w ≤ 1/2`.
- `plaqActivity_le_gen` (`OffDiagonalActivityBound.lean:122`) proves `plaqActivity w M ≤ cQ·w³` whenever `2 + 2wHi⁵·cQ ≤ cQ`. At wHi = 1/2 that allows cQ = 32/15 ≈ 2.13 instead of 4, and any wHi < 1 with cQ = 2/(1−2wHi⁵).
- This affects only the area-law interface, not hcross/TM reach. Cost: one module plus its importers.

**H, I (not loose).**
- The pilot nome `nome = 1/1024` (`BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`) is an instance, already superseded by `scGuards_of_le_inv55`.
- `wH = 1/100000`, `epsH = 5e-15` (`SU2LinkDecayHeat.lean:75–78`): the side condition 4w³(1+c) ≤ c with that ε allows w ≤ 1.08e-5, so wH is tight for the chosen ε. ε is a design choice.

## Summary
- Verified-loose items on the seed path: A (cheap, 64 modules → 1/48), B (2856 modules → about 1/20 together with A), C (subsumed), and D (rate design; affects Robust3).
- None reaches w = 1/8. Even E plus the 96 guard gives only 1/9.8, consistent with the STOP note's ceiling of about 0.10. Reaching 1/8 needs the orthogonality expansion (SCOPE-SU2-ORTHOGONALITY).
