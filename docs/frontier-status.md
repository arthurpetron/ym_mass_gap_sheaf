# Frontier status

> **Auto-generated** by `scripts/frontier_status.py` on 2026-07-18.
> Axiom-gate source: complete current-provenance build log `/tmp/ymgap-full-build-authoritative.log` (exact live gates; baseline exceptions also validated).
> Read-only report — no Lean source is edited. Every bundle below is OPEN
> by design; this only records the current partial closes and the residual
> open fields, parsed mechanically from the sources + the axiom baseline.

The Clay Yang–Mills mass-gap problem remains **OPEN**. This document is a
status ledger, not a claim of closure.

## Summary

| Frontier bundle | Lean type | # partial closes | # open fields |
|---|---|---|---|
| Tier0Scorecard atoms | `Tier0Scorecard` | 6 | 3 |
| ReconstructionScorecardFinal tokens | `ReconstructionOpenFrontier` | 2 | 6 |
| UniformSpacingFloor | `UniformSpacingFloor` | 5 | 0 |
| SpectralMarginInput fields | `SpectralMarginInput` | 3 | 0 |
| SixJPentagon | `SixJPentagon` | 3 | 1 |
| ClayTarget | `ClayTarget` | 1 | 0 |
| ContinuumYMExistence | `ContinuumYMExistence` | 1 | 0 |

## Tier0Scorecard atoms

**(a) Lean type** — `YMGap.Continuum.Tier0Scorecard.Tier0Scorecard`  
module `lean/YMGap/Continuum/Tier0Scorecard.lean`

```lean
structure Tier0Scorecard (p : z4Chain.toLattice.Plaquette) (w : Q') (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type 1
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `fixedSpacing_met` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |
| `subA_offCorr_decompose` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |
| `subA_tree_graph` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |
| `subB_prodFloor_pos` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |
| `subB_physGap_pos` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |
| `toFrontierC` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |

**(c) Fields that remain OPEN:**

- `tTree` — **(T′)** — the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree inequality, over the (D2) lattice `d2Sep.val` (the coupled atom).
- `d1Mayer` — **(D1)** — the absolute Mayer–Ursell connecting-cluster expansion over the CLOSED 4D count `z4ClusterCountBound p`.
- `a2Racah` — **(A2, Level-1 coarse)** — the doubly-stochastic Racah 6j² kernel, a permutation-satisfiable surrogate (`RacahInhabit.racahRP`), carried ...

<details><summary>full field ledger (status by doc-marker)</summary>

| field | status | doc |
|---|---|---|
| `fixedSpacing` | PROVED | PROVED — the legacy fixed-spacing surrogate conjunction. |
| `subA` | — | Historical Sub-wall A; |
| `subB` | — | Historical Sub-wall B package (`hlocalize`, `hbridge`, `hadd`). |
| `d2Sep` | — | **(D2)** — the plaquette-graph `SepLattice` metric refining `z4Chain` (inhabited DATA, carried only to type `tTree`). |
| `tTree` | OPEN | **(T′)** — the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree inequality, over the (D2) lattice `d2Sep.val` (the coupled atom). |
| `d1Mayer` | OPEN | **(D1)** — the absolute Mayer–Ursell connecting-cluster expansion over the CLOSED 4D count `z4ClusterCountBound p`. |
| `a2Racah` | OPEN | **(A2, Level-1 coarse)** — the doubly-stochastic Racah 6j² kernel, a permutation-satisfiable surrogate (`RacahInhabit.racahRP`), carried ... |
| `a2Pentagon` | — | **(A2, Level-2 numeric shape)** — a minimal fractional-6j numeric core `PentagonRelation.PentagonNumericCore`, pinned to `1/4` at the sma... |

</details>

## ReconstructionScorecardFinal tokens

**(a) Lean type** — `YMGap.Rubric.ReconstructionScorecardFinal.ReconstructionOpenFrontier`  
module `lean/YMGap/Rubric/ReconstructionScorecardFinal.lean`

```lean
structure ReconstructionOpenFrontier (D : SmulGNSData) (op : TransferOperator D.toGNSData.gnsComplete) (L : AdditiveTransferOperator D.toGNSData) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w) (N : Nat) : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `reconstruction_status` | `lean/YMGap/Rubric/ReconstructionScorecardFinal.lean` | live exact: Quot.sound, propext |
| `all_fixed_spacing_reconstruction_proved` | `lean/YMGap/Rubric/ReconstructionScorecardFinal.lean` | live exact: Quot.sound, propext |

**(c) Fields that remain OPEN:**

- `node1` — OPEN node ①.
- `OpenNode1FiniteSMargin` = `AcNReserveAnalytic.FiniteSMargin w`
- `OpenTrueMargin` = `ReconstructionScorecard.OpenTrueMargin`
- `OpenPhysicalWilsonBridge` = `WilsonSpectralBridge.CharacterDiagResolution op RCScaleClose.rcScaleResidualPlus w N`
- `OpenBoundedHamiltonian` = `BoundedFunctionalCalculusResidual (excG op w hw0 hw1 N) L`
- `OpenContinuumMinlos` = `ReconstructionScorecard.OpenContinuumMeasure`

<details><summary>full field ledger (status by doc-marker)</summary>

| field | status | doc |
|---|---|---|
| `status` | — | The proved legacy status record. |
| `node1` | OPEN | OPEN node ①. |
| `trueMargin` | — | Historical dimensionless-margin token. |
| `physicalWilsonBridge` | — | Historical Wilson character-diagonalization bridge token. |
| `boundedH` | — | Legacy bounded-log auxiliary, not the canonical unbounded generator. |
| `continuumMinlos` | — | Optional sigma-additive Minlos-style measure packaging. |

</details>

## UniformSpacingFloor

**(a) Lean type** — `YMGap.Continuum.UnifiedContinuumFloor.UniformSpacingFloor`  
module `lean/YMGap/Continuum/UnifiedContinuumFloor.lean`

```lean
structure UniformSpacingFloor {ι : Type} {α : Type} (le : Q' → α → Prop) (g : ι → α) : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `ofUniformPhysGapFloor` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | live exact: Quot.sound, propext |
| `ofModeEnergyFloor` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | live exact: axiom-free |
| `ofContinuumGapPersistence` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | live exact: propext |
| `ofUniformRatioVariation` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | live exact: Quot.sound, propext |
| `ofDimensionalTransmutation` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | live exact: Quot.sound, propext |

**(c) Fields that remain OPEN:**

- (no field flagged OPEN by doc-marker; see the full field ledger below)

<details><summary>full field ledger (status by doc-marker)</summary>

| field | status | doc |
|---|---|---|
| `floor` | — | The uniform positive floor. |
| `floor_pos` | — | The floor is strictly positive. |
| `bound` | — | The floor lies below the per-scale gap quantity at every scale at once. |

</details>

## SpectralMarginInput fields

**(a) Lean type** — `YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput`  
module `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean`

```lean
structure SpectralMarginInput (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `toAsymptotic` | `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean` | live exact: Quot.sound, propext |
| `uniform_floor` | `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean` | live exact: Quot.sound, propext |
| `continuum_floor_pos` | `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean` | live exact: Quot.sound, propext |

**(c) Fields that remain OPEN:**

- (no field flagged OPEN by doc-marker; see the full field ledger below)

<details><summary>full field ledger (status by doc-marker)</summary>

| field | status | doc |
|---|---|---|
| `sl` | — | The graded spectral-localization datum (summable graded defect). |
| `T` | — | The summable-defect exponent descent tower (supplies `ρ = 1−δ`, floor). |
| `hδ` | — | **THE TAIL-SHIFT IDENTIFICATION** — the two product-floor stacks coincide: `T.δ k = sl.gapDefect (k + fmCutoff …)`. |
| `spacing` | — | The lattice spacings `a_j > 0`. |
| `spacing_pos` | — | Each spacing is strictly positive. |
| `atSpacing` | — | The fixed-spacing infinite-volume cluster bounds. |
| `ceilConst` | — | A uniform physical ceiling. |
| `physCeil` | — | The physical gap is bounded above by the ceiling. |
| `anchor` | — | The UV anchor floor `g0 > 0`. |
| `anchor_pos` | — | The anchor is strictly positive. |
| `anchor_le` | — | The anchor bound `g0 ≤ physGap_0`. |
| `shift` | — | The per-mode eigenvalue-shift budget `shift_k = (loc k).shift`. |
| `hadd` | — | **`hadd`** — the located-2nd-eigenvalue ↔ physical-margin dictionary. |
| `hbridge` | — | **`hbridge`** — the shift is controlled by defect·margin (`= bulk_shift`, trajectory form). |

</details>

## SixJPentagon

**(a) Lean type** — `YMGap.Continuum.Tier0Scorecard.SixJPentagon`  
module `lean/YMGap/Continuum/Tier0Scorecard.lean`

```lean
structure SixJPentagon : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `a2_racah` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |
| `a2_tetra_nonneg` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: Quot.sound, propext |
| `pentagon_to_racah` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | live exact: axiom-free |

**(c) Fields that remain OPEN:**

- `pentagon` — **The Biedenharn–Elliott pentagon** — a guarded CUBIC closure of `P` (nonlinear in the kernel).

<details><summary>full field ledger (status by doc-marker)</summary>

| field | status | doc |
|---|---|---|
| `P` | — | The rational dim-absorbed 6j-square kernel underlying the pentagon. |
| `pentagon` | OPEN | **The Biedenharn–Elliott pentagon** — a guarded CUBIC closure of `P` (nonlinear in the kernel). |

</details>

## ClayTarget

**(a) Lean type** — `YMGap.Rubric.ClayScorecard.ClayTarget`  
module `lean/YMGap/Rubric/ClayScorecard.lean`

```lean
structure ClayTarget : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `clay_fixed_spacing_met` | `lean/YMGap/Rubric/ClayScorecard.lean` | live exact: Quot.sound, propext |

**(c) Fields that remain OPEN:**

- (no field flagged OPEN by doc-marker; see the full field ledger below)

<details><summary>full field ledger (status by doc-marker)</summary>

| field | status | doc |
|---|---|---|
| `fixedSpacing` | PROVED | The fixed-spacing clauses — PROVED (`clay_fixed_spacing_met`). |
| `continuumExistence` | — | Historical RG/loopy/tightness package; |
| `o4Restoration` | — | Legacy weak O4 slot; |
| `uniformInCoupling` | — | Weak existential schedule slot; |

</details>

## ContinuumYMExistence

**(a) Lean type** — `YMGap.Continuum.FourDExistence.ContinuumYMExistence`  
module `lean/YMGap/Continuum/FourDExistence.lean`

```lean
structure ContinuumYMExistence {M : Nat → Type} (μ_inf : ContinuumMeasure M) : Type 2
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `ym_mass_gap_of_existence` | `lean/YMGap/Continuum/FourDExistence.lean` | live exact: Quot.sound, propext |

**(c) Fields that remain OPEN:**

- (no field flagged OPEN by doc-marker; see the full field ledger below)

<details><summary>full field ledger (status by doc-marker)</summary>

| field | status | doc |
|---|---|---|
| `os_axioms` | — | The bundled OS axioms OS0–OS4 (content-bearing, from `OSAxioms.lean`). |
| `os1_o4_restoration` | — | **OS1, continuum:** full `O(4) ⋉ ℝ⁴` Euclidean invariance (rotation restoration beyond the lattice `H₄`). |
| `gauge_content` | — | **Gauge:** Schwinger functions generated by gauge-invariant curvature invariants. |
| `uv_asymptotic_freedom` | — | **UV:** short-distance asymptotic freedom. |
| `nontrivial` | — | **Nontriviality:** the measure is interacting, not Gaussian. |

</details>

## Semantic-root exclusion audit

Every `YMGap/*.lean` not reachable (transitively) from the selective
`YMGap.lean` semantic/audit root.  The `YMGap.*` Lake glob still compiles
each of these modules independently; `scripts/lean_import_guard.py`
requires every exclusion component to have a reviewed manifest root.

Reachable modules parsed from import closure; **6 of 2537** `YMGap/*.lean` files are unreachable from `YMGap.lean`.

- `lean/YMGap/Continuum/HarmonicLowerSixTailBaseSemanticFactors.lean`
- `lean/YMGap/Continuum/HarmonicLowerSixTailEnvelopeCertificateE8ChartA.lean`
- `lean/YMGap/Continuum/HarmonicLowerSixTailEnvelopeCertificateE8ChartAXPascal.lean`
- `lean/YMGap/Continuum/ScratchGraphFour.lean`
- `lean/YMGap/ModuliAlgebra.lean`
- `lean/YMGap/PolyAtlas.lean`

## Noncomputable ledger

Every `noncomputable def/abbrev/instance` in `YMGap/`. These do not compile
to executable code (they rest on `Q'`/data that Lean cannot evaluate) but
remain type-checked and axiom-gated.

**21** noncomputable declaration(s).

| module | line | decl |
|---|---|---|
| `lean/YMGap/Continuum/BirkhoffContraction.lean` | 179 | `fullFloor_of_birkhoffTransfer` |
| `lean/YMGap/Continuum/ChannelFeedbackRecursion.lean` | 295 | `looseFloorData` |
| `lean/YMGap/Continuum/ChannelFeedbackRecursion.lean` | 344 | `looseFloorEps` |
| `lean/YMGap/Continuum/ChannelFeedbackRecursion.lean` | 394 | `defectRecursion_of_looseBound` |
| `lean/YMGap/Continuum/DominantModeRecursion.lean` | 210 | `floorData` |
| `lean/YMGap/Continuum/DominantModeRecursion.lean` | 218 | `floorEps` |
| `lean/YMGap/Continuum/DominantModeRecursion.lean` | 247 | `dominantModeRecursion` |
| `lean/YMGap/Continuum/FrontierStatementBugFence.lean` | 115 | `legacyTrueMargin_surrogate_unconditional` |
| `lean/YMGap/Continuum/NormExcitedDrift.lean` | 472 | `prodFloorVal` |
| `lean/YMGap/Continuum/NormExcitedDrift.lean` | 502 | `dominantRGCoeffStep` |
| `lean/YMGap/Continuum/QuadraticKernel.lean` | 290 | `sq` |
| `lean/YMGap/Continuum/QuadraticKernel.lean` | 325 | `toCReal` |
| `lean/YMGap/Continuum/RouteGProductFloorAssembly.lean` | 218 | `twoRegimeProductFloor` |
| `lean/YMGap/Continuum/RouteGProductFloorAssembly.lean` | 261 | `twoRegimeDefectGapRecursion` |
| `lean/YMGap/Continuum/SingleStepDefectReduction.lean` | 307 | `defectRecursion_of_singleStep` |
| `lean/YMGap/Continuum/SingleStepDefectReduction.lean` | 347 | `trueMarginRecursion_of_singleStep` |
| `lean/YMGap/Continuum/TempleSpectralStabilityDefect.lean` | 224 | `templeResidual_model` |
| `lean/YMGap/Continuum/UniformCouplingFromAF.lean` | 148 | `afFloorData` |
| `lean/YMGap/Continuum/UniformCouplingFromAF.lean` | 152 | `afFloorEps` |
| `lean/YMGap/Continuum/UniformCouplingFromAF.lean` | 175 | `afDefectGapRecursion` |
| `lean/YMGap/Continuum/UniformCouplingFromAF.lean` | 212 | `dominantModeRecursion_of_AFCertificate` |

