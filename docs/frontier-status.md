# Frontier status

> **Auto-generated** by `scripts/frontier_status.py` on 2026-07-31.
> Axiom-gate source: `lean/AXIOM_AUDIT.md` hashed baseline (21665 tracked declarations, 2741 namespaces, 0 reviewed exceptions).
> Guard configuration: **5 protected frontier types**, **0 reviewed allowlist entries**.
> Read-only report — no Lean source is edited. `GUARDED OPEN` is determined
> from `YMGapGuard.lean`; field counts are only documentation-marker counts.

The Clay Yang–Mills mass-gap problem remains **OPEN**. This document is a
status ledger, not a claim of closure. Run `make lean-frontier-guard` for
the authoritative environment-level inhabitance check.

## Summary

| Frontier bundle | Lean type | theorem state | # partial closes | # doc-marked OPEN fields |
|---|---|---|---|---|
| Tier0Scorecard atoms | `Tier0Scorecard` | **GUARDED OPEN** | 6 | 6 |
| ReconstructionScorecardFinal tokens | `ReconstructionOpenFrontier` | **DECLARED OPEN** | 2 | 10 |
| UniformSpacingFloor | `UniformSpacingFloor` | **GUARDED OPEN** | 5 | 0 |
| SpectralMarginInput fields | `SpectralMarginInput` | interface/input (not guard-verified) | 3 | 0 |
| SixJPentagon | `SixJPentagon` | **DECLARED OPEN** | 3 | 1 |
| ClayTargetPinned | `ClayTargetPinned` | **GUARDED OPEN** | 4 | 3 |
| ClayTarget | `ClayTarget` | **GUARDED OPEN** | 1 | 2 |
| FrontierDAG | `FrontierDAG` | **GUARDED OPEN** | 4 | 3 |
| ContinuumYMExistence | `ContinuumYMExistence` | interface/input (not guard-verified) | 1 | 0 |

## Tier0Scorecard atoms

**(a) Lean type** — `YMGap.Continuum.Tier0Scorecard.Tier0Scorecard`

module `lean/YMGap/Continuum/Tier0Scorecard.lean`
theorem state: **GUARDED OPEN**

```lean
structure Tier0Scorecard (p : z4Chain.toLattice.Plaquette) (w : Q') (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type 1
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `fixedSpacing_met` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |
| `subA_offCorr_decompose` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |
| `subA_tree_graph` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |
| `subB_prodFloor_pos` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |
| `subB_physGap_pos` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |
| `toFrontierC` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- `subA` — OPEN ×4 — Sub-wall A ((T′), (D1), (D2), pentagon).
- `subB` — OPEN ×3 — Sub-wall B (`hlocalize`, `hbridge`, `hadd`) in one input.
- `tTree` — **(T′)** — the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree inequality, over the (D2) lattice `d2Sep.val` (the coupled atom).
- `d1Mayer` — **(D1)** — the absolute Mayer–Ursell connecting-cluster expansion over the CLOSED 4D count `z4ClusterCountBound p`.
- `a2Racah` — **(A2, Level-1 coarse)** — the doubly-stochastic Racah 6j² kernel, a permutation-satisfiable surrogate (`RacahInhabit.racahRP`), carried ...
- `a2Pentagon` — **(A2, Level-2 genuine)** — the fractional-6j associator numeric core `PentagonRelation.PentagonNumericCore`, pinned to `1/4` at the smal...

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `fixedSpacing` | PROVED | PROVED — the fixed-spacing rubric line (`ClayFixedSpacingMet`). |
| `subA` | OPEN | OPEN ×4 — Sub-wall A ((T′), (D1), (D2), pentagon). |
| `subB` | OPEN | OPEN ×3 — Sub-wall B (`hlocalize`, `hbridge`, `hadd`) in one input. |
| `d2Sep` | — | **(D2)** — the plaquette-graph `SepLattice` metric refining `z4Chain` (inhabited DATA, carried only to type `tTree`). |
| `tTree` | OPEN | **(T′)** — the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree inequality, over the (D2) lattice `d2Sep.val` (the coupled atom). |
| `d1Mayer` | OPEN | **(D1)** — the absolute Mayer–Ursell connecting-cluster expansion over the CLOSED 4D count `z4ClusterCountBound p`. |
| `a2Racah` | OPEN | **(A2, Level-1 coarse)** — the doubly-stochastic Racah 6j² kernel, a permutation-satisfiable surrogate (`RacahInhabit.racahRP`), carried ... |
| `a2Pentagon` | OPEN | **(A2, Level-2 genuine)** — the fractional-6j associator numeric core `PentagonRelation.PentagonNumericCore`, pinned to `1/4` at the smal... |

</details>

## ReconstructionScorecardFinal tokens

**(a) Lean type** — `YMGap.Rubric.ReconstructionScorecardFinal.ReconstructionOpenFrontier`

module `lean/YMGap/Rubric/ReconstructionScorecardFinal.lean`
theorem state: **DECLARED OPEN**

```lean
structure ReconstructionOpenFrontier (D : SmulGNSData) (op : TransferOperator D.toGNSData.gnsComplete) (L : AdditiveTransferOperator D.toGNSData) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w) (N : Nat) : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `reconstruction_status` | `lean/YMGap/Rubric/ReconstructionScorecardFinal.lean` | within gate {propext, Quot.sound} |
| `all_fixed_spacing_reconstruction_proved` | `lean/YMGap/Rubric/ReconstructionScorecardFinal.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- `node1` — OPEN node ①.
- `trueMargin` — OPEN: the genuine dimensionless physical margin.
- `physicalWilsonBridge` — OPEN: the physical Wilson double-Haar bridge.
- `boundedH` — OPEN: the bounded functional-calculus Hamiltonian `H = −log T`.
- `continuumMinlos` — OPEN: the cited-classical continuum Minlos measure.
- `OpenNode1FiniteSMargin` = `AcNReserveAnalytic.FiniteSMargin w`
- `OpenTrueMargin` = `ReconstructionScorecard.OpenTrueMargin`
- `OpenPhysicalWilsonBridge` = `WilsonSpectralBridge.CharacterDiagResolution op RCScaleClose.rcScaleResidualPlus w N`
- `OpenBoundedHamiltonian` = `BoundedFunctionalCalculusResidual (excG op w hw0 hw1 N) L`
- `OpenContinuumMinlos` = `ReconstructionScorecard.OpenContinuumMeasure`

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `status` | PROVED | the PROVED-UNCONDITIONAL status. |
| `node1` | OPEN | OPEN node ①. |
| `trueMargin` | OPEN | OPEN: the genuine dimensionless physical margin. |
| `physicalWilsonBridge` | OPEN | OPEN: the physical Wilson double-Haar bridge. |
| `boundedH` | OPEN | OPEN: the bounded functional-calculus Hamiltonian `H = −log T`. |
| `continuumMinlos` | OPEN | OPEN: the cited-classical continuum Minlos measure. |

</details>

## UniformSpacingFloor

**(a) Lean type** — `YMGap.Continuum.UnifiedContinuumFloor.UniformSpacingFloor`

module `lean/YMGap/Continuum/UnifiedContinuumFloor.lean`
theorem state: **GUARDED OPEN**

```lean
structure UniformSpacingFloor {ι : Type} {α : Type} (le : Q' → α → Prop) (g : ι → α) : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `ofUniformPhysGapFloor` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | within gate {propext, Quot.sound} |
| `ofModeEnergyFloor` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | within gate {propext, Quot.sound} |
| `ofContinuumGapPersistence` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | within gate {propext, Quot.sound} |
| `ofUniformRatioVariation` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | within gate {propext, Quot.sound} |
| `ofDimensionalTransmutation` | `lean/YMGap/Continuum/UnifiedContinuumFloor.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- (none; absence of an `OPEN` marker does **not** prove that the
  structure is inhabited or that its physical hypotheses are discharged)

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `floor` | — | The uniform positive floor. |
| `floor_pos` | — | The floor is strictly positive. |
| `bound` | — | The floor lies below the per-scale gap quantity at every scale at once. |

</details>

## SpectralMarginInput fields

**(a) Lean type** — `YMGap.Continuum.AsymptoticSpectralLoc.SpectralMarginInput`

module `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean`
theorem state: interface/input (not guard-verified)

```lean
structure SpectralMarginInput (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `toAsymptotic` | `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean` | within gate {propext, Quot.sound} |
| `uniform_floor` | `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean` | within gate {propext, Quot.sound} |
| `continuum_floor_pos` | `lean/YMGap/Continuum/AsymptoticSpectralLoc.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- (none; absence of an `OPEN` marker does **not** prove that the
  structure is inhabited or that its physical hypotheses are discharged)

<details><summary>full field ledger (documentation markers only)</summary>

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
theorem state: **DECLARED OPEN**

```lean
structure SixJPentagon : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `a2_racah` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |
| `a2_tetra_nonneg` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |
| `pentagon_to_racah` | `lean/YMGap/Continuum/Tier0Scorecard.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- `pentagon` — **The Biedenharn–Elliott pentagon** — a guarded CUBIC closure of `P` (nonlinear in the kernel).

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `P` | — | The rational dim-absorbed 6j-square kernel underlying the pentagon. |
| `pentagon` | OPEN | **The Biedenharn–Elliott pentagon** — a guarded CUBIC closure of `P` (nonlinear in the kernel). |

</details>

## ClayTargetPinned

**(a) Lean type** — `YMGap.Rubric.ClayTargetPinned.ClayTargetPinned`

module `lean/YMGap/Rubric/ClayTargetPinned.lean`
theorem state: **GUARDED OPEN**

```lean
structure ClayTargetPinned {M : Nat → Type} (μ_inf : ContinuumMeasure M) : Type 2
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `toClayTarget` | `lean/YMGap/Rubric/ClayTargetPinned.lean` | within gate {propext, Quot.sound} |
| `pinned_fixedSpacing_proved` | `lean/YMGap/Rubric/ClayTargetPinned.lean` | within gate {propext, Quot.sound} |
| `toClayTarget_fixedSpacing` | `lean/YMGap/Rubric/ClayTargetPinned.lean` | within gate {propext, Quot.sound} |
| `toClayTarget_o4_eq` | `lean/YMGap/Rubric/ClayTargetPinned.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- `continuumExistence` — OPEN: continuum measure existence + tightness.
- `limitData` — OPEN: the Λ→∞ / a→0 limits + reflection positivity, together with the legacy weak O4 slot, carried on the shared masses as genuine `Conti...
- `uniformInCoupling` — OPEN: the gap uniform across coupling / the continuum.

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `bundle` | — | ONE OS-axiom bundle over `μ_∞`: fixes the observable algebra `A`, the probability functional `E`, and the OS4 spectral model `S`. |
| `recon` | — | ONE OS reconstruction over the SAME `μ_∞`: fixes `H_∞`, the Hamiltonian, the finite spectral model and the located gap. |
| `wilson` | — | The extra module structure (add/neg/smul + the GNS form `E(star a · b)`) living over the bundle's OWN observable algebra `bundle.A`. |
| `gnsData` | — | The GNS datum for the completed Hilbert space. |
| `gns` | — | ONE completed GNS Hilbert space over that datum. |
| `fixedSpacing` | PROVED | PROVED: transported verbatim from `clay_fixed_spacing_met`. |
| `ePinned` | PROVED | **PIN (the genuinely NEW interface):** the GNS form's expectation IS the OS bundle's probability functional `E`. |
| `specPinned` | — | **PIN:** the reconstruction's OS4 spectral model IS the bundle's OS4 model, so the gap is read off the SAME finite spectral data that fee... |
| `gnsPinned` | — | **PIN:** the GNS datum IS the one forged from the bundle's algebra. |
| `massGap` | — | `Δ` = the mass gap, carried WITH a positivity witness (Type-level `Σ'`, NOT a bare `∃`). |
| `massGapPinned` | — | **PIN:** that `Δ` is the gap of THIS reconstruction (its margin `1 − sep`), not a free positive real. |
| `hasGap` | PROVED | The genuine spectral gap of the shared reconstruction. |
| `continuumExistence` | OPEN | OPEN: continuum measure existence + tightness. |
| `limitData` | OPEN | OPEN: the Λ→∞ / a→0 limits + reflection positivity, together with the legacy weak O4 slot, carried on the shared masses as genuine `Conti... |
| `massPinned` | — | **PIN:** the continuum-limit mass IS the same `Δ` as the mass-gap clause. |
| `uniformInCoupling` | OPEN | OPEN: the gap uniform across coupling / the continuum. |

</details>

## ClayTarget

**(a) Lean type** — `YMGap.Rubric.ClayScorecard.ClayTarget`

module `lean/YMGap/Rubric/ClayScorecard.lean`
theorem state: **GUARDED OPEN**

```lean
structure ClayTarget : Type
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `clay_fixed_spacing_met` | `lean/YMGap/Rubric/ClayScorecard.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- `continuumExistence` — OPEN: the continuum (`a → 0`) measure existence + tightness.
- `uniformInCoupling` — OPEN: the gap uniform across coupling / the continuum.

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `fixedSpacing` | PROVED | The fixed-spacing clauses — PROVED (`clay_fixed_spacing_met`). |
| `continuumExistence` | OPEN | OPEN: the continuum (`a → 0`) measure existence + tightness. |
| `o4Restoration` | — | Legacy weak O4 slot; |
| `uniformInCoupling` | OPEN | OPEN: the gap uniform across coupling / the continuum. |

</details>

## FrontierDAG

**(a) Lean type** — `YMGap.Rubric.FrontierDAG.FrontierDAG`

module `lean/YMGap/Rubric/FrontierDAG.lean`
theorem state: **GUARDED OPEN**

```lean
structure FrontierDAG (p : z4Chain.toLattice.Plaquette) (w : Q') {D : GNSData} (G : SpectralGapData D.gnsComplete) (L : AdditiveTransferOperator D) (N pΓ : Nat) : Type 1
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `toSubWallA` | `lean/YMGap/Rubric/FrontierDAG.lean` | within gate {propext, Quot.sound} |
| `trueMarginAtom` | `lean/YMGap/Rubric/FrontierDAG.lean` | within gate {propext, Quot.sound} |
| `o4Atom` | `lean/YMGap/Rubric/FrontierDAG.lean` | within gate {propext, Quot.sound} |
| `boundedHAtom` | `lean/YMGap/Rubric/FrontierDAG.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- `bulkCtrl` — The bond-moved spectral-localization certificate (open `bulk_shift`).
- `a2Pentagon` — (A2, Level-2) the genuine fractional-6j associator numeric core `PentagonRelation.PentagonNumericCore` (physical associator OPEN).
- `edgeShift` — The pinned edge-shift residual (`hId`/`hLin`;

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `bulkCtrl` | OPEN | The bond-moved spectral-localization certificate (open `bulk_shift`). |
| `d2Sep` | — | (D2) the plaquette-graph `SepLattice` metric refining `z4Chain` — inhabited DATA, carried only to type `tTree`. |
| `tTree` | — | (T′) the per-cluster Penrose / Poghosyan–Ueltschi spanning-tree inequality over the (D2) lattice `d2Sep.val`. |
| `d1Mayer` | PROVED | (D1) the absolute Mayer–Ursell connecting-cluster expansion over the CLOSED 4D count `z4ClusterCountBound p`. |
| `a2Racah` | PROVED | (A2, Level-1) the coarse doubly-stochastic Racah 6j² surrogate, carried only to discharge the coarse `Tier0FrontierC` a2 slot; |
| `a2Pentagon` | OPEN | (A2, Level-2) the genuine fractional-6j associator numeric core `PentagonRelation.PentagonNumericCore` (physical associator OPEN). |
| `coreB` | — | (Core B) the finite-`s` central-autoconvolution theta-floor margin. |
| `edgeShift` | OPEN | The pinned edge-shift residual (`hId`/`hLin`; |
| `trueMargin` | PROVED | The genuine dimensionless physical margin recursion `Δ_k = m_lat(a_k)/a_k`. |
| `boundedH` | — | Residual B — the bounded self-adjoint additive Hamiltonian with `e^{−H}=T`. |
| `o4` | — | The physical `O(4)` isotropization running (`betaDrop`-sign / anisotropy). |

</details>

## ContinuumYMExistence

**(a) Lean type** — `YMGap.Continuum.FourDExistence.ContinuumYMExistence`

module `lean/YMGap/Continuum/FourDExistence.lean`
theorem state: interface/input (not guard-verified)

```lean
structure ContinuumYMExistence {M : Nat → Type} (μ_inf : ContinuumMeasure M) : Type 2
```

**(b) Best partial close(s)** — module + decl + (d) axiom gate:

| decl | module | axiom gate |
|---|---|---|
| `ym_mass_gap_of_existence` | `lean/YMGap/Continuum/FourDExistence.lean` | within gate {propext, Quot.sound} |

**(c) Fields explicitly marked OPEN in source documentation:**

- (none; absence of an `OPEN` marker does **not** prove that the
  structure is inhabited or that its physical hypotheses are discharged)

<details><summary>full field ledger (documentation markers only)</summary>

| field | status | doc |
|---|---|---|
| `os_axioms` | — | The bundled OS axioms OS0–OS4 (content-bearing, from `OSAxioms.lean`). |
| `os1_o4_restoration` | — | **OS1, continuum:** full `O(4) ⋉ ℝ⁴` Euclidean invariance (rotation restoration beyond the lattice `H₄`). |
| `gauge_content` | — | **Gauge:** Schwinger functions generated by gauge-invariant curvature invariants. |
| `uv_asymptotic_freedom` | — | **UV:** short-distance asymptotic freedom. |
| `nontrivial` | — | **Nontriviality:** the measure is interacting, not Gaussian. |

</details>

## Unimported-file audit

Every `YMGap/*.lean` NOT reachable (transitively) from `YMGap.lean` — i.e.
silently skipped by the default `lake build` and therefore un-audited.

Reachable modules parsed from import closure; **70 of 2793** `YMGap/*.lean` files are unreachable from `YMGap.lean`.

- `lean/YMGap/Continuum/BF4CalibratedCubeSpectralFence.lean`
- `lean/YMGap/Continuum/BF4CentralLowerCubePositiveRow.lean`
- `lean/YMGap/Continuum/BF4CentralLowerCubeRowDomination.lean`
- `lean/YMGap/Continuum/BF4DyadicCubeVacuumCalibration.lean`
- `lean/YMGap/Continuum/BF4MatchedProfileFactorialCollapsedQuarter.lean`
- `lean/YMGap/Continuum/CompactDualCutoffOneLocalFaceGramCertificate.lean`
- `lean/YMGap/Continuum/CompactDualCutoffOnePhysicalRemainderRGI9.lean`
- `lean/YMGap/Continuum/CompactDualPhysicalRemainderLocality.lean`
- `lean/YMGap/Continuum/CompactDualWholeSlabProjectiveBridge.lean`
- `lean/YMGap/Continuum/FiniteOccurrenceReverseRecovery.lean`
- `lean/YMGap/Continuum/HarmonicLowerSixCubicDebtCoefficient1330Certificate.lean`
- `lean/YMGap/Continuum/HarmonicLowerSixTailBaseSemanticFactors.lean`
- `lean/YMGap/Continuum/HarmonicLowerSixTailEnvelopeCertificateE8ChartA.lean`
- `lean/YMGap/Continuum/HarmonicLowerSixTailEnvelopeCertificateE8ChartAXPascal.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighCertificate.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock0Row0.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock0Row1.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock0Row2.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock0Row3.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock0Row4.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock1Row0.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock1Row1.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock1Row2.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock1Row3.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock1Row4.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock2Row0.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock2Row1.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock2Row2.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock2Row3.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock2Row4.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row0.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row1.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row2.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row3.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock3Row4.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock4Row0.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock4Row1.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock4Row2.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock4Row3.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock4Row4.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock5Row0.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock5Row1.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock5Row2.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock5Row3.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsBlock5Row4.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk0.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk1.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk2.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk3.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk4.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk5.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk6.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk7.lean`
- `lean/YMGap/Continuum/HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerHighRowsChunk8.lean`
- `lean/YMGap/Continuum/ScratchGraphFour.lean`
- `lean/YMGap/Continuum/Z4AdjacentCubeCancellationActivity.lean`
- `lean/YMGap/Continuum/Z4AdjacentCubeCancellationConditionalKernel.lean`
- `lean/YMGap/Continuum/Z4AdjacentCubeGeneralSourceConditionalKernel.lean`
- `lean/YMGap/Continuum/Z4AdjacentCubeJointConditionalKernel.lean`
- `lean/YMGap/Continuum/Z4AdjacentCubeSharedFaceRecouplingKernel.lean`
- `lean/YMGap/Continuum/Z4CubeStretchedSourceCoverageFence.lean`
- `lean/YMGap/Continuum/Z4FusionPairSingletInjection.lean`
- `lean/YMGap/Continuum/Z4HalfTimeReflectionAdjacentEvenReachableEndpointCompression.lean`
- `lean/YMGap/Continuum/Z4OutwardSevenCubeGoodBackgroundSwitching.lean`
- `lean/YMGap/ModuliAlgebra.lean`
- `lean/YMGap/PolyAtlas.lean`
- `lean/YMGap/RG/DominatedSummableDistortion.lean`
- `lean/YMGap/RG/GradedPerronFrobeniusContraction.lean`
- `lean/YMGap/RG/ScaleDependentGradedPerronFrobenius.lean`
- `lean/YMGap/RG/ScaleDependentGroupedContraction.lean`

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

