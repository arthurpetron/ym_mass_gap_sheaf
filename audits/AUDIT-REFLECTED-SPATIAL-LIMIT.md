# Actual reflected spatial limits and positive variance

Date: 2026-09-16. Baseline: `4d34aa6`.

The whole-project goal remains a constructive nontrivial continuum
Yang--Mills theory on R^4 with the required QFT axioms and positive physical
Hamiltonian gap for every compact simple group. This checkpoint does not
close that goal. It constructs spatial limiting scalars for the original
SU(2) reflected signed plaquette-character presentations, at fixed nome
under explicit small-nome guards, and preserves a positive local variance.

## Proved causal chain

All paths below are relative to the repository root. Declaration names
are qualified by the namespace matching their module name.

| Producer | Source | Actual consumer/result |
| --- | --- | --- |
| `aligned_chartInsertion_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTranslatedProbe.lean:219` | Exact prefix-polynomial transport of the literal reflected insertion between aligned original charts. |
| `pairCap`, `chartProbe_interval` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:69`, `:219` | Computed actual interval for the signed product, including all cross terms and repetitions. |
| `chartProbe_local`, `chartCarrier` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:337`, `:255` | Literal link locality and a fixed translated box carrier, not a locality claim inferred from polynomial equivalence. |
| `active_core_size_floor` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoxBoundary.lean:81` | Omitted-face separation forces an active core of size at least `r+1-M` (natural subtraction). |
| `determinant_bound`, `finiteValue_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoxBoundary.lean:96`, `:120` | Signed mixed numerator retains both original partitions; normalization cancels them before any limit. |
| `chartScalar_spatial_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialComparison.lean:56` | Actual cross-width chart scalars differ by at most `A*rho^(r+1-M)`. All interval/locality inputs are supplied. |
| `rectangle`, `diagonalCauchy` | `lean/YMGap/Continuum/SpatialPivotCauchy.lean:88`, `:117` | One computed spatial pivot and its fixed-row modulus give explicit three-index diagonal Cauchy data. |
| `spatialCauchy`, `spatialLimit` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialLimit.lean:69`, `:78` | Actual original chart data supply every premise of the generic pivot theorem. |
| `jointPairing_spatial_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialLimit.lean:88` | Removing cutoff/time first, then growing the recentered box, yields the same constructed scalar. |
| `spatialLimit_chart_independent` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialLimit.lean:104` | Different valid observation charts change the modulus, not the scalar up to `CReal.Equiv`. |
| `recentered_variance_floor` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialVariance.lean:51` | First and second raw moments share the same original action, partition, stage, buffer and chart. |
| `spatialVariance_floor`, `spatialVariance_ne_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialVariance.lean:93`, `:101` | The actual limiting variance is at least `starRatio(w)>0`, hence not equivalent to zero. |

## Constants and parameter dependence

Fix `base>0`, physical presentations `x,y : PhysicalSpan base`, and
`H >= radius(x), radius(y)`. Let `C(r,k,t)` be `recenteredScalar` at margin
`r`, heat stage `k`, and boundary-time buffer `t`. The width is
`W_r=base+2*r+2`. The proved inequality is

```text
|C(r+d,k,t) - C(r,k,t)| <= A * rho^(r+1-M)
N   = max(base, 2*H+1)
M   = 6*N^4
rho = entropyRate 625 (adjustedCoreRate w hd)
A   = (pairCap(x,y)+pairCap(x,y)) * boxAmplitude(w,hd,hs,N)
```

Definitions: `boxSize` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:244`,
`carrierSize` and `boxAmplitude` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoxBoundary.lean:53` and `:56`,
`spatialAmplitude` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialComparison.lean:35`.
The exponent uses truncated natural subtraction, not integer subtraction.
The box amplitude is explicitly
`probePrefactor(w,hd,24*N^4) * (2^M * 625^M) / (1-rho)`.

`pairCap` depends only on the original coefficients and representation
labels: `spanCap_translate`, `spanCap_encode`, `spanCap_mirror` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:108`,
`:116`, `:124`. The larger `A` also depends on `base,H,w`. It is independent
of `r,d,k,t`; `rho` depends on `w`. No uniformity in nome, physical spacing,
all base supports, or increasing temporal separation is claimed.

The hypotheses of `chartScalar_spatial_bound` explicitly retain `0<w<1`,
`heatRatio w <= 1/2`, `heatRemainderBound w < 1`, and `rho<1`.
No new analytic hypothesis is introduced to obtain the spatial limit.
The earlier small-nome pilot is unchanged; this increment does not extend
the applicable nome range.

## The pivot contraction, without a uniform temporal mixing rate

For positive tolerance `epsilon`, compute

```text
p = M + geometricCutoff(rho,A,epsilon/4)
D = max(p, rowModulus(p,epsilon/4))
```

These are Type-level functions `pivot`, `diagonalModulus` at
`lean/YMGap/Continuum/SpatialPivotCauchy.lean:39` and `:43`.
For sufficiently late independent indices the comparison is

```text
C(r,k,t) --spatial error--> C(p,k,t)
         --one row's modulus--> C(p,j,u)
         --spatial error--> C(s,j,u).
```

Each error is at most `epsilon/4`. The same explicit `D` works for
`C(n,n,n)` and supplies `spatialCauchy`; no monotonicity of the supplied
row moduli and no width-uniform row modulus are assumed. The actual row
modulus and its rectangle theorem are `rowModulus`, `row_rectangle` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialLimit.lean:47` and `:52`.

`rowLimits_converge` at `lean/YMGap/Continuum/SpatialPivotCauchy.lean:159`
handles the actual `QMhat` representatives; it does not equate different
row reindexings. In the concrete consumer the row Cauchy data have the
existing chart modulus, and `jointPairing_chart` identifies their limits.
Chart independence follows by uniqueness of the limit of the SAME
chart-independent recentered `jointPairing` sequence. It is neither
finite-chart stationarity nor compatibility between different base widths.

## Nontriviality survives this spatial passage

`spatialVariance` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialVariance.lean:63`
is exactly the spatial second moment minus the square of the spatial first
moment of a fundamental face character. `recenter_unit` at `:40` and the
existing face recentering identity pin the finite variance floor to these
same raw chart scalars. `spatialVariance_converges` at `:70` uses genuine
multiplication continuity; it does not assume canonical approximation
indices coincide. Order passage retains `starRatio(w)>0` at `:93`.

This is a nonzero scalar variance. This checkpoint does not construct a
nonzero vector in a spatially completed carrier or a continuum excitation.

## Next consumers and explicit open boundaries

The following is a source-reviewed next-proof plan, not a claimed closure.

- Export the spatial-limit form's symmetry, positivity, Cauchy--Schwarz,
  linearity and unit normalization. Fixed-width source laws are
  `jointPairing_symm`, `jointPairing_nonnegative`, `jointPairing_cauchySchwarz`
  at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPairingLaws.lean:44`,
  `:52`, `:67`, with linear laws starting at `:113`. Recentered list-map
  identities and actual convergence are the needed connecting proofs.
- Derive null descent from the LIMIT form's Cauchy--Schwarz. Limit-nullity
  does not imply finite-width nullity. The reusable parametric consumer is
  `SquaredSeminorm` at
  `lean/YMGap/Continuum/CRealSeminormCompletion.lean:39`, not an identification
  with an old width-dependent completed carrier. Existing physical-time
  source laws start at `jointPairing_time_sum` in
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPhysicalTime.lean:46`;
  `recenter_time` is at
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialRecenter.lean:99`.
- Prove base-inclusion coherence for unchanged face words before claiming
  one presentation-independent union carrier. The present spatial comparison
  fixes `base`; chart independence does not discharge this obligation.
  Nor is the present signed plaquette-character algebra identified with a
  full Wilson/cylinder algebra or all spatial translations.
- Prove the needed same-partition connected temporal decay with a strict
  rate independent of width. Current `mixRate` at
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferMixingRate.lean:110`
  explicitly retains width dependence through its floor/cap fraction.
  The new spatial boundary bound is not such a temporal estimate: its
  support-box constant grows with the chart covering separated probes.
  The existing prefactor-removal argument is illustrated by
  `evenMoment_first_le` at
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean:97`;
  its spatial-limit analogue has not been supplied.
- Full Hilbert/OS/QFT reconstruction, physical time/spacing calibration,
  controlled continuum passage and continuum nontriviality, and every
  compact simple group remain open. No dimensionless rate is relabelled a
  physical Hamiltonian gap.

## Verification boundary

Seven focused serialized checks completed successfully via the monitored
launcher, one worker and a 20 GiB worker ceiling. All 59 printed public
axiom gates were within `{propext, Quot.sound}`. No `sorry`, new axiom,
classical shortcut, native certificate trust, weakened frontier field or
changed safety limit was introduced. Independent read-only mathematical
review checked original actions/partitions, literal support/placement,
pivot quantifiers, actual limit representatives and positive variance.

Final local log evidence (SHA-256 hashes are of logs, not source files):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-chart-box-boundary-20260916.log` | 6 | `c56112b86afe3cc837a1c6877e81671c9c58161dace2174a9f5f9a5b8079ee79` |
| `ym-chart-translated-probe-20260916.log` | 7 | `600e858801c16b396e10ac0b15b351893fda3e4053713322d54b5fc695b6735d` |
| `ym-chart-probe-control-20260916.log` | 15 | `5a953f3d1d6536fe52f16ada62f9d8a06dec981c143d18992b8c93b4ce787b52` |
| `ym-chart-spatial-comparison-20260916.log` | 4 | `e3cbd15bceb6398604183d380384f97c1a8f0c1fb39e9a8f17f774c5416d1571` |
| `ym-spatial-pivot-20260916.log` | 13 | `e52a7cfb64f7c6034d60d1b0a1c04aea737d5f5d2d76a62e362fa473b4cbe029` |
| `ym-chart-spatial-limit-20260916.log` | 8 | `5a813d1fc4111a31486746126b6b33d4738846bc8435317ce22af220dd9c425f` |
| `ym-chart-spatial-variance-20260916.log` | 6 | `293401b8c2682a2f87db9af8ff03467aee84b23f1edfc009526850475850db7c` |

Seven imports were added to the selective root. No root build, full-tree
build or full audit ran; this report does not imply one. No routine
literature scan ran. The timestamped cached math-ph report and repository
12-hour minimum scan interval remain in force.
