# Exact source Young identity on the original plaquette energy

2026-09-24 UTC. Follows `40a6a89`. The constructive continuum Yang--Mills
and Clay target remain OPEN.

## Checked mathematical increment

For the actual symmetric product heat kernel K and arbitrary supported source
a and observable f, define on its two original slices

    J = Hxy[K a(x)^2 (f(x)-f(y))^2],
    D = Hxy[K (a(x)-a(y))^2 (f(x)-f(y))^2].

The original source energy satisfies the exact identity

    4 E + D = 2 J.

For 0<w<1 and the explicit guard headCutoff(w)<=K, the existing product-heat
certificate gives D>=0, hence 2E<=J. Source positivity is NOT an additional
premise. The identity itself needs only valid indices and support, not the
positivity cutoff. Repeated heat indices are permitted there.

For distinct valid indices, the actual heat marginal and pairing give

    J = H[a^2 f^2] + H[a^2 P(f^2)] - 2 H[a^2 f P(f)]
      = H[a^2 (f^2 + P(f^2) - 2 f P(f))].

P is the existing productMap, not an assumed spectral operator.

The ORIGINAL action consumes both identities with q=P_fringe(V*g).
`projected_young_moment_identity` expresses 4E_original+D directly through
the actual P(f) and P(f^2), retaining the complete projected source. Strict
spatial padding constructs the fringe-independence premise for the literal
plaquette and original terminal message. The original action, energy and
common partition have not been replaced. No source derivative occurs in J.

## Declaration map

All paths below are under `lean/YMGap/Continuum/`.

| Module:line | Declaration | Result |
| --- | --- | --- |
| `SU2QuaternionProductHeatSourceYoung.lean:80` | `singleEndedCost` | Actual J. |
| `SU2QuaternionProductHeatSourceYoung.lean:87` | `sourceIncrementCost` | Actual D. |
| `SU2QuaternionProductHeatSourceYoung.lean:106` | `singleEnded_swap` | Endpoint symmetry of J. |
| `SU2QuaternionProductHeatSourceYoung.lean:203` | `four_mul_sourceEnergy_add_increment_eq_two_singleEnded` | 4E+D=2J. |
| `SU2QuaternionProductHeatSourceYoung.lean:228` | `two_mul_sourceEnergy_le_singleEndedCost` | 2E<=J under the positivity cutoff. |
| `SU2QuaternionProductHeatSourceYoungMoments.lean:82` | `singleEndedCost_eq_moments` | Exact three-moment expansion. |
| `SU2QuaternionProductHeatSourceYoungMoments.lean:149` | `singleEndedCost_eq_weightedPolynomial` | Collected actual product-map expression. |
| `BF4ExactSlabFixedSpatialSourceYoung.lean:60` | `projected_young_identity` | Original-source signed identity. |
| `BF4ExactSlabFixedSpatialSourceYoung.lean:79` | `projected_young_moment_identity` | Original-source identity with actual heat images. |
| `BF4ExactSlabFixedSpatialSourceYoung.lean:99` | `projected_energy_le_singleEndedCost` | Original projected-energy upper bound. |
| `BF4ExactSlabFixedSpatialSourceYoung.lean:117` | `padded_plaquette_energy_le_singleEndedCost` | Literal original terminal-message consumer. |
| `SU2HeatFundamentalIncrementBudget.lean:29` | `one_sub_qpow_thirtyTwo_le` | 1-w^32<=32(1-w). |
| `SU2HeatFundamentalIncrementBudget.lean:119` | `fundamental_curvature_bounds` | 0<=5-8w^12+3w^32<=960(1-w)^2. |

The last two statements are separate scalar estimates on 0<=w<=1. They
do NOT prove the required four-link spin-two heat image. A canonical
substitution draft is separate, unverified work at this checkpoint; the
literal four-link producer remains OPEN.

## Analytic boundary and next decision

The sourceMoment definition in
`SU2QuaternionProductHeatProjectedSourceEnergy.lean:49` weights insertions
by q*P(q), not q^2. Thus the zeroth-order costs above are not already the
SAME interacting centered variance. Dropping D removes the two-endpoint
source correction; this is not a uniform scaling estimate or a claim that
the numerical bound improves every earlier bound.

The next analytic requirement is useful control of the COMPLETE signed
combination against SAME centered variance for ONE justified changing-scale
observable family, or its direct sampled response. A source-specific
comparison of the raw square with the interacting law is another possible
input, not a theorem supplied here. Do not add further wrappers assuming it.
The actual four-link heat-image calculation can simplify J but cannot alone
supply that comparison or survival. Preserve D for cancellation analysis.

EVERY-vector spatial/spacing gap control, SAME continuum limits, full
Hilbert/OS/QFT and local YM/short-distance identification, physical-time
Hamiltonian and finite positive mass, and EVERY compact simple group all
remain OPEN. No canonical field, analytic premise or axiom was added or
weakened; no source sorry was added or discharged.

## Verification

Four final narrow checks passed eleven printed gates, all within
{propext, Quot.sound}. Each ran through the monitored launcher with one worker.

| Target | Accepted log under `/tmp/` | Worker ceiling | Gates |
| --- | --- | --- | --- |
| `SU2QuaternionProductHeatSourceYoung` | `ym-gap-source-young-check-5.log` | 2 GiB | 3 |
| `SU2QuaternionProductHeatSourceYoungMoments` | `ym-gap-source-young-moments-check-5.log` | 2 GiB | 2 |
| `BF4ExactSlabFixedSpatialSourceYoung` | `ym-gap-original-source-young-check-5.log` | 2 GiB | 4 |
| `SU2HeatFundamentalIncrementBudget` | `ym-gap-fundamental-increment-budget-check-3.log` | 1 GiB | 2 |

Accepted logs contain no error, warning, sorryAx or Classical.choice. One
earlier check stopped at the unchanged 12 GiB system reserve. Verification
resumed only after recovery, with reduced worker ceilings; a 1 GiB trial
was insufficient for the larger import environment. A rejected original
consumer used the classical core `List.nodup_range`; it was replaced by
the existing constructive `CayleyParentInj.range_nodup` and rechecked.
Failed checks are not evidence. No full-root build, audit, guard or progress
metric was run. Semantic imports were updated, not fully rebuilt.
