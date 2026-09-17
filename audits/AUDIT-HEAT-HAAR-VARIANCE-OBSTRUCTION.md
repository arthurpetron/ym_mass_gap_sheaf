# Original-face Haar variance is not small near nome one

Date: 2026-09-17 UTC. Base revision: `de3ad1d`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 for every
compact simple gauge group, with same-theory QFT and a positive physical
Hamiltonian gap, constructively within {propext, Quot.sound}. OPEN.

## The mathematical test

This tests an actual original physical plaquette, not a surrogate finite
state model. Let h_K be its full original heat prefix, and R_K=h_K-1.
The coefficient identity is already `faceHeat_eq_one_add`,
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeFaceRemainder.lean:95`.

The new module is
`lean/YMGap/Continuum/BF4ExactSlabHeatHaarVarianceObstruction.lean`:

| Declaration | Line | Result |
|---|---:|---|
| `remainder_mean_zero` | 65 | H[R_K]=0, every cutoff. |
| `prefix_mean_one` | 77 | H[h_K]=1, same original Haar functional. |
| `fundamental_remainder_pairing` | 99 | H[chi_1*R_K]=2*w^3, every K>=1. |
| `remainderVariance` | 124 | Defined as H[R_K^2], not a different law. |
| `remainderVariance_lower` | 134 | H[R_K^2]>=4*w^6, every K>=1. |
| `remainderVariance_gt_one` | 159 | H[R_K^2]>1 when w>=7/8 and K>=1. |
| `no_eventual_small_variance` | 170 | No cutoff threshold can make all subsequent variances <=1. |

The mean and pairing equalities reuse original character cancellation and
the character recurrence. `first_character_pair`,
`lean/YMGap/Continuum/BF4ExactSlabHeatHaarGuardObstruction.lean:206`,
gives H[chi_1^2]=1 and kills all other positive-spin terms in the pairing.
It and `inserted_sum_zero`, same file:263, were exposed with unchanged
statements and proof bodies. They are reused results, not new theorems here.

Ordinary Haar Cauchy--Schwarz then yields

    (2*w^3)^2 = H[chi_1*R_K]^2
              <= H[chi_1^2] H[R_K^2] = H[R_K^2].

The underlying inequality is `weighted_cauchySchwarz`,
`lean/YMGap/Continuum/QuaternionHaarWeightedCauchySchwarz.lean:87`,
with its weight set to one and BOTH polynomial support obligations proved.
The rational threshold is sufficient because
4*(7/8)^6=117649/65536>1. No asymptotic extrapolation, numerical experiment,
new positivity axiom or higher-spin truncation assumption enters.

## What is ruled out, and what is not

The earlier `no_eventual_small_intervals`,
`lean/YMGap/Continuum/BF4ExactSlabHeatHaarGuardObstruction.lean:340`,
ruled out the full remainder's small two-sided Interval certificate near
w=1. That alone did NOT rule out small Haar L2 variation. The new result
excludes this weaker individual-face variance cap one, even after arbitrarily
increasing the cutoff. All nome dependence is explicit in 4*w^6.

The norm theorem does not require h_K itself to be positive. For a
probability-density interpretation retain the existing positivity certificate,
for example `faceHead_certificate`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:91`,
with K>=headCutoff(w). The variance bound remains valid at every cutoff
meeting both this guard and K>=1. No guard is weakened.

This is NOT a variance lower bound for the complete endpoint V*T^n1, its
conditional Haar determinant, or a shared-heat reference law. It does NOT
refute a signed full-action estimate or the Yang--Mills gap. The live consumer
remains `terminalResidual_clearedDefect`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:158`,
against its actual full `combinedTest`, same file:71.
Its quantitative signed bound, weighted stable decomposition and spatially
uniform summation budget remain open.

Planning consequence: do not spend proof effort building a near-one
face-by-face perturbative argument whose input is this refuted bare-Haar
variance cap. A different reference or a signed interacting estimate needs
its own proved comparison; neither is supplied by the current result.
Continuum scaling, physical mass, full QFT and every-group realization remain
open. No canonical Clay atom closes.

## Verification

Two final focused checks passed through the monitored launcher, serialized
with one worker and the mandatory 20 GiB ceiling after fresh process/swap
preflights. Swap stayed at 6669.00 MiB; no competing compiler/runner was
observed. All seven new-module and 21 shared-module printed gates use only
{propext, Quot.sound}, or no axioms. Final logs contain no warnings, errors
or sorryAx. Namespace repairs changed neither statements nor resource limits.
Independent source review confirmed the original carrier, cutoff indexing,
Haar normalization, support premises, threshold and limited scope.

No sorry, new axiom, canonical frontier or analytic guard changed. Root
import added; root/full-tree/full-audit/guard NOT run. CI remains manual-only.
No literature scan occurred.

| Log under `/tmp/` | SHA-256 |
|---|---|
| `ym-heat-haar-variance-obstruction-20260917.log` | `f99fe7473c8ac4247a2e60c3c8fbec4096e3b96a547a1b242d3e06170602b04b` |
| `ym-heat-haar-guard-shared-api-20260917.log` | `217391d2f39f342ef4daae093d9fc9241614a332e7987bb5be2fcf03f6e33000` |
