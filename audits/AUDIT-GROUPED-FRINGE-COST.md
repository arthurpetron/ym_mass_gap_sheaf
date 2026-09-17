# Combined active and grouped-fringe estimate on the original action

Date: 2026-09-17 UTC. Parent checkpoint: `b752d9e`.

The whole-project goal is unchanged: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, with same-theory QFT
axioms, isolated vacuum and positive finite physical Hamiltonian gap.
This checkpoint proves a finite original-action inequality, not that goal.

## Mathematical result

Write g_n=T^n1, t=T^(n+1)1, nu=V*g_n*t, and h=headFloor(w). Keep the
existing active tests but zero their fringe seeds. Let A be their corrected
sum and r the entire original fringe residual sum. Then S=A+r is the
ORIGINAL corrected sum, coefficientwise. The proved inequality is

    h*<f,S>_nu^2 <= E_gn(f) *
      [h*||S||_nu^2 + D_active + 2h*R_active + (1-h)*||r||_nu^2].

D_active and R_active are the existing FamilyCost remainders evaluated
on active-only seeds; they are not newly assumed bounds. The inactive
residuals vanish coefficientwise, and componentDeterminant already
vanishes unless both indices are active. No sign is assigned to R_active.
All active--fringe cross terms remain in ||S||_nu^2. The original kinetic
product and both endpoint weights V*g_n are retained.

## Checked declaration map

| Result | Declaration and source |
| --- | --- |
| Add one unit-factor test, keeping exact signed cross cost | `prepend_unit_dual`, `lean/YMGap/Continuum/QuaternionHaarUnitFamily.lean:85` |
| Zero seed gives coefficient-zero residual | `weightedResidual_zero`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSeeds.lean:70` |
| Corrected sum from active-only seeds has no inactive contribution | `correctedSum_active`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSeeds.lean:127` |
| Active-only sum plus r is the original corrected sum | `correctedSum_split`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSeeds.lean:149` |
| One original energy for family plus grouped fringe | `grouped_fringe_marginal_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroupedFringeFlow.lean:73` |
| Exact combined cost decomposition | `grouped_cost_split`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroupedFringeCost.lean:79` |
| Full estimate for actual residuals and unchanged S | `actualResidual_grouped_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroupedFringeCost.lean:114` |
| Previously constructed approximant uses this estimate | `approximant_grouped_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroupedFringeCost.lean:154` |

The retained approximation theorem is `approximation_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:94`;
its degree witness `approximationDegrees` is at :86. Neither degree or
observable is changed by the new energy consumer.

## Why the combination is causal

Prepending (polyOne,jump(r)) to the old family changes its flow and cost by

    newFlow = kinetic*jump(r) + oldFlow,
    newCost = kinetic*jump(r)^2 + oldCost + 2h*jump(r)*oldFlow.

The existing `fringeSum_jump_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeKernel.lean:117`,
identifies the first terms with twice the SAME nu pairings. For the mixed
term, reuse `flowPair_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:188`,
with the observable equal to r. Only the OLD tests require conditional
centering. No new two-erasure compiler or orthogonality premise is needed.

`signedCost_pin`, same file:270, and the original energy identity give
new flow=2*(L(f)+<f,r>), new cost=2*(C+||r||^2+2h*L(r)), energy=2E.
The positive factor four cancels exactly. `flow_actual_pin` and
`cost_actual_split`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:178` and :206,
then give the displayed corrected-sum formula. The active-seed pin puts
the same original S on BOTH sides.

## Boundaries and remaining analytic input

This does not prove that the new cost is always smaller than the old one.
Their fringe-cost difference is
(1-h)*(||sum q_i||_nu^2-sum ||q_i||_nu^2), which has no fixed sign.
Grouping preserves cancellations; it does not prove stability of the
chosen decomposition. No active-labelled test is assumed outside the
transfer kernel, and r is not assumed orthogonal to A.

The required regulator-controlled bound on the combined cost remains OPEN.
The proposed next producer is a full-fringe weighted conditional projection:
first prove its same-action integration, kernel and orthogonality identities,
then seek a norm-controlled fringe choice. This is a proposed new
decomposition, NOT a result for the current r. Its active consumer must
keep original conditional centering or first prove an exact reduced-transfer
pin. Reduced-marginal centering alone is insufficient.

No uniform completed-sector gap, physical-time calibration, continuum
construction, full QFT reconstruction or every-group theorem is obtained.
The transfer-kernel input remains about T(g_n*r), not T(r), and only on
the finite Haar carrier.

## Verification

Four modules passed focused serialized checks via the monitored launcher,
one worker, unchanged 20 GiB ceiling, fresh process/swap preflight each time.
All 19 printed gates use only {propext, Quot.sound}. Final logs contain no
errors, warnings, sorryAx or classical dependencies. One intermediate
GroupedFringeCost check reported a missing namespace; it was corrected and
the final check is clean. No actual sorry was introduced or discharged.

An independent read-only mathematical review checked the signed mixed
terms, factors two/four, same corrected sum, and the absence of a false
universal-cost improvement claim. Four root imports were added;
root/full-tree/full-audit/guard NOT run. Canonical statements, CI and safety
limits were unchanged.

Final local log SHA-256 values (logs are not repository artifacts):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| ym-active-seeds-20260917.log | 11 | `2b2630430769b7cd249c269f9d185b3a4f3884547bd2a34ca712145e2ba56a31` |
| ym-unit-family-20260917.log | 4 | `55d07a3a9fd14e5f5a9a5befd093dc0276075a0a59e659ede5cc66c8b010adf2` |
| ym-grouped-fringe-flow-20260917.log | 1 | `9fa9abcf5b79985b19a35a934305af19511d6fa981122b15273bc5f188dc9f7f` |
| ym-grouped-fringe-cost-20260917.log | 3 | `5d497bd183e6b7be6f38e3a6befabf872919f7a478dd6f0a9e6fef3b8bb96509` |
