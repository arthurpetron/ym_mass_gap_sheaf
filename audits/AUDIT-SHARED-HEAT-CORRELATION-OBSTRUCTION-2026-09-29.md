# Exact shared-heat test of the proposed neighbor budget

Date: 2026-09-29 UTC. This is a checked obstruction to a sufficient-bound
shortcut, not a new bound or counterexample for the original slab or Clay.

## Test and proof

The existing complete finite SU(2) relative heat packet has two Haar
marginals. For its fundamental coordinate tests x_0 and y_0, the new module
proves unit mass, zero means, both variances 1/4, and covariance w^3/4 at
every K>=1. All cutoff spins are retained; no tail estimate or absolute
window enters the calculation.

Declarations in
`lean/YMGap/Continuum/SU2QuaternionSharedHeatCorrelationObstruction.lean`:

- Line 53, `heat_mass`; lines 58 and 62, `left_mean` and `right_mean`;
  lines 66 and 72, `left_variance` and `right_variance`.
- Line 83, `coordinate_covariance`, from the existing
  `SU2QuaternionRelativeHeatTransmission.coordinate_transmission` and
  `RelativeHeatMarkovData.relativeHeat_lower_marginal` /
  `relativeHeat_upper_marginal`.
- Line 93, `coefficient_lower_bound`: any rho satisfying
  `2*Cov(x_0,y_0) <= rho*(Var(x_0)+Var(y_0))` must satisfy `w^3 <= rho`.
- Line 118, `coefficient_deficit_le`: the explicit necessary constraint
  `1-rho <= 3*(1-w)` whenever 0<=w<=1 and w^3<=rho.
- Lines 124--129, `testNome`, `testCutoff`, `testWeightCertificate`: the
  rational nome 7/8, the explicit cutoff headCutoff(7/8)+1, and an actual
  positive certificate for this weight. No positivity premise is left open.
- Line 134, `test_covariance`: the covariance is exactly 343/2048.
- Line 142, `test_degree_budget_obstruction`: for any rational degree>=2,
  the proposed coefficient cannot also satisfy degree*rho<1. Already
  `2*w^3=343/256>1` at the test nome.

Thus the failure is in the actual correlation, not merely the previously
obstructed coarse floor/cap estimate. Signed four-copy algebra and SU(2)
structure alone do not make a shared-heat-only coefficient small enough
for that neighbor budget.

## Exact limits of the conclusion

This is the two-endpoint heat law with unit one-sided weights. It is NOT the
actual original full-slab conditional law, whose left-only and right-only
heat factors are nontrivial and remain in
`BF4ExactSlabTwoLinkFourCopy.interactionWeight`. The new obstruction applies
to a universal estimate that also covers those unit weights; it does not
give a lower correlation bound for the full slab after its other factors
are retained.

The test coordinates are ordinary supported polynomials, not gauge-invariant
Wilson observables. A genuinely restricted observable-sector estimate would
need its own proved sector and operator compatibility and is not refuted
here. Likewise, degree*rho<1 is a proposed sufficient scalar budget, not a
necessary condition for Yang--Mills mass generation. No uniform dimensionless
gap is made a prerequisite for a physically calibrated continuum gap.

## Execution consequence

Do not next build a universal small-correlation lemma from the shared heat
factor alone. Retain the actual one-sided factors and original inverse
normalizer in a variance-relative estimate, or establish collective signed
control that does not rely on the excluded scalar budget. The existing
four-copy identity and completed normalization identity remain valid.

The useful original estimate on a justified scaling family, completed
prediction-angle passage, block geometry, thermodynamic control, nontrivial
survival, same-theory OS/QFT and physical mass, and every-group Clay target
remain OPEN. No analytic assumption bundle has been added.

## Verification

The one new module passed a focused check through the safe-build skill's
monitored launcher, one worker and the mandatory 20 GiB ceiling. All 11
printed gates report only {propext, Quot.sound}. An explicit arithmetic
proof replaced an eager closed-cutoff reduction; no limits were raised.
No new sorry, axiom, classical dependency or weakened frontier was introduced.
No full-tree/root build, broad audit, guard, progress metric or CI run.
The canonical chart's displayed claims remain unchanged.

Parallel Luna source/scope review confirmed the moment calculation and the
restricted conclusion. It found no quantitative estimate retaining both
one-sided factors in the four narrowly searched modules
`SU2QuaternionFourCopyCovariance`, `SU2QuaternionSharedFactorDeterminant`,
`BF4ExactSlabTwoLinkFourCopy`, and `BF4ExactSlabTwoLinkNormalizerPin`.
This is not a repository-wide absence claim: the existing coarse
`BF4ExactSlabSharedFaceComparison` bound remains available, with its already
documented scalar-budget obstruction.
