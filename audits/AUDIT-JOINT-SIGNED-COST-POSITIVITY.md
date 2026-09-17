# Joint signed-cost positivity and fringe lower bound — 2026-09-17 UTC

## Whole-project goal and scope

The unchanged target is constructive continuum Yang--Mills on R^4 for every
compact simple gauge group, with the required same-theory QFT structure,
nontrivial state space, isolated vacuum and finite positive physical mass gap.
This checkpoint proves a finite-regulator SU(2) cost inequality, not that gap.

On the SAME original odd marginal nu=V*g_n*g_(n+1), write
J(q)=D(q)+2hR(q), with h=headFloor(w). The new result is

    0 <= J(q),
    (1-h) * sum_{i in fringe} ||q_i||_nu^2 <= J(q).

It holds for arbitrary supported polynomial tests q_i and arbitrary finite
component correction degrees. No conditional-centering assumption is needed.
The upper budget needed by the original-energy consumer remains OPEN.

## Original objects and exact consumer

- `marginalWeight` and `marginalPair`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:75`, `:78`,
  fix the full unnormalized original marginal. No reduced density is substituted.
- `diagonalRemainder` and `determinantRemainder`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:78`, `:88`,
  are the existing cost terms. `cost_actual_split`, same file `:206`, states
  marginalCost=h*||S||_nu^2+D+2hR, retaining signed unordered pairs.
- `actualResidual_corrected_energy`, same file `:294`, and its actual-family
  specialization `approximant_energy`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:129`,
  remain the original temporal-energy consumers. This is not a link-update
  Markov generator or a newly substituted operator.

## Checked argument

1. `finite_family_completed_square`,
   `lean/YMGap/Continuum/QuaternionHaarFiniteFamilyDual.lean:197`, completes
   the existing positive certified quadratic at z=-h*z0, b=1. If its flow
   pairing equals its product-square norm N, the result is cost>=h*N.
   The proof cancels only the known positive scalar h, never N. Zero norm
   therefore presents no exceptional case or hidden positivity assumption.
2. `oneSidedFamily`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOneSidedFamily.lean:69`,
   retains the original coordinate factors, including fringe units, and
   lifts tests to the upper endpoint. `oneSidedFamily_product_pin` (:73),
   `oneSidedFamily_flow_pin` (:141), `oneSidedFamily_cost_pin` (:205), and
   `oneSidedFamily_square_pin` (:242) identify their original quantities.
   These are one-sided insertions, not two-ended jumps: no extra factor two
   enters the flow or norm. The coefficient 2h in the pair cost is retained.
   `oneSidedFamily_floorCertificates` (:268) and
   `oneSidedFamily_tests_supported` (:279) supply the constructive inputs.
3. The old `flow_actual_pin`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:178`, makes
   the one-sided flow at S equal ||S||_nu^2. Thus `corrected_cost_norm_floor`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedCostPositive.lean:63`,
   proves marginalCost>=h*||S||_nu^2. Subtract that SAME norm using the exact
   cost split: `joint_remainder_nonnegative`, same file `:108`, gives J>=0.
4. `activeTests`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCostFringeSplit.lean:45`,
   preserves active tests and zeros the others on the original full carrier.
   `activeTests_supported` (:49) preserves support;
   `determinantRemainder_activeTests` (:90) gives literal equality of R;
   `diagonalRemainder_split` (:128) gives

       J(q) = J(activeTests(q)) + (1-h)*sum_fringe||q_i||_nu^2.

   Apply J(activeTests(q))>=0 to obtain `fringe_norm_cost_lower_bound`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedCostPositive.lean:131`.

Only fringe DETERMINANT crosses vanish. Ordinary fringe cross pairings need
not vanish; individual active determinant crosses remain signed. The remaining
active joint cost is nonnegative, not strictly positive (zero tests attain zero).

## Audit-driven next step and excluded inferences

Before building another determinant-cancellation argument, test the necessary
fringe budget on `familyTests`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamily.lean:115`, along the
constructed `approximationDegrees`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:86`.
The approximants target Phi=H[nu]*f-H[nu*f], not f; retain this normalization
and full-nu dependence. The required upper bound has controlled
width/depth/cofinal-cutoff dependence and an explicit approximation remainder.
It need only hold along a sufficient constructed schedule, not every degree.

The fringe cost depends on the first, seed degree only: `corrected`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:66`, leaves
fringe tests unchanged. Increasing the second correction degree cannot
reduce it. The actual source is still nu*Phi (`source`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:62`),
and the reciprocal approximates the full nu*(P_i nu) denominator
(`denominator`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedWindow.lean:41`;
`inverse`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:68`).

The new lower bound proves neither growth of the actual fringe sum relative
to ||Phi||_nu^2 nor failure of that schedule. Deleting fringe tests is an
algebraic diagnostic, NOT an active-only approximation theorem. No obstruction
to a different grouped-fringe or weighted-projection producer is established.
A successful fringe budget would still leave the active joint upper cost open.

The new argument needs no transfer positive-semidefiniteness theorem, exact
reciprocal, inverse-density limit, or ordinary-Haar orthogonality of weighted
tests. It does not promote a dimensionless or finite-volume bound to a
spacing/volume-uniform physical gap. The completed small-nome branch and its
known AF-guard incompatibility are unchanged; continuum/QFT and every-group
joins remain open.

## Verification boundary

Four focused serialized checks used the monitored launcher with one worker,
a 20 GiB ceiling and a fresh process/swap preflight before each invocation.
All 21 printed gates (15 new, six existing) are within {propext, Quot.sound}.
The final logs have no errors, warnings, sorryAx or classical dependencies.
Independent mathematical/source review passed, including same-marginal
normalization, the absence of a jump factor two, and the fringe lower bound.

Three new modules are registered in `lean/YMGap.lean`. No sorry was added or
discharged, no analytic premise added, and no canonical frontier field changed.
Root/full-tree build, full axiom audit and guard were NOT run. CI and machine
safety limits are unchanged. Final focused logs and SHA-256:

```text
/tmp/ym-family-completed-square-20260917.log
af6b2064e9f8a539c162f500bfbdcb8cf55f2c472f8439cbcfec9eed0794e67d
/tmp/ym-one-sided-family-20260917.log
a8f08a37c800c935c456cd5b459edc90cb40b9c7b1badeadf400b2ef7c4146c6
/tmp/ym-cost-fringe-split-20260917.log
4182bcf60ee8597764011efbd08750c912aa2b31e7db09fb84be38d7361f420b
/tmp/ym-signed-cost-positive-20260917.log
3b5195ebfca524387b1b8099c3391e2005fbd180eefda326f0bea27219d5a2e5
```
