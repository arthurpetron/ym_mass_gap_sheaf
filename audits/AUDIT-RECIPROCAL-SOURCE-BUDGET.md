# Retained reciprocal-source budget — 2026-09-17 UTC

## Whole-project goal and scope

The unchanged goal is constructive continuum Yang--Mills on R^4 for every
compact simple gauge group, with the required same-theory QFT structure,
nontrivial state space, isolated vacuum and finite positive physical mass gap.
This checkpoint sharpens a finite SU(2) family norm estimate. It proves no
regulator-uniform gap, continuum limit or new Clay completion node.

Write nu=V*g_n*g_(n+1), M_i=P_i nu, J_i,k for the actual finite polynomial
reciprocal of nu*M_i, and tau_i for the actual Haar piece of nu*Phi, where
Phi=H[nu]*f-H[nu*f]. The new retained budget is

    B_I = sum_{i in I} H[M_i*J_i,k*tau_i^2],
    sum_{i in I} ||q_i||_nu^2 <= B_I,
    ell * B_I <= sum_{i in I} H[tau_i^2].

The second inequality verifies that this is a refinement of the previous
lower-window bound, not merely an alternative expression. It retains all
original density, source, finite-degree and regulator dependence.

## Exact objects and checked argument

The original marginal is `marginalWeight`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:75`.
The actual denominator, inverse and test are `denominator`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedWindow.lean:41`,
and `inverse`/`test`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeed.lean:68`, `:116`.
`source` and `piece`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredHaarTelescope.lean:62`, `:66`,
remain unchanged; `familyTests`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamily.lean:115`, uses them.

For z=J*tau and q=M*z-P_i(nu*z), the existing
`weightedResidual_square_le`,
`lean/YMGap/Continuum/SU2QuaternionWeightedResidualNorm.lean:95`, gives
H[nu*q^2]<=H[nu*(M*J*tau)^2]. Construct the missing signs explicitly:

- `inverseCertificate`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualSeedReciprocalNorm.lean:76`,
  proves J>=0 by the actual finite geometric sum.
- `inverseResidualCertificate`, same file `:89`, proves 1-nu*M*J>=0
  using exact reciprocal cancellation and the nonnegative geometric residual.
- `reciprocalSourceCertificate`, same file `:107`, certifies M*J*tau^2>=0.
  These are nonnegative, not strictly positive: J at degree zero is zero.
- The certificate M*J*(1-nu*M*J)*tau^2>=0 compares the uncentered norm
  with H[M*J*tau^2]. Thus `test_norm_le_reciprocal_source`, same file `:118`,
  proves the claimed local bound. It needs support, not P_i(tau)=0.
- The identity

      1-ell*M*J = (1-nu*M*J)+(nu-ell)*M*J

  certifies the refinement `reciprocal_source_le_scaled_square`, same file
  `:148`. No exact reciprocal or inverse-density limit is introduced.

`sourceCost`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReciprocalSourceBudget.lean:65`,
is the computed rational B_I. `family_norm_le_sourceCost` (:73) and
`sourceCost_scaled_le_pieceSquares` (:86) sum the two bounds. Arbitrary
finite second-stage corrections preserve the norm bound through
`corrected_family_norm_le_sourceCost` (:103).

Two existing costs now have sharper explicit upper estimates:
`fringe_cost_le_sourceCost` (:118) gives fringeCost<=(1-h)*B_fringe;
`diagonal_cost_le_sourceCost` (:131) gives D<=(U-h)*B_labels.
They retain the SAME marginal and the exact factors h=headFloor(w), U=prefixCap(w).
The original joint-cost lower bound is `fringe_norm_cost_lower_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedCostPositive.lean:131`.
The upper-cost consumer is still `actualResidual_corrected_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`, with
actual-family specialization `approximant_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:129`.

## Remaining mathematical test

Control B_fringe relative to ||Phi||_nu^2 along the actual
`approximationDegrees`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:86`,
with the required width/depth/cofinal-cutoff dependence. This would suffice
to bound fringe cost. Failure to control this upper estimate alone does
NOT prove growth of the actual fringe norm or rule out another producer.
Choosing k=0 makes B zero but does not supply the required approximation.
The degree k and original global upper window remain inside J; neither
is silently omitted from the budget's definition.

The second correction degree cannot change fringe tests (`corrected`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:66`). Nor does
reordering the final label sum change the numeric projection telescope:
`partialProjection` and `term`,
`lean/YMGap/Continuum/SU2QuaternionHaarBlockTelescope.lean:46`, `:50`,
still define the source pieces. No reordered producer is constructed here.
The new estimates require no density or target independence and do not
discard action-carrying fringe coordinates. The signed active joint upper
cost and physical-scaling/continuum/QFT/every-group joins remain open.

## Verification boundary

Two focused serialized checks used the monitored launcher, one worker and
a 20 GiB ceiling, with a process/swap preflight before each invocation.
All 11 printed gates have dependencies within {propext, Quot.sound}.
Final logs contain no errors, warnings, sorryAx or classical dependencies.
Independent mathematical/source review passed the certificate identities,
normalization, finite-family aggregation and unchanged cost factors.

Two root imports were added. No sorry was added/discharged, no analytic
premise introduced, and no canonical frontier field changed. Root/full-tree
build, full axiom audit and guard were NOT run. CI and safety limits are
unchanged. Logs and SHA-256:

```text
/tmp/ym-actual-seed-reciprocal-norm-20260917.log
98387c7dc1e7eb8b906947aa6331f0e600b85166f6e8ce3912fd92cac99b3ea9
/tmp/ym-reciprocal-source-budget-20260917.log
5fa45c65d892182d267cf4b865e1ce7acc72e7f035e60d80d9fa356e954b01bb
```
