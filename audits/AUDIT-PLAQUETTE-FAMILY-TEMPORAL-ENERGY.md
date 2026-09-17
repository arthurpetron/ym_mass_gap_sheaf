# Signed-family original temporal energy

Date: 2026-09-17 UTC. Pre-change checkpoint: `628f6e215364354760a0d26f7afd5f12e9965e9d`.
This report records a new checked finite theorem and a read-only review of
its next analytic consumer. It does not close a canonical Clay frontier.

## Result and parameter scope

For every rational nome 0<w<1, heat cutoff K>=headCutoff(w), spatial width,
terminal depth n, duplicate-free physical spatial plaquette list qs and
arbitrary rational coefficients c, the original spatial polynomial
f=sum(c_p*chi_p) satisfies

    L(w)*sum(c_p^2) <= 600*U(w)*normalizedEnergy(f).

The declaration is `family_energy_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`.
The actual polynomial is `spatialSpan`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilySchedule.lean:61`.
No positivity of coefficients or common private link is assumed. Repeated
labels cannot be counted as independent coefficients: nodup is explicit.

The positive constants are `lower` and `upper`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryWindow.lean:45` and
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryWindow.lean:46`, namely
min(headFloor(w),1)^24 and (1+prefixCap(w))^24. Positivity is certified by
`lower_positive` and `upper_positive` in that module at :48 and :51.
These constants depend explicitly on nome, not width, depth, family size or
cofinal K. This is not a coupling-uniform or physical-spacing mass bound.

## Checked causal composition

1. `normalized_family_coercivity`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:77`,
   divides the previously proved full-action bound by its SAME positive
   partition. It retains the entire squared signed insertion, including
   every cross term. The input is `family_partition_coercivity`,
   `lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualFamily.lean:374`.
2. `doubledLabels`, `doubledCoeff`, `doubledLabels_nodup`,
   `doubledLabels_physical`, and `doubled_square_sum`, respectively
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyLabels.lean:35`,
   :42, :83, :97 and :114, place c at time n and -c at time n+1.
   The two time copies are disjoint. Their coefficient-square sum is
   exactly twice the source square sum. The identity itself needs no nodup;
   applying the original family lower bound does.
3. `difference_source` and `difference_placed`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilySchedule.lean:194`
   and :209, prove coefficient-level identities before Haar integration.
   They identify the signed schedule with the original jump and with the
   doubled-label source. Their squares are transported by
   `windowRatio_span_mul_originalFiniteValue`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowProbeSpan.lean:215`.
4. `normalizedEnergy_window`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:109`,
   identifies that normalized squared jump with twice the actual temporal
   energy. The coefficient doubling and energy doubling cancel, leaving
   exactly 600*U, not 1200*U or 300*U. The original denominator is
   `oddMass`, same module :64, and `oddMass_compactPartition` at :75
   identifies its 2*n+1 transitions. The chosen chain keeps n transitions
   on either side of the central one-step window.

Only the positive original partition and the positive rational two are
cancelled. The argument never divides by a coefficient, a coefficient
square sum or an observable norm; empty/zero families remain valid.

## Next analytic consumer: not supplied by this theorem

The exact consumer is `clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
With g=g_n, Z=m(g*Tg)=oddMass, A=m(g*Tg*f^2), B=m(g*Tg*f), and S=sum(c_p^2),
the path-specific remaining upper comparison is

    Z*A-B^2 <= C(w)*Z^2*S.

Together with the new energy lower bound, a positive C would give the
cleared fraction L/(600*U*C). This is a mathematical consequence, not a new
unconditional Lean gap theorem. The same odd-marginal moments are pinned by
`marginal_middleRatio`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:130`.
The comparison must have the regulator control required on the chosen
justified coupling domain/scaling trajectory. An all-nome theorem would be
sufficient but is not a prerequisite imposed by the unchanged Clay target.

**NOT FOUND:** a producer of this upper bound beyond the current small-nome
guards, uniform in width, depth and cofinal cutoff, in the searched modules.

- `finite_covariance_distance_bound`,
  `lean/YMGap/Continuum/BF4ExactSlabSelectedTwoProbeCovariance.lean:86`,
  retains `hsmall`, `hd` and `hs`. These persist in
  `connectedScalar_uniform_bound`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformConnectedDecay.lean:193`.
- `covariance_bound`,
  `lean/YMGap/Continuum/BF4ExactSlabTwoProbeCovariance.lean:153`, transports an
  assumed determinant estimate; it does not supply the missing estimate.
- `windowRatio_covariance_bound`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedCovariance.lean:95`,
  concerns temporal separation with a width-dependent computed rate.
  `no_width_uniform_computed_rate`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:132`,
  rules out promotion using that rate, not stronger actual estimates.
- `plaquette_mass_square_le`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteDefect.lean:94`,
  gives the original single-face cap four. Applying ordinary Cauchy--Schwarz
  to a sum of these caps retains a family-size factor; this observation is
  a paper-level review, not a new formalized sharpness theorem.
- `marginal_variance_cap`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletCoercivity.lean:174`,
  retains the width-dependent kinetic cap and another interacting variance.

Additional searched files, all under `lean/YMGap/Continuum/`:
`BF4ExactSlabFixedSpatial{ActualMarginalWindow,OddLocalVariance,SpatialVariance,JointCentralVariance,InputCovariance,ConditionalMessage,LocalDirichletCoercivity}.lean`
and `BF4ExactSlab{PlaquetteConnectedCovariance,StarLocalInfluence,ConnectedCoefficientBound,AllNomeFaceSetComparison,RootedResponseResummation,ConnectedFaceResponse}.lean`.
The sparse DUAL Gram estimate does not state that the original interacting
covariances vanish outside its interference graph.

## Preserved boundaries

The completed fixed-spacing small-nome branch remains proved:
`completed_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionCompletedGap.lean:153`, and
`normalizedCertificate`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean:165`.
The new theorem does not extend those results along an AF scaling trajectory.
Signed fundamental sums still do not by themselves cover products, the
physical time orbit or the full dense sector. No full OS/QFT, physical mass
calibration, continuum or all-compact-simple-group closure is claimed.

## Verification

All three new modules passed focused serialized checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`, with
explicit `.olean` outputs. Final logs contain no errors or sorryAx.
All 17 printed gates lie within {propext, Quot.sound}; four are axiom-free.
An independent source review checked the action, partition, signs,
normalization, factor two, cofinal cutoff shift and degenerate cases.

Final logs and SHA-256:

- `/tmp/ym-plaquette-family-labels-20260917.log`:
  `5982ef3d41a0885a781352eddd1666997a773a09c785a4300b638cbcd820b583`
- `/tmp/ym-plaquette-family-schedule-20260917.log`:
  `d253ad85a50f561edec5a290a2b3ed8adc78d99825a51be59e4573ba63dabfff`
- `/tmp/ym-plaquette-family-energy-20260917.log`:
  `552374d1fee0e364681d27bfdf568ab681824e4daaa311ab3cd29def68c4e4b9`

Three root imports added. No sorry introduced/discharged, new axiom,
analytic premise, canonical field, resource setting or CI change.
Full-root build/audit/guard/progress NOT run.
