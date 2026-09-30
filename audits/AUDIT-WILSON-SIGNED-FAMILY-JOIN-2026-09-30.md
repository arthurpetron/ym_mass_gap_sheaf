# Reuse of signed-family coercivity on the literal Wilson carrier

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS. The literal Wilson completed-carrier join is
kernel-checked; the fixed-nome finite estimate was already available.

## Why step back

The previous plan mistakenly treated a fixed-nome original-action
signed-family floor as missing. The source already contains it:

- `BF4ExactSlabPlaquetteAffineCoercivity.affine_partition_coercivity`,
  `lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCoercivity.lean:174`,
  retains the exact original selected action, partition Z, arbitrary signed
  coefficients and arbitrary center m. Its constants do not depend on the
  extent, number of source faces, or late heat cutoff.
- `normalized_variance_floor` in that module, :242, specializes to the
  actual interacting mean and cancels the SAME partition. The explicit
  floor is `varianceFloor`, :233, equal to lower(w)/(600*upper(w)).
- `BF4ExactSlabPlaquetteBoundaryWindow.lower` and `upper`,
  `lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryWindow.lean:45`, :46,
  are the 24th powers of the nome-dependent local floor and cap.
- `BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.family_joint_variance_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean:136`,
  already passes this estimate through the existing fixed-width joint limits.
  Its `familyExcitation_norm_floor`, :157, uses the older face-span completion.
  It is not by itself a theorem about the literal Wilson completion.

The cube-adjoint identities remain correct. Instantiating them with another
absolute local heat-floor penalty would not, by itself, improve the existing
floor. That implementation branch is suspended. Its unused, uncompiled local
support draft was discarded; no committed proof was removed.

## The missing join

For arbitrary finite physical spatial face list qs and rational coefficients c,
the new `familyExpression` is the literal signed sum of radius-zero Wilson
plaquette loops. It retains order, repetitions and signs; the empty list is
represented by zero times the unit. The coefficient identity is proved before
any positivity or limit argument.

The first and full squared source polynomials agree in one original finite
window ratio. Every mixed term is retained. Both known scalar sequences
converge to their already chosen limits, so uniqueness gives equality of the
means and diagonal moments. Subtracting the actual product of means yields
the centered norm identity. No isometry or substitution of completed carriers
is assumed.

The consumer constructs `familyExcitation` using the EXISTING all-nome Wilson
centering stream and obtains

    ||v_c||^2 >= varianceFloor(w) * sum_{p in qs} c(p)^2.

The floor requires qs duplicate-free and every listed face spatially physical.
Coefficient positivity is not required. A positive coefficient-square budget
gives a nonzero actual completed vector. Its time correlations use the SAME
existing completed time map. This last identity is not a positive-time bound.

New declarations:

- `BF4WilsonPlaquetteFamilySourcePin.familyExpression`, `source_family_span`,
  `mixedProduct_mean`, `mixedProduct_square`, in
  `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilySourcePin.lean:51`, :92,
  :135, :156.
- `BF4WilsonAllNomePlaquetteFamilyVariance.family_mean_pin`,
  `family_square_pin`, `centered_norm_pin`, `centered_norm_floor`, in
  `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:112`,
  :119, :126, :140.
- `familyExcitation`, `familyExcitation_norm_floor`,
  `familyExcitation_norm_ne_zero`, `familyExcitation_ne_zero`, and
  `familyExcitation_correlator_pin` in that module at :147, :151, :162,
  :177, :187.

## Quantitative boundary and next priority

The floor is uniform in width, finite family size and late cutoff at FIXED
strict nome 0<w<1. Widths still have different carriers. No cross-width or
changing-spacing convergence is established here.

`BF4ExactSlabPlaquetteAffineCalibrationObstruction.sixHundred_floor_le_defect_power`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean:75`,
already bounds THIS certificate by (1-w)^48/600. The same module compares it
with the available time-loss budget and rules out that direct certificate
combination for survival. This is not an upper bound on actual variance and
not a Yang--Mills refutation. The new completed join does not improve the
constant or remove that obstruction.

Next work must improve the coupled quantitative estimate, not repeat fixed-nome
coercivity. Relative-derivative dual bounds are a candidate; any absolute
minimum used to construct polynomial reciprocal approximants must disappear
from the final coercivity constant, with its remaining role in the explicit
approximation modulus recorded. Such an improved physical family estimate
is NOT proved by this checkpoint.

## Verification boundary

Both new modules passed final focused serialized monitored checks. All 15
printed public gates lie within {propext, Quot.sound}; no `sorryAx` remains.
The initial source check exposed induction syntax issues, and the initial
consumer check exposed a local-notation/binder collision. They were corrected
without increasing heartbeats or memory limits. Final logs:
`/tmp/ym-wilson-family-source-pin-20260930.log` and
`/tmp/ym-wilson-family-variance-20260930.log`.

One worker, mandatory 20 GiB hard cap, 12 GiB OS reserve and dynamic memory
telemetry. No broad root build, full audit, guard, CI change, raised memory
limit, new axiom, new sorry, old sorry discharge or canonical frontier change.
Sol supplied the finite source pin; Luna independently reviewed the scalar
join and its scope; root supplied the completion proof and all verification.
The canonical chart is unchanged and is not reprinted.
