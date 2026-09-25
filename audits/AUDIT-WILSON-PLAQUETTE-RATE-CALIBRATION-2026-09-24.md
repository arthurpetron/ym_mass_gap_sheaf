# Audit: same-carrier plaquette rate calibration

Date: 2026-09-24 UTC

## Scope

`BF4WilsonAllNomePlaquetteRateCalibration` combines the checked positive
lag-two response floor with the existing completed strict two-step transfer
bound for the same literal-width all-nome Wilson plaquette state.  It proves
the explicit rational inequality

`twoStepFloor ≤ twoStepRate * plaquetteNormCeiling`.

The result remains parameterized by nome and width.  It is a fixed-parameter
rate calibration, not a spacing-uniform rate, a Hamiltonian mass calibration,
or a continuum/Clay result.

## Declarations

In
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteRateCalibration.lean`:

- `rcscale_as_mul` (lines 43--47) identifies completed rational scaling with
  the descended quotient product.
- `rational_scale` (lines 49--52) transports rational scaling of a rational
  quotient value to the product in `Q'`.
- `plaquette_twoStep_floor_le_rate_mul_normCeiling` (lines 54--70) composes
  `plaquetteExcitation_twoStep_floor`,
  `plaquetteExcitation_twoStep_bound`,
  `plaquetteExcitation_norm_ceiling`, and nonnegative scalar monotonicity.

## Verification

The focused monitored check was run with one worker and a 2 GiB worker cap:
`/tmp/ym-gap-wilson-plaq-rate-calibration-check-53.log`.
The log reports only `{propext, Quot.sound}` for the declarations.  No
`sorryAx`, `Classical`, warning, or error was reported.

## Boundary

The inequality constrains the already existing fixed-parameter rate and
ceiling; it does not make either quantity uniform in coupling, width, spatial
volume, or lattice spacing.  The scaling-survival, thermodynamic/continuum,
physical-mass, QFT, and every-compact-simple-group obligations remain open.
