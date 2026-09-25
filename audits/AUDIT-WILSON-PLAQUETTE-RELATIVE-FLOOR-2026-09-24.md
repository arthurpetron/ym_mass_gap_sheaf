# Audit: same-carrier normalized plaquette response

Date: 2026-09-24 UTC

## Scope

This certificate divides the explicit positive lag-two response floor by the
actual completed diagonal ceiling.  It proves a positive Rayleigh-style lower
witness for the true lag-two matrix coefficient of the same literal-width
all-nome Wilson excitation, then cancels the supplied positive norm floor to
obtain `relativeFloor ≤ twoStepRate`.  The result is fixed in nome and width;
it is not a uniform spectral gap, physical mass calibration, or continuum
theorem.

## Checked declarations

In
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteRelativeFloor.lean`:

- `relativeFloor` (lines 48--50) defines the normalized rational witness.
- `relativeFloor_positive` (lines 52--54) proves strict positivity.
- `relativeFloor_cap` (lines 56--68) proves cancellation against the actual
  diagonal ceiling.
- `plaquetteExcitation_relative_floor` (lines 70--81) proves the lower bound
  for the actual same-carrier lag-two pairing.
- `plaquette_relativeFloor_le_rate` (lines 95--109) cancels the supplied
  positive norm floor against the existing completed transfer bound.
- `twoStepRate_positive_of_plaquette` (lines 111--118) derives strict
  positivity of the existing fixed-parameter transfer rate from the positive
  same-carrier response.

## Verification

The focused monitored check used one worker and a 2 GiB worker cap; output is
`/tmp/ym-gap-wilson-plaq-relative-floor-check-58.log`.  Every new declaration
reports only `{propext, Quot.sound}`.  No `sorryAx`, `Classical`, warning, or
error was reported.

## Boundary

The normalized witness and rate positivity still depend on the nome, width,
and active-face premise.  No coupling/spacing-uniform estimate, continuum
passage, physical Hamiltonian, QFT construction, or all-compact-simple-group
result is supplied.
