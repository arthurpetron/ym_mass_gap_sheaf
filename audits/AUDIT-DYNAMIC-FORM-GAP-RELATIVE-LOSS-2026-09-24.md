# Audit: dynamic form-gap family and relative loss

Date: 2026-09-24 UTC

## Scope

The source-independent dynamic family previously retained only completed
squared-norm contraction.  `BF4PhysicalDynamicVacuumSectorFormGapRelativeLoss`
adds a separate form-level certificate and does not conflate it with the
existing contraction field.  The fixed-`w=1/2` geometric staging family
inhabits this certificate, and its literal moving-centered cube channel gets a
relative-loss statement at every scale.

## Declarations

In
`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFormGapRelativeLoss.lean`:

- `DynamicVacuumSectorCompletedFormGapFamily` (lines 42--47) is the minimal
  family-indexed form-gap input.
- `marginalHalfGeometricCompletedFormGapFamily` (lines 49--53) inhabits it
  using the existing `completedSectorFormGap` at every scale.
- `channel_relative_loss_of_formGapFamily` (lines 62--75) transports the
  form gap to the literal channel norm and one-step same-object correlation.
- `channel_relative_loss_of_formGapFamily_global` (lines 80--100) exposes the
  same lag-one coefficient through the global completed Markov transfer on
  the identical embedded vector, by equality transport only.
- `channel_relative_loss_margin_positive_of_formGapFamily` (lines 102--107)
  proves the scale-wise margin positive.
- `marginalHalfGeometricCompletedFamily_movingCube_relative_loss` (lines
  111--128) specializes the result to the actual moving-centered cube channel.
- `marginalHalfGeometricCompletedFamily_movingCube_margin_positive` (lines
  130--135) gives its positive margin at every scale.

## Verification

The focused monitored check was run with one worker and a 40 GiB worker cap:

`python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFormGapRelativeLoss.lean --check-output /tmp/ym-gap-dynamic-form-gap-relative-loss.log --status-seconds 30`

Every printed declaration reports only `{propext, Quot.sound}`.  No `sorryAx`,
classical input, choice, or custom axiom appears.

## Boundary

The family uses fixed nome `1/2` and constant lattice-unit margin while its
attached spacing tends to zero.  The repository already proves that this
staging family cannot satisfy a two-sided physical-rate band.  Therefore this
milestone is a valid same-object relative-loss family certificate, not a
physical mass-gap calibration or continuum Yang--Mills construction.
