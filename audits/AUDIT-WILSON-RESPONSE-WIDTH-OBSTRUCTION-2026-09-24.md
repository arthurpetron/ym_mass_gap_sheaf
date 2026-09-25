# Audit: width obstruction for the computed original-response witness

## Scope

This audit covers the new source file
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialResponseWidthObstruction.lean`.
It concerns only the explicit positive number `uniformFloor` from the
original plaquette dual-test calculation.  It does not bound the actual
transfer matrix, an actual Rayleigh quotient, a physical correlation, or a
continuum limit.

## Checked declarations

- `responseMarginBase` (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialResponseWidthObstruction.lean:31`) is the rational `1/32`.
- `detectorScale_le_margin_power` (`:58`) proves the displayed detector scale is at most `(1/32)^width`, using the temporal-face injection and the existing head-floor bound.
- `uniformFloor_le_margin_power_square` (`:85`) proves the computed response witness is at most `(1/32)^(width+width)`; the denominator is handled constructively by its lower bound one.
- `responseWidthModulus` (`:110`) is the explicit `HKConvGen.powBaseCutoff` modulus.
- `uniformFloor_le_epsilon` (`:113`) gives the resulting width modulus for every positive rational tolerance.
- `no_width_uniform_uniformFloor` (`:127`) proves that no positive rational lower floor can hold for every positive width at fixed strict nome.

## Verification

Focused command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialResponseWidthObstruction.lean \
  --check-output /tmp/ym-gap-response-width-obstruction.log
```

The command exited 0.  The printed axiom reports for all six public
declarations contain only `{propext, Quot.sound}`; no `sorryAx`, classical
axiom, or custom axiom occurs.

## Boundary

This is an obstruction to promoting this particular computed lower-witness
coefficient to a width-uniform floor.  It does not refute a stronger response
estimate and does not close A03, B04, B05, or any continuum/Clay node.
