# Audit: fixed-family normalization-scale ceiling

## Scope

The fixed `w = 1/2` geometric family has a definitionally constant nome and
therefore a definitionally constant reciprocal moving-cube normalization
scale.  The new certificate packages that stream as the generic global ceiling
consumed by the raw nontriviality and normalization-debt routes.

## Declarations

| declaration | location | result |
|---|---|---|
| `marginalHalfGeometric_normalizationScale_eq` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizationCeiling.lean:34` | Exact reciprocal normalization scale is equal at every geometric cutoff to its scale-zero value. |
| `marginalHalfGeometric_normalizationScaleCeiling` | same file `:41` | Inhabited `MovingCubeNormalizationScaleCeiling` for the actual fixed-family channel. |
| `marginalHalfGeometric_normalizationScaleCeiling_uniformNormFloor` | same file `:53` | Generic raw-channel `DynamicVacuumSectorUniformRCNormFloor` obtained from that ceiling. |
| `marginalHalfGeometric_correlationSqDebt_le_ceiling_fourth` | same file `:61` | Uniform fourth-power normalization-debt bound for every geometric cutoff. |

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 30 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizationCeiling.lean \
  --check-output /tmp/ym-gap-fixed-family-normalization-ceiling.olean --status-seconds 30
```

The check completed successfully.  All four declarations report only
`{propext, Quot.sound}`; no `sorryAx`, classical input, custom axiom, or
`noncomputable` declaration appears.

## Boundary

This closes a finite scalar certificate only.  It does not provide raw
representative variation, positive-time scheduled-rate variation, a physical
rate band, thermodynamic or continuum passage, OS/QFT reconstruction, physical
mass, or the all-group Clay theorem.
