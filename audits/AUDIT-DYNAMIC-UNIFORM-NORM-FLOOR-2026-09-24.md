# Audit: fixed-family uniform moving-cube norm floor

## Scope

The scheduled same-object channel requires an explicit scale-uniform positive
floor before a cutoff-limit representative can prove continuum nontriviality.
For the fixed-`w = 1/2` geometric staging family, the nome is definitionally
constant, so the existing moving-coordinate floor supplies this finite-family
input.  This does not construct the scheduled representative limit, a
physical-rate band, or a continuum Yang--Mills theory.

## Declarations

| declaration | location | result |
|---|---|---|
| `marginalHalfGeometricMovingCubeUniformRCNormFloor` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorUniformNormFloorSpecialization.lean:34` | Inhabits `DynamicVacuumSectorUniformRCNormFloor` for the literal moving-cube channel, with floor `centralPhysicalVacuumSectorCoordinateFloor (1/2) 1 0`. |
| `marginalHalfGeometricMovingCube_uniform_floor_le_zeroTime` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorUniformNormFloorSpecialization.lean:49` | Transfers the same rational floor to the scheduled zero-time autocorrelation at every geometric scale. |

The proof uses the existing `centralPhysicalDynamicMovingCubeRCChannel` floor
field and `sampledConnectedAutocorrelation_zero_eq_normSq`; it introduces no
new carrier or observable.

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorUniformNormFloorSpecialization.lean \
  --check-output /tmp/ym-gap-uniform-floor-specialization.log --status-seconds 30
```

Both declarations report only `{propext, Quot.sound}` and no `sorryAx`,
classical input, custom axiom, or `noncomputable` declaration.

## Boundary

The representative-level scheduled convergence field remains open.  The
finite floor is uniform only along this constant-nome staging family; it does
not supply spacing-uniform physical decay or the scaling-survival node.
