# Audit: positive-time rate-power variation core

## Scope

The exact sampler arithmetic identifies the fixed-family positive-time stream
with a fixed rational base `r` raised to `time * 2^scale`, where `0 < r < 1`.
This module constructs the full summable rational step-variation certificate
for that exact dyadic-exponent stream. It is intentionally independent of the
large normalized moving-cube continuum compiler.

## Declaration

| declaration | location | result |
|---|---|---|
| `positiveRatePowerVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.lean:60` | For every rational `0 < r < 1` and positive `time`, constructs `SummableRationalStepVariation (fun scale => r^(time * 2^scale))`. |

The variation budget is `r^scale`. The exponent inequality
`scale <= time * 2^scale` gives pointwise domination, and the checked
`geometricPowerTailControl` supplies the representation-invariant antitone
tail. Both directions of the step bound are retained.

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 48 \
  --reserve-gib 8 --max-swap-gib 8 --status-seconds 30 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.lean \
  --check-output /tmp/ym-gap-fixed-family-rate-power-variation-core.olean
```

The declaration reports only `{propext, Quot.sound}`. No `sorryAx`, classical
input, custom axiom, `native_decide`, or `noncomputable` declaration appears.

## Boundary

This is the exact scalar rate-power certificate. The compiler-facing equality
transport into `normalizedMovingCubeSampledRatePower` imports a very large BF4
environment and remains a separate open bridge. Raw representative variation,
physical-rate control, thermodynamic/continuum passage, OS/QFT reconstruction,
physical mass, and the all-group Clay theorem remain open.
