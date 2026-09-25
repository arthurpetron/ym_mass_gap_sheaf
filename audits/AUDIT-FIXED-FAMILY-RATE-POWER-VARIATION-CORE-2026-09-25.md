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
| `positiveRatePowerVariation_limit_equiv_zero` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.lean:101` | The completed CReal limit of that exact positive-time stream is equivalent to `CReal.ofQ' 0`, with an explicit epsilon/stage argument. |

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
transport is now discharged for the concrete geometric staging family by
`BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization`;
other families still require their own pointwise bridge. The new limit theorem
records a concrete obstruction: at positive time this geometric spacing family
has zero rate-power limit, so it cannot itself calibrate a positive physical
mass. Raw representative variation, a different physical-rate scaling family,
thermodynamic/continuum passage, OS/QFT reconstruction, physical mass, and the
all-group Clay theorem remain open.
