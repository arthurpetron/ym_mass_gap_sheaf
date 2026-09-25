# Audit: actual fixed-family scheduled-rate specialization

## Scope

This milestone transports the lightweight certificate for
`r^(time * 2^scale)` to the literal normalized moving-cube scheduled-rate
stream of `marginalHalfGeometricCompletedFamily`. The transport uses the
definitionally fixed rate pin and the exact floor-sampler arithmetic. It is a
rate-variation input only; it does not provide raw connected-moment variation,
continuum survival, or a positive physical mass.

## Declarations

| declaration | location | result |
|---|---|---|
| `actual_stream_eqv_geometric` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:58` | The actual scheduled stream is pointwise `Q'`-equivalent to the fixed squared rate raised to `time * 2^scale`. |
| `marginalHalfGeometric_positiveRatePowerVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:68` | For every positive integer time, constructs `SummableRationalStepVariation` for the actual normalized scheduled-rate stream. |
| `marginalHalfGeometric_ratePowerVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:77` | Adds the automatic time-zero branch, giving the compiler's all-time rational rate-variation input. |

The fixed squared base is strictly between zero and one by the existing
`cutoffUniformRate_pos`/`cutoffUniformRate_lt_one` bounds. The pointwise
transport uses `marginalHalfGeometric_latticeSteps_eq` and the existing
definitionally fixed rate specialization.

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 48 \
  --reserve-gib 8 --max-swap-gib 8 --status-seconds 30 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean \
  --check-output /tmp/ym-gap-fixed-family-rate-power-variation-specialization.olean
```

Both load-bearing declarations report only `{propext, Quot.sound}`. No
`sorryAx`, classical input, custom axiom, `native_decide`, or `noncomputable`
declaration appears.

## Boundary

The normalized moving-cube compiler now has its rational scheduled-rate input
for this concrete staging family. The raw representative variation remains an
independent required input, and the positive-time rate-power limit is the zero
obstruction proved by
`positiveRatePowerVariation_limit_equiv_zero` in
`BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.lean:101`.
Thus no positive physical mass, thermodynamic/continuum passage, OS/QFT
reconstruction, or Clay theorem is claimed.
