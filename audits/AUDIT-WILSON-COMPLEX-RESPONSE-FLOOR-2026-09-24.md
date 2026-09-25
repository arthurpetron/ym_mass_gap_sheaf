# Audit: same-carrier response-floor consumer

## Claim audited

`BF4WilsonAllNomeComplexGap.complex_even_lag_response_power_floor` converts
an explicit norm cap and an explicit positive response floor into the rational
rate comparison `floor ≤ twoStepRate^n * C` for the same complex Wilson
carrier.  The cap and response are hypotheses; this theorem does not construct
either one and does not assert parameter-uniform survival.

## Declaration and dependency evidence

| declaration | location | evidence |
|---|---|---|
| `complex_even_lag_corr_decay` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:181` | Same-object even-lag correlator bound with coefficient `twoStepRate^n`. |
| `twoStepRate_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean:48` | Supplies nonnegativity needed for `RCscale_mono`. |
| `complex_even_lag_response_power_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:210` | Composes the decay bound with the explicit cap and reflects the two `RC` inequalities to `floor ≤ q^n*C`. |

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.olean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-wilson-complex-gap-check-20.log
```

Result: exit 0.  The new declaration's axiom set is exactly
`{propext, Quot.sound}`; the log contains no `sorryAx`, `Classical`, warning,
or error.

## Boundary

This is a conditional response-floor compiler on the fixed nome/width complex
completion.  It leaves the norm-cap producer, response producer, strict rate
positivity, spacing/thermodynamic/continuum control, physical mass
calibration, full OS/QFT structure, and every-group construction open.
