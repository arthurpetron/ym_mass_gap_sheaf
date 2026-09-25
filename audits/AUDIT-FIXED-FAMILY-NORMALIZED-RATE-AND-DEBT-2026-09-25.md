# Audit: fixed-family normalized rate and debt inputs

## Scope

This milestone closes the two rational scalar inputs that are available for
the fixed `w = 1/2` geometric staging family: the literal normalized
scheduled-rate stream and the reciprocal-square normalization debt.  It does
not construct the raw same-object CReal representative variation, and it does
not assert a positive physical mass or a continuum Yang--Mills theorem.

## Declarations

| declaration | location | result |
|---|---|---|
| `marginalHalfGeometric_normalizationNormDebtVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:75` | Converts the exact pointwise-constant rational debt certificate into the `MovingCubeNormalizationNormDebtVariation` input consumed by the constructive-real normalized-limit compiler. |
| `marginalHalfGeometric_positiveRatePowerVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:84` | Transports the checked `r^(time * 2^scale)` variation certificate to the literal normalized scheduled-rate stream for every positive time. |
| `marginalHalfGeometric_ratePowerVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:94` | Adds the exact time-zero branch and inhabits the compiler's all-time rational rate-variation input. |

The debt declaration uses
`marginalHalfGeometric_normalizationNormDebtRationalVariation` from
`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt.lean:33`.
The rate declarations use the fixed-rate pin and
`marginalHalfGeometric_latticeSteps_eq`; no new estimate is hidden in the
transport.

## Verification

The focused monitored check was:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 48 \
  --reserve-gib 8 --max-swap-gib 8 --status-seconds 30 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean \
  --check-output /tmp/ym-gap-fixed-family-specialization-debt.olean
```

All three printed declarations report only `{propext, Quot.sound}` and no
`sorryAx`, classical input, custom axiom, `native_decide`, or
`noncomputable` declaration.

## Boundary

The normalized compiler now has both scalar rational inputs for this concrete
family.  Its raw representative field still requires an explicit
`MovingCubeRawScheduledRepresentativeVariation`; the positive-time geometric
rate limit is zero by
`positiveRatePowerVariation_limit_equiv_zero`, so this family cannot calibrate
a positive physical mass.  Thermodynamic/continuum passage, OS/QFT
reconstruction, all-group extension, and the Clay target remain open.
