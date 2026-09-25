# Audit: fixed-family normalization-debt variation

## Scope

The normalized moving-cube cutoff compiler needs a rational step variation for
the reciprocal-square normalization debt.  In the inhabited geometric staging
family the nome is definitionally `1/2` at every scale, so the moving-cube
floor, reciprocal scale, and squared debt are the same rational expression at
all scales.  This closes that one compiler input without selecting a quotient
representative or claiming a continuum limit.

## Declarations

| declaration | location | result |
|---|---|---|
| `marginalHalfGeometric_normalizationNormDebt_eq` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt.lean:26` | The exact `movingCubeNormalizationNormDebt` is equal at every scale to its value at scale `0`. |
| `marginalHalfGeometric_normalizationNormDebtRationalVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt.lean:33` | `SummableRationalStepVariation` for the actual debt stream, via the pointwise-constant zero-variation constructor. |

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 30 \
  --check lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt.lean \
  --check-output /tmp/ym-gap-fixed-family-normalized-debt.log --status-seconds 30
```

The focused monitored check completed successfully.  Both declarations report
only `{propext, Quot.sound}`; there is no `sorryAx`, classical input, custom
axiom, or `noncomputable` declaration.

## Boundary

This is a constant-nome staging-family input only.  The raw sampled
same-object representative variation, the normalized-limit compiler consumer,
positive-time rate-power convergence, physical-rate band,
thermodynamic/continuum passage, OS/QFT reconstruction, physical mass, and
every-group theorem remain open.  The family still has constant lattice margin
while its attached spacing tends to zero.
