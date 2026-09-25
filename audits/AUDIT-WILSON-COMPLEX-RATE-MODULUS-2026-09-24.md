# Audit: even-lag positivity and scalar rate modulus

## Claims audited

`BF4WilsonAllNomeComplexGap.complex_even_lag_corr_nonnegative` proves
nonnegativity of each even-lag same-object correlator on the complex Wilson
carrier.  `complexRateCutoff` and `complexRateCutoff_bound` provide an explicit
constructive cutoff for the scalar coefficient `twoStepRate^n`, conditional on
strict positivity of that rate.

The cutoff is not an absolute observable modulus: the correlator estimate is
scaled by the selected state's norm, and a separate norm cap is still required.

## Declaration and dependency evidence

| declaration | location | evidence |
|---|---|---|
| `inner_even_diagonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:89` | Exact pairing identity at even lag. |
| `inner_nonnegative` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexification.lean:329` | Nonnegative real component of every complex diagonal pairing. |
| `complex_even_lag_corr_nonnegative` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:188` | Rewrites the lagged correlator to a diagonal norm and applies `inner_nonnegative`. |
| `complexRateCutoff` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:196` | Defines `HKConvGen.powBaseCutoff` at the actual `twoStepRate`. |
| `complexRateCutoff_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:199` | Applies `HKConvGen.pow_base_le_cutoff`; explicitly requires `0 < twoStepRate` and `epsilon > 0`. |
| `twoStepRate_lt_one` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean:53` | Supplies the strict upper-rate premise. |

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.olean \
  --check-worker-limit-gib 2
```

Result: exit 0.  The generated object hash was
`3dd996583c81bd8cf4ac0bbddaca27139c42774bacffa35a68dda121eb8cb20b`.
The printed axiom sets for all three new declarations are exactly
`{propext, Quot.sound}`; the log contains no `sorryAx`, `Classical`, warning,
or error.

## Boundary and missing certificate

The all-nome rate has only a nonnegative theorem in the current dependency
path; strict positivity is therefore an explicit premise here, not silently
inferred.  The rate cutoff controls only the scalar coefficient.  A uniform
absolute correlator modulus still needs a same-carrier norm cap and a justified
parameter-uniform rate/positivity certificate.  Spacing, thermodynamic,
continuum, physical-mass, full OS/QFT, and all-group obligations remain open.
