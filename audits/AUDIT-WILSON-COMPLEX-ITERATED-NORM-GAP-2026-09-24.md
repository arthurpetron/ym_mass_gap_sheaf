# Audit: iterated same-carrier complex norm contraction

## Claim audited

`BF4WilsonAllNomeComplexGap.complex_iterated_norm_gap` proves geometric decay
of the norm-square of every vacuum-orthogonal state under every discrete power
of the existing completed time map.  The rate is `twoStepRate^n` at fixed nome
and width.  This is not a spacing-uniform, thermodynamic, continuum, physical-
Hamiltonian, or Clay mass-gap theorem.

## Declaration and dependency evidence

| declaration | location | evidence |
|---|---|---|
| `complexTime_preserves_orthogonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:74` | The translated state remains in the same complex vacuum complement. |
| `complex_twoStep_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:93` | Componentwise addition of the existing real completed two-step bounds. |
| `complex_twoStep_translated` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:132` | Applies the strict estimate at every translated discrete time. |
| `complex_oneStep_norm_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:146` | Exact semigroup/pairing rewrite to the intervening norm square. |
| `complex_iterated_norm_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:159` | Nat induction; each step uses `RCscale_mono` with the nonnegative fixed rate, then `RCscale_RCscale` and `Q'.pow_succ`. |
| `twoStepRate_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean:48` | Supplies the constructive monotonicity witness for scaling the induction hypothesis. |

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.olean \
  --check-worker-limit-gib 2
```

Result: exit 0.  The generated object hash was
`2261715d9dabe60a51b2a9c3bba4d623abede223e2c3788d8f4703136cef2b73`.
The printed axiom set for `complex_iterated_norm_gap` is exactly
`{propext, Quot.sound}`.  The log contains no `sorryAx`, `Classical`, warning,
or error.

## Boundary

The theorem is uniform in the discrete iteration index `n`, but its rate still
depends on the nome/coupling and literal width.  It does not provide a
nonzero excitation, an A03 scaling comparison, a thermodynamic or continuum
modulus, a physical mass calibration, full OS/QFT reconstruction, or an
all-compact-simple-group construction.
