# Audit: same-object even-lag correlator decay

## Claim audited

`BF4WilsonAllNomeComplexGap.complex_even_lag_corr_decay` converts the
iterated norm contraction on the existing complex Wilson carrier into the
same-object correlator estimate at lag `2*n`:

```text
I x (CT (2*n) x) <= twoStepRate^n * I x x.
```

The statement is fixed in nome and literal width and is purely discrete.

## Declaration and dependency evidence

| declaration | location | evidence |
|---|---|---|
| `inner_even_diagonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:89` | Exact same-object pairing identity `I x (CT (2*n)x) = I (CT n x) (CT n x)`. |
| `complex_iterated_norm_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:159` | Constructive induction gives the `twoStepRate^n` norm-square bound. |
| `complex_even_lag_corr_decay` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:180` | Rewrites by `inner_even_diagonal` and applies the iterated bound; no new carrier or representative is introduced. |

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.olean \
  --check-worker-limit-gib 2
```

Result: exit 0.  The generated object hash was
`3bed1b705ab0e3e6f1ef4f157a80565c4ab3f8a272439dcb6e6e130aa7e82072`.
The printed axiom set for `complex_even_lag_corr_decay` is exactly
`{propext, Quot.sound}`; the log contains no `sorryAx`, `Classical`, warning,
or error.

## Boundary

This realizes only a fixed-parameter discrete same-object decay estimate.  It
does not supply spatial/spacing uniformity, an A03 surviving excitation, a
thermodynamic or continuum modulus, a physical Hamiltonian/mass calibration,
full OS/QFT reconstruction, or an all-compact-simple-group construction.
