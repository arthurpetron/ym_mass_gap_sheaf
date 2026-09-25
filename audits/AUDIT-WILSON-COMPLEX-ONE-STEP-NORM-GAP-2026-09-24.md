# Audit: same-carrier translated one-step norm contraction

## Claim audited

`BF4WilsonAllNomeComplexGap.complex_oneStep_norm_gap` is a fixed-`w`/fixed-
`width` discrete consequence of the already checked translated two-step
correlator.  It does not assert a continuum limit, a physical Hamiltonian, or
the Clay mass gap.

## Declaration and dependency evidence

| declaration | location | evidence |
|---|---|---|
| `complexTime_preserves_orthogonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:74` | Componentwise use of `completedInner_time_balance`; preserves the actual complex vacuum complement. |
| `inner_time_sum` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:85` | Rewrites the complex pairing of two translated states using the completed-time semigroup identity. |
| `inner_even_diagonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:89` | Exact `2*n` diagonal identity derived from `inner_time_sum`; no limiting argument. |
| `complex_twoStep_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:93` | Adds the two real component bounds supplied by `completed_twoStep_form_gap` on the same all-nome completion. |
| `complex_twoStep_translated` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:132` | Applies the strict bound to `CT n x` after proving translated vacuum orthogonality; exposes correlator indices `n,n+2`. |
| `complex_oneStep_norm_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:145` | Rewrites the translated correlator with `inner_time_sum` and `inner_even_diagonal`, yielding the norm-square contraction at `n+1`. |

## Verification

Focused monitored check:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.olean \
  --check-worker-limit-gib 2
```

Result: exit 0.  The generated object hash was
`28b727e7a0233cba1b04a5cdcce1b90479537cb514c1c8f2a4869f46fb91e080`.
The printed axiom set for `complex_oneStep_norm_gap` is exactly
`{propext, Quot.sound}`; the log contains no `sorryAx`, `Classical`, warning,
or error.

## Boundary

The estimate is uniform in the time index `n` but not claimed uniform in
coupling/nome `w` or lattice width.  It remains partial J02 evidence.  The
spatial/spacing rate control, A03 scaling-survival comparison, thermodynamic
and continuum passage, physical mass calibration, full OS/QFT structure, and
the every-compact-simple-group theorem remain open.
