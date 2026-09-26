# Audit: real all-nome same-carrier even-lag iteration

Date: 2026-09-25 UTC

## Result

The real all-nome Wilson completion now has a kernel-checked iteration of its
fixed nome/width two-step form estimate.  The declarations are:

| declaration | location | role |
|---|---|---|
| `completedInner_even_diagonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:174` | rewrites an even-lag same-object pairing as the norm at the intervening time slice |
| `completed_twoStep_translated` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:182` | transports the strict two-step estimate to every discrete time slice while preserving vacuum orthogonality |
| `completed_oneStep_norm_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:200` | converts the translated two-step estimate to a one-step norm contraction |
| `completed_iterated_norm_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:214` | iterates the contraction with the explicit power `twoStepRate^n` |
| `completed_even_lag_corr_decay` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:234` | gives the same-object even-lag upper bound |
| `completed_even_lag_corr_nonnegative` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:241` | gives nonnegativity of the same-object even-lag pairing |
| `completed_even_lag_response_power_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:250` | combines explicit norm-cap and response-floor hypotheses with the decay estimate |

The proof uses the existing `completedTime_preserves_vacuumComplement` and
`completedInner_time_sum` declarations in
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:158--178` and the
existing fixed-parameter rate facts `twoStepRate_nonnegative` and
`twoStepRate` from
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDenseCenteredGap.lean:143`.
No new carrier, observable, transfer, or scaling family is introduced.

The response-floor consumer concludes the rational inequality
`floor ≤ twoStepRate^n * C`; it does not manufacture either the norm cap or
the response floor.

## Verification

Focused command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean \
  --check-output /tmp/ym-all-nome-response-floor.log --status-seconds 20
```

The command exited successfully.  The file's `#print axioms` output for the
new declarations is `{propext, Quot.sound}`; `sorryAx`, classical choice, and
`native_decide` do not occur.

## Scope boundary

This is a fixed nome/width discrete result on the literal completed Wilson
carrier.  It is not a spatially uniform estimate, a changing-spacing or
changing-coupling family, an OS/GNS identification, a physical mass
calibration, a continuum/QFT construction, an all-group theorem, or the Clay
mass-gap result.  The canonical ASCII chart therefore has no marker change.
