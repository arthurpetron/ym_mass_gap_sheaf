# Audit: completed same-carrier norm ceiling

## Claim audited

`CRealSeminormPairingCompletion.completedInner_diagonal_le_normCeiling`
transports the explicit per-stream ceiling from the dense pairing to the
completed diagonal.  `BF4WilsonAllNomeCenteredVector.centeredVector_norm_ceiling`
and `BF4WilsonAllNomeDyadicExcitation.dyadicExcitation_norm_ceiling` specialize
that result to the actual centered Wilson carrier and its padded dyadic square.

## Declaration and dependency evidence

| declaration | location | evidence |
|---|---|---|
| `normCeiling` / `diagonal_le_normCeiling` | `lean/YMGap/Continuum/CRealSeminormPairingCompletionBounds.lean:64,88` | Computes a rational ceiling from the supplied `PairingData` and bounds every stream diagonal stage at or beyond `normBase`. |
| `completedInner_diagonal_le_normCeiling` | `lean/YMGap/Continuum/CRealSeminormPairingCompletion.lean:221` | Reindexes the same pairing stream by `n ↦ max n normBase`, proves convergence to the existing representative limit, and applies the constructive one-sided limit principle. |
| `centeredNormCeiling` | `lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:177` | Instantiates `normCeiling` on the actual `centeredStream`, with no new carrier or selected quotient representative. |
| `centeredVector_norm_ceiling` | `lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:180` | Gives the completed diagonal cap for every actual centered vector. |
| `dyadicNormCeiling` / `dyadicExcitation_norm_ceiling` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicExcitation.lean:49,52` | Specializes the same cap to every padded dyadic square at its supplied width. |

## Verification

Focused monitored checks:

```text
python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/CRealSeminormPairingCompletion.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/CRealSeminormPairingCompletion.olean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-pairing-completion-cap-check-25.log

python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.olean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-wilson-centered-cap-check-26.log

python3 scripts/safe_lean_build.py --jobs 1 \
  --check lean/YMGap/Continuum/BF4WilsonAllNomeDyadicExcitation.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeDyadicExcitation.olean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-wilson-dyadic-cap-check-28.log
```

All three checks exited 0.  The new declarations report only
`{propext, Quot.sound}` and the logs contain no `sorryAx`, `Classical`, warning,
or error.

## Boundary

The cap is explicit but depends on the supplied centered stream and therefore
on its expression, width and nome.  It is not a uniform-in-scale or
uniform-in-width bound, does not supply a response floor, and does not close
the thermodynamic, continuum, physical-mass, full OS/QFT, or every-group
obligations.
