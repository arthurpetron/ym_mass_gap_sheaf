# Audit: width-one auxiliary norm floor

Date: 2026-09-25 UTC.

The new declaration
`YMGap.Continuum.BF4ExactSlabWidthOneActualFringePairing.fringeTest_norm_lower`
is a direct consequence of the already checked
`fringeTest_norm_product_lower` at
`lean/YMGap/Continuum/BF4ExactSlabWidthOneActualFringePairing.lean:198--227`.
It defines
`fringeTestNormFloor` at `:235` as

`Q'.divPos ((1/16) * w^18) 2`,

proves positivity at `:238--242`, and proves the lower bound at `:244--272`.
The proof uses the original width-one marginal, the existing certificate for
the seed square, and the elementary coefficient estimate
`2 * (1 - w^9) ≤ 2`; it does not divide by an interacting marginal or alter
the action.

The monitored safe check was:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 40 \
  --check lean/YMGap/Continuum/BF4ExactSlabWidthOneActualFringePairing.lean \
  --check-output /tmp/ym-gap-width-one-floor.log --status-seconds 20
```

The check passed. The printed axiom reports for the three new declarations
contain only `{propext, Quot.sound}`. The result is fixed width-one,
fixed-depth auxiliary polynomial data. It is not a gauge-invariant excitation,
not a changing-scale survival theorem, and not the open A03 signed-cost versus
interacting-centered-variance comparison.
