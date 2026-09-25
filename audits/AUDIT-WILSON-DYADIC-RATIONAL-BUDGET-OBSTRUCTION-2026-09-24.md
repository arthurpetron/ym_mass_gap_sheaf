# Audit: coarse dyadic rational-budget obstruction

Date: 2026-09-24 UTC  
Scope: `BF4WilsonAllNomeDyadicRationalBudgetObstruction`

## Checked declarations

`YMGap.Continuum.BF4WilsonAllNomeDyadicRationalBudgetObstruction.dyadicSide`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:26`)
is the explicit natural side `2^scale` used by the certificate arithmetic.

`dyadicLossBoundFormula`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:28`)
is the cubic rational loss expression
`384 * (ofNat side * (ofNat side * ofNat side)) * (1-w)`.

`CoarseBudgetData`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:35`)
is a Type-level bundle carrying `rho`, `delta`, `theta`, the defect/fraction
hypotheses, and the proposed loss budget as explicit fields.

`no_rational_loss_budget`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:47`)
proves `False` from the following explicit hypotheses: `0 < 1-w`,
`0 ≤ delta`, `0 ≤ theta`, `delta + theta ≤ 1`, a coarse defect bound
`rho ≤ 1-w`, and the proposed budget
`dyadicLossBoundFormula w scale ≤ 2*delta*rho`.  The proof bounds the right
side by `2*(1-w)` while the cubic certificate is strictly larger because its
coefficient is at least `384` and `2^scale ≥ 1`.

The theorem is parameterized by an abstract `rho`; it does not import or
silently identify `rho` with `starRatio`.  An application to the existing
`starRatio` therefore still requires an explicit checked instance of the
coarse defect inequality.

`coarse_budget_data_empty`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:110`)
packages the same result as an explicit function from the Type-level budget
bundle to `False`.  Thus the proposed budget has no constructive inhabitant
under `0 < 1-w`; no excluded-middle or choice principle is used.

## Verification

Command:

```text
python3 scripts/safe_lean_build.py --check \
  lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-dyadic-budget-obstruction-check9.log
```

The monitored source check exited 0.  The log printed no warnings, errors,
`sorryAx`, or classical axioms.  The load-bearing theorem audits to
`{propext, Quot.sound}` for both printed theorems.  No existing chart node
changes status.

## Honest boundary

This is a certificate-number obstruction, not a lower bound on the actual
completed variance or loss.  It shows that the currently exposed cubic upper
bound cannot itself discharge the rational survival budget when paired with a
coarse `1-w` defect floor.  The next work must sharpen the SAME-object loss
comparison, change the scaling-family certificate, or prove a different
response route.  No uniform gap, thermodynamic/continuum passage, physical
mass calibration, or Clay theorem is established.
