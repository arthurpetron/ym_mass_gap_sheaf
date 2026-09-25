# Audit: same-carrier two-step rate-margin calibration

Date: 2026-09-24 UTC  
Scope: `BF4WilsonAllNomeTwoStepMargin`

## Checked declarations

`YMGap.Continuum.BF4WilsonAllNomeTwoStepMargin.twoStepEnergy`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTwoStepMargin.lean:38`) names the
completed lag-two loss for an arbitrary state in the existing all-nome Wilson
completion.

`vacuumComplement_twoStep_rate_margin` (`:103`) assumes an explicit positive
norm floor and a relative bound of the lag-two loss by `delta` times that same
norm.  It combines the constructive response-lower inequality with the
existing `vacuumComplement_twoStep_form_gap`, then cancels the supplied norm
floor to prove `1 - delta ≤ twoStepRate`.

`vacuumComplement_twoStep_margin_le_relative_energy` (`:112`) rewrites the
same result as the necessary rate-margin inequality
`1 - twoStepRate ≤ delta`.

## Verification

Command:

```text
python3 scripts/safe_lean_build.py --check \
  lean/YMGap/Continuum/BF4WilsonAllNomeTwoStepMargin.lean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-two-step-margin-check4.log
```

The monitored source check exited 0 after one safety refusal while the host
was below the 12 GiB reserve.  The successful log printed no warnings,
errors, `sorryAx`, or classical axioms.  All load-bearing declarations audit
to `{propext, Quot.sound}`.  No chart node changes status.

## Honest boundary

This is a backward calibration only.  It does not prove a relative loss
estimate for a changing-scale family, remove nome/width dependence, identify
the transfer rate with a physical Hamiltonian, or establish a continuum gap.
