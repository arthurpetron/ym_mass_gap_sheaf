# Audit: no schedule rescues the computed two-step rate

Date: 2026-09-25 UTC

## Checked declaration

`YMGap.Continuum.BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.no_width_uniform_computed_twoStepRate_schedule`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.lean:173-232`)

For every constructive nome schedule `nome : Nat → Q'` with explicit witnesses
`0 < nome width` and `nome width < 1`, and every rational `q` with
`0 ≤ q < 1`, the theorem proves that it is impossible to have

```text
∀ width, 0 < width →
  twoStepRate (hnome0 width) (hnome1 width) width ≤ q.
```

The proof selects `r = (1+q)/2`, chooses the explicit width modulus for
`e = (1-r)/2`, applies the existing width-only estimate
`mixFraction ≤ (1/32)^width ≤ e` at that width, and then shows
`q < r² < mixRate² = twoStepRate`.  It therefore applies equally to an
arbitrary coupling schedule; changing the nome cannot repair this particular
computed `mixRate^2` certificate.

## Scope boundary

This is a negative result about the displayed scalar certificate
`twoStepRate := mixRate * mixRate`.  It is not a bound on the actual transfer
operator beyond the existing fixed-parameter theorem, not a disproof of a
different rate estimate, and not a Yang--Mills or continuum statement.  The
roadmap node “spatial and spacing control of the rate” therefore remains open:
the next positive route must change the SAME-operator estimate, not merely
retune the coupling in this formula.

## Verification

Command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.lean \
  --check-output /tmp/ym-two-step-schedule.log --status-seconds 20
```

Exit code: `0`.  The printed axiom report for the new declaration is exactly
`[propext, Quot.sound]`; no `sorryAx` or forbidden classical axiom occurs.

