# Audit: same-carrier dyadic relative-energy survival

Date: 2026-09-24 UTC  
Scope: `BF4WilsonAllNomeDyadicRelativeSurvival`

## Checked declarations

`YMGap.Continuum.BF4WilsonAllNomeDyadicRelativeSurvival.dyadicEnergy`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:44`)
names the completed loss of the actual padded dyadic-square excitation at its
own discrete lag `side scale`.

`dyadic_response_ge_fraction_of_relative_energy` (`:110`) proves that an
explicit relative loss bound for that SAME state, together with
`delta + theta ≤ 1`, leaves at least the fraction `theta` of its completed
norm in the lagged response.  The proof uses only eventual-order arithmetic,
completed positivity, and the exact same state and time map.

`dyadic_response_floor_of_relative_energy` (`:124`) consumes the existing
`dyadicExcitation_norm_floor` and converts the preceding norm fraction into
the explicit response floor `theta * starRatio w`.

`dyadic_relative_energy_of_loss_budget` (`:140`) consumes the existing
`centered_dyadic_loss_bound`, assumes the explicit SAME-norm budget
`lossBound ≤ 2*delta*norm`, and cancels the positive factor two constructively.
`dyadic_response_floor_of_loss_budget` (`:154`) composes this with the response
floor theorem.

`dyadic_relative_energy_of_rational_loss_budget` (`:156`) weakens the input
interface from a quotient-real budget to the explicit rational inequality
`dyadicLossBound ≤ 2*delta*starRatio w`.  It uses the existing positive norm
floor and nonnegative scalar monotonicity to recover the completed budget.

## Verification

Command:

```text
python3 scripts/safe_lean_build.py --check \
  lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean \
  --check-worker-limit-gib 2 \
  --log-file /tmp/ym-gap-dyadic-relative-survival-check6.log
```

The monitored source check exited 0.  The log printed no warnings, errors,
`sorryAx`, or classical axioms.  All load-bearing declarations audit to
`{propext, Quot.sound}`; `dyadicLossBound` is axiom-free.  No existing chart
node changes status.

## Honest boundary

The SAME-norm budget is an explicit premise.  The available cubic absolute
loss bound has not been shown to satisfy it for a changing nome/spacing/scale
trajectory.  Therefore this milestone is a genuine finite-parameter
relative-survival compiler with a rationalized interface, not a scaling-uniform gap, continuum limit,
physical mass calibration, or Clay theorem.
