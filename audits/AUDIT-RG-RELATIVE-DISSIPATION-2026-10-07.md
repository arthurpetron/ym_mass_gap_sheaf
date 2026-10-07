# Relative RG dissipation and ordinary budget (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple gauge group, the required
SAME-theory QFT structure and a positive physical Hamiltonian mass gap.

Continuation of `8a347c79`. This checkpoint proves a better sufficient
comparison/budget reduction, not its Yang--Mills analytic instance.

## Relative comparison on the actual completed carriers

Write A for the original fine squared norm, F for its actual time-two squared
norm, B for the mapped coarse squared norm and C for its actual time-one
squared norm. The required estimates are

```
B <= A,       F <= delta*A+(1-delta)*C,       C <= rC^2*B.
```

For `0<=delta<=1`, `0<=rC<=1`, these give
`F <= alpha*A`, with `alpha=delta+(1-delta)*rC^2`.
The existing SAME-carrier recovery gives rate `(3+alpha)/4` and margin
`(1-delta)*(1-rC^2)/4`.

- `lean/YMGap/Continuum/BF4WilsonAllNomeRGRelativeDissipation.lean:40`,
  `relativeFactor`; `:42`, `relativeFactor_error`: its additive error is
  exactly `delta*(1-rC^2)`, with kappa=1.
- Same file `:102`, `relative_comparison_iff_dissipation`: the signed
  comparison is equivalent to `(1-delta)*(A-C) <= A-F`.
- Same file `:123`, `twoStepFactor_of_relative_comparison`; `:152`,
  `contraction_of_relative_comparison`: the actual original completed fine
  and coarse inner products/time operators are used. No lower norm bound,
  map linearity or norm inverse is assumed. The two-step factor theorem
  itself needs only `delta<=1`; recovery adds the stated sign/rate guards.
- Same file `:50`, `relativeFactor_nonnegative`; `:56`,
  `relativeFactor_le_one`; `:70`, `relativeRate_margin`: factor caps and
  recovered margin are proved, not independent numerical assumptions.

This removes an unnecessary coercivity demand: directions sent to zero by
the map can have positive fine norm, provided their actual time-two norm is
at most delta times that norm. It does NOT say the full new hypothesis
package follows from the old `ApproxRgIntertwiner` package. Its relative
comparison is a separate analytic obligation; old canonical fields remain.

## The computed upper margin pays the dyadic error weight

Use the existing recurrence at kappa=1, with
`epsilon_n <= delta_n*(1-r_n^2)`, nonnegative epsilon and delta.
The already proved OWN computed margin ceiling gives
`1-r_n <= (1-seed)*2^(-n)`. The polynomial inequality
`1-r_n^2 <= 2*(1-r_n)` then yields

```
2^n*effectiveDefect_n <= 2*(1-seed)*delta_n.
```

Thus ordinary prefix sums `sum_{k<n} delta_k <= D` feed the EXISTING weighted
budget with `S=2*(1-seed)*D`. The existing sufficient seed floor becomes
`(1-seed)*(seed-D)`, positive when `D<seed<1`.

- `lean/YMGap/Continuum/BF4WilsonAllNomeRGDissipationBudget.lean:66`,
  `weightedEffectiveDefect_le_relative`: no all-scale contraction, rate cap
  or positive lower margin is a premise of the weight cancellation.
- Same file `:103`, `relativeError_summable`: joins ordinary prefix sums to
  the existing `RgErrorSummable` predicate, with explicit sign guards.
- Same file `:132`, `seedFloor_relativeBudget_eqv`; `:152`,
  `seedFloor_relativeBudget_positive`; `:161`,
  `computedMargin_lower_of_relativeBudget`: exact floor and existing lower
  margin theorem, not an assumed lower envelope.
- Same file `:178`, `relativeRate`; `:186`, `relativeError`: explicit
  recursive rates and their own errors. `:190`, `computedRate_relativeError`,
  proves literal equality to the existing computed sequence.
- Same file `:203`, `relativeRate_bounds`; `:220`,
  `relativeError_nonnegative`; `:232`, `relativeRate_margin_lower`: under
  `0<=seed<1`, `0<=delta_n<=1`, `0<=D<seed` and the supplied ordinary prefix
  budget, the constructed rates have
  `2^(-n)*(1-seed)*(seed-D) <= 1-r_n`.

No external numerical self-consistency is assumed by this specialization.
No infinite series convergence without a modulus is asserted: the required
budget and conclusion are inequalities for every finite prefix/scale.

## Original-action ingredients and prohibited replacement

The exact integrated action remains
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:188`,
`original_twoLayer_gluing`, with `middleIntegrand` at `:61` and `gluedMiddle`
at `:73`. It retains `K01*V1*K12` under the middle Haar integral and the
outside spatial factors. Bare heat composition does not remove V1 or identify
this kernel with a separately selected coarse heat/spatial action.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:138`,
`blockNoise_variance_loss`, supplies the exact finite signed identity

```
m(noise_t(g,f)) = m(g*T^(2t)(g*f^2)) - m((T^t(g*f))^2).
```

Its endpoint term is not silently identified with A above. The existing
padded-square filtered scalar already reaches the SAME completed OS response:
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136`,
`originalOwnBlockVariance_converges`;
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:159`,
`centeredVector_time_pairing`;
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:158`,
`completedInner_time_sum`. These fixed-parameter scalar pins do not supply
the changing-action all-vector estimate.

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalNoiseVacuumObstruction.lean:44`,
`blockNoise_one`, proves exact cancellation for f=1, without support or
positivity hypotheses. Same file `:68`, `terminal_input_not_le_noise`, uses
the actual positive terminal squared mass under `0<w<1` and
`K>=headCutoff w` to rule out bounding arbitrary input mass by ANY scalar
multiple of that noise. This is NOT a vacuum-complement no-go or a theorem
about a reciprocal algorithm's actual residual. Centering eliminates this
particular example, not the remaining quantitative comparison obligation.

## Verification and next producer

Three final serialized focused checks passed 7+9+2 printed axiom gates, all
within {propext, Quot.sound}; `computedRate_relativeError` uses no axioms.
The precise dependency-complete target
`+YMGap.Continuum.BF4WilsonAllNomeRGDissipationBudget:olean` also passed.
Missing namespace/constant-polynomial elaboration failures were repaired and
are not verification evidence. Independent read-only review confirmed the
mathematics, non-circular recurrence and stated obstruction scope.

Final focused logs and SHA-256:

- `/private/tmp/ym-oct7-rg-relative-dissipation.log`:
  `81d77c6a0bfae4008ec33791cfd46885cd0e8ccbb96e52a6ed9efecff990b822`.
- `/private/tmp/ym-oct7-rg-dissipation-budget.log`:
  `a9e8565521c0b9d8473e3a0e30d224a97fa1d204c77d9b5fc1bcba24bb54cfec`.
- `/private/tmp/ym-oct7-conditional-noise-vacuum.log`:
  `189d8f75ba4e04321576ebaa91b994bb36da17d7771ac118847f785b16a038ae`.

All checks used the monitored launcher, one 20-GiB compiler, 12-GiB reserve
and current capacity checks; swap remained zero. No source holes, new axioms,
classical shortcuts, changed canonical fields or raised heartbeats. Root
imports are registered; no full-root/tree build or audit is claimed, the
hashed baseline is not regenerated, and CI remains off.

NEXT: construct an actual fine/coarse map and prove the relative dissipated-
form comparison with a useful ordinary delta prefix budget, retaining full
middle spatial action, signed terms and separately normalized OWN forms.
Independent AF window survival, justified spacing/volume control, the SAME
limiting OS/QFT theory, every compact simple group and Clay remain OPEN.
The canonical broad chart is unchanged and is not reprinted.
