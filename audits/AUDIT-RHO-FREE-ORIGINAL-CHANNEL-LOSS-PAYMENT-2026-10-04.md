# Rho-free original channel credit and chronological loss payment

The whole-project target remains OPEN: nontrivial continuum Yang--Mills
on R^4 for EVERY compact simple group, with SAME-theory full QFT axioms
and finite positive physical mass. These are finite SU(2) source-specific
estimates, not a continuum, scaling, survival or physical-gap closure.

## Forward estimate, backward consumer

The previous absolute-band rho has a proved exponential ceiling. This
increment instead keeps the ACTUAL uncentered channel moment Q, the original
odd-law raw second moment U, original partition Z and OWN variance V.
The loss L=M-Z is computed from the SAME original channels and terminal
source; it is not assumed small or replaced by a global/reference loss.
The literal Wilson character has a cap-four certificate. Coefficient-one
summed heat-loss Cauchy--Schwarz and that certificate give

```
(Q-U)^2 <= 4*L*Q,     Z*V <= U <= 2*Q+L.
```

The second inequality uses root-free rational Young and the original
mean subtraction. No excitation/variance/loss is inverted. Zero variance
and zero loss remain allowed. Constants four and two do not depend on
perimeter, but L is parameter-dependent and no useful relative-loss bound
is supplied. These statements do not assert a uniform mass gap.

New producers are in
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean`:

| Declaration | Line | Content |
| --- | --- | --- |
| `squareOriginalRawSecondMoment` | 384 | Actual Haar integral of original marginalWeight times F^2. |
| `paddedSquare_channel_rawSecond_loss_bound` | 422 | Actual mismatch square <=4*L*Q. |
| `paddedSquare_rawSecond_le_twice_channelMoment_add_loss` | 489 | U<=2*Q+L, no norm reciprocal. |
| `paddedSquare_oddVariance_le_twice_channelMoment_add_loss` | 542 | SAME original Z*OWNVar<=2*Q+L. |

The marginal pin is `oddMoment_eq_square_channels`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:87`.
The existing original variance comparison is
`original_variance_le_projected_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:90`.
The Type-level literal cap is `paddedSquareSquareBound`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:99`.

Let ell=side(scale), a=w^(12*ell), b=w^(32*ell), d=1-b and
k=2*a-1-b>=0. The exact heat identity then yields

```
E + I/(4Z) + (k/4)*OWNVar <= (d/2)*M/Z + (k/4)*L/Z.
```

The ENTIRE source increment I is retained, with no Taylor/cubic/omitted-mode
error. This is `paddedSquare_energy_exact_loss_variance_payment`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareExactVariancePayment.lean:136`.
Its k>=0 guard has the already-proved numeric window, not a justified
physical trajectory. Arbitrary depth including zero is allowed; K>=head
and K>=2 are explicit. It does not claim a universal numerical ordering
against the earlier rho payment, since the additive loss now costs.

The actual chronological split, `originalOwnBlockCost_energy_split`,
`lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean:150`,
keeps the stage OWN center and BOTH original chronological partitions.
Writing M=Z+L in the endpoint payment gives

```
Cost + I/(4Z) + (k/4)*endpointOWNVar
 <= d/2 + (d/2+k/4)*L/Z + Drift + Signed.
```

Here Signed is the COMPLETE original signed multiplication correction,
and Drift still uses the STAGE mean. The scalar simplification uses actual
oddMass, exactly the partition in L and its reciprocal; no definitional
identification of a different partition is needed. New declarations:

- `originalOwnBlockCost_exact_loss_payment`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean:299`.
- `originalOwnBlockCost_exact_loss_boundary_paid`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean:361`.

The latter bounds ONLY Drift by computed eta times the RAW stage-centered
endpoint reference square, using `originalBoundaryDrift_upper`,
`lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean:205`.
Only that boundary-paid variant requires endpoint depth>=1.
Endpoint OWN variance, raw reference square and filtered-start norm remain
three distinct quantities. No new assumed analytic budget is introduced.

## Repointed mathematical frontier

The actual remaining sufficient estimate is JOINT control of the lag sum
of `d/2+(d/2+k/4)*L/Z+eta*RawReference+Signed-I/(4Z)-(k/4)*endpointOWNVar`
against the SAME filtered-start variance. Its backward consumer is
`original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
Do not substitute Signed=Cost-(E+Drift) and call the resulting circular
identity a new estimate. Do not silently identify endpoint and filtered
variances or drop the retained negative increment/variance terms.

Source review found no existing increment-versus-loss payment. Actual
`sourceIncrementCost`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoung.lean:87`,
integrates the square of BOTH source and observable jumps. Actual
`jump_heatLoss_pin`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:52`,
realizes twice source loss by the source jump square alone. Existing
`squareChannelIncrement_nonnegative` and
`squareChannelResponseSquares_le_increment`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:139`
and `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:156`,
give positivity and a response-square floor, not a lower comparison to L.
Absorbing the entire displayed loss penalty by I alone would suffice if
`I >= (2*d+k)*L = (4*(1-a)+3*k)*L`. This stronger input is UNPROVED and
NOT necessary: a joint signed/window estimate can instead retain the loss.
No formal impossibility for the actual endpoint sources is claimed.

Justified scaling, nontrivial continuum survival, physical mass calibration,
SAME OS/full QFT/continuum and every group remain OPEN. Partial A03 only;
no exact canonical displayed claim changes, so no ASCII/paper list reprint.

## Verification boundary

Three serialized focused checks exited 0. All SEVEN new public axiom gates
(one definition, six theorems) report exactly {propext, Quot.sound}.
The first target retains pre-existing unused GNS binder warnings; independent
diff review confirms their source lines are unchanged from HEAD. The other
two accepted logs contain no warnings/errors. Accepted logs and SHA256:

| Log under `/private/tmp/` | SHA256 |
| --- | --- |
| `ym-raw-channel-loss-credit-20261004-4.log` | `f146bc6e72bc9960ccf6d5aa212cdd78b07e546951941e0162854cfb982d0b6b` |
| `ym-exact-loss-variance-payment-20261004-2.log` | `801a31561acefa9a251c3b2d43b1513c5cb57df5bc72c9b9c6c44ad634bf32a9` |
| `ym-chronological-loss-payment-20261004-2.log` | `de2ba4e04f88e8ae6963e4dcd41fd2895498b7c3d6f3846d381d3507a43e4f7f` |

Frozen Lean source SHA256, in producer/energy/chronological order:

```
a9b4ddc55e8b2a373ef8f630ac63491930c897b5d6976d9ed763dc48747d95a5
fd2c7343f32a887f5d512771227fce18452fd8b94b41452f9338ef530a32f9dd
66ed6aa988320ad80f21b6b6c98fcd903b8bf99c48ed018058d35cf913ccbd3f
```

Independent frozen mathematical review passed. Earlier failed attempts
(transparency timeout/unfolding, rational ring-constant type, local center
notation collision) are REJECTED evidence. The first launcher invocation
was cancelled when its displayed default ceiling did not match the required
20-GiB limit; restricted process/swap inspection was replaced by permitted
host telemetry. All accepted runs used ONE monitored 20-GiB worker,
12-GiB reserve and a fresh process/pressure/swap preflight, with no competing
compiler, 75--76% free memory and zero swap. No resource settings were changed.

No new sorry/axiom/Classical/unsafe proof escape, analytic budget or weakened
frontier. Existing root imports register all three modules; registration is
NOT root verification. No full/root build, broad audit, guard or metrics run.
CI remains off. The Clay target and active goal remain OPEN.
