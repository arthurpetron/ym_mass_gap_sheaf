# Sharper original channel credit with one unchanged source leg

Three focused checks and independent frozen-source review passed. The whole
project goal remains OPEN: nontrivial continuum Yang--Mills on R^4 for EVERY
compact simple group, SAME-theory full QFT axioms and a finite positive
physical Hamiltonian mass gap. This increment improves a finite comparison.

## Mathematical meet

For the literal signed/repeated F, use the ORIGINAL projected endpoint
source q at depth n+1 and the SAME projected family spectator R. Its actual
certificates give l*R<=q<=u*R, where l=localLower(w,4*length(qs)) and
u=localUpper(w,4*length(qs)). R is independent of every active block; F is
independent of passive blocks. Let

```
S  = oddMass * OWN oddVariance(F)
A  = original full-heat raw second moment of q and F^2
Q  = original passive channel square with insertion F^2
B1 = full kineticPair(q*F^2, R).
```

Keep the first source leg q*F^2 unchanged in BOTH comparisons. Positivity
and the upper band in the second full-heat leg prove A<=u*B1. Positivity
of the actual partial-swap kernel and the lower band in its second leg
prove Q>=l*B1. The mixed conditional pair equals B1 because R is genuinely
active-independent: ONLY R is moved to the upper slice, and missing active
heat factors are restored on R alone. No positivity of an individual signed
Gram channel is assumed. Thus

```
l*S <= l*A <= l*u*B1 <= u*Q
rho_new*S <= Q,   rho_new = l*recipPos(u) > 0
rho_old <= rho_new,   rho_old = l^2*recipPos(u^2).
```

The last comparison uses the actual l<=1<=u scalar bounds. The original
uncentered moment bounds OWN variance; no change of mean or law is hidden.
No source mass, excitation norm or variance is inverted. Empty families,
zero variance, arbitrary signed coefficients and repeated faces are included.

The COMPLETE existing energy estimate now gives, for h=1-w and t=h^2/2,

```
E + 48*t*rho_new*S <= (h+t)*C*S - t*Curvature + ErrorBudget.
```

The original action, nome, cutoff, depth, source, OWN center, odd partition
and channel schedule remain unchanged. Leading C, signed curvature and the
ENTIRE cubic/omitted-mode error are retained verbatim. This replaces only
the earlier squared-band payment by a provably larger linear-band payment.

| Declaration | Source | Role |
| --- | --- | --- |
| `familyChannelPair_spectator_full` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelLinearBand.lean:146` | Actual mixed conditional/full-heat pin with active-independent R only. |
| `channelSquare_sourceMoment_linear_band` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelLinearBand.lean:201` | One unchanged first leg gives l*A<=u*Q. |
| `family_channel_square_linear_variance_credit_cleared` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:324` | SAME original odd partition and OWN variance. |
| `channelObservableSquareLinearVarianceCredit` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:370` | Computed positive l/u; only positive scalar u inverted. |
| `channelObservableSquareLinearVarianceCredit_positive` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:375` | Positivity at fixed nome/family size. |
| `family_channel_observableSquare_linear_variance_credit` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:382` | Actual retained-square comparison rho_new*S<=Q. |
| `channelObservableSquareVarianceCredit_le_linear` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:430` | Checked dominance over the earlier squared credit. |
| `channelSquareLinearEnergyVariancePayment` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean:125` | Computed 48*t*rho_new. |
| `channelSquareLinearEnergyVariancePayment_positive` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean:130` | Positive fixed-member energy payment. |
| `padded_family_energy_paid_channel_square_linear` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean:143` | Direct COMPLETE original-energy consumer. |

## Rejected join and remaining analytic input

Q is NOT identified with the passive `sourceMoment(q,F^2)`. The channel
pair shares every unselected coordinate; the partial productMap erases
them. Only the MIXED pairing with active-independent R admits the full-heat
pin. This distinction was caught by source and independent mathematical
review before verification.

The stronger credit still depends on nome and the complete family size.
The first-order coefficient C is unchanged. Its existing limitation remains:
`channelLeadingCoefficient_ge_ninetySix`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelCoefficientFence.lean:81`.
No useful uniform lower bound or small corrected energy ratio is proved.
NEXT is useful joint control of the COMPLETE residual

```
(h+t)*C*S - t*Curvature + ErrorBudget - 48*t*rho_new*S
```

against SAME surviving variance on an explicitly justified changing family,
then the actual chronological filtered/window comparison. The macro consumer
`aggregate_window_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`, remains
unsupplied. Nontrivial continuum survival, physical calibration, SAME OS/QFT
passage, every compact simple group and Clay remain OPEN. Partial A03 support
only; canonical chart claims are unchanged, so no ASCII chart is reprinted.

## Verification boundary

Accepted checks each exited 0 without warnings/errors. All 19 printed gates
(ten new) report only {propext, Quot.sound}:

- `/private/tmp/ym-passive-channel-linear-band-20261004-3.log`: two gates;
  SHA256 `0d5ceab0c94a672c35da257eed313b170254d0ff69509438417bf9515e4bdcc9`.
- `/private/tmp/ym-original-channel-linear-credit-20261004-1.log`: eleven
  gates, five new; SHA256
  `e306779e1c28b5975214589c9e4db89784131def06494881b960e9bc1c80056c`.
- `/private/tmp/ym-original-channel-linear-payment-20261004-1.log`: six
  gates, three new; SHA256
  `ece4e69636efb0b536ba81a25416668711873c565d1aacb736f61ec56c1649d3`.

Frozen source SHA256:

- `SU2QuaternionPassiveChannelLinearBand.lean`:
  `9f1510b9c3958448b7829a97f837b04ab2d9ec0d439ea73f3912b26eaac3fd51`.
- `BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean`:
  `509da7eaf5d96cc1fd53f2a6448727c017bfe3476914365e8a868fb455389fe5`.
- `BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean`:
  `f50bf97cb45ac57cc9aa6eff346e598d536f2db3751978a1d6a3ce008aad1f1c`.

The first two producer attempts failed on namespace/associativity repairs
and are REJECTED evidence. No heartbeat or resource increase was needed.
Each run used ONE monitored worker capped at 20 GiB with a 12-GiB reserve
and fresh process/memory-pressure/swap checks; swap was zero. Independent
frozen semantic review passed. No new sorry, axiom, Classical/native_decide/
noncomputable declaration, analytic premise or weakened frontier. Root
registration is NOT root verification. No full/root build, broad audit,
guard or metrics run; CI stays off. No ASCII or paper-list reprint.
