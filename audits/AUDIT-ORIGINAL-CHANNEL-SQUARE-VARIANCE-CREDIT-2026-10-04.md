# Original channel square versus SAME interacting variance

Two final narrow checks and independent source review passed. The unchanged
goal remains nontrivial continuum Yang--Mills on R^4 for every compact simple
group, with SAME-theory full QFT axioms and a finite positive physical mass
gap. This increment pays one finite analytic sub-input, not that goal.

## Constructed comparison and direct consumer

For the literal signed/repeated family F=spatialSpan(width,coeff,qs), retain
the ORIGINAL projected terminal source q at depth n+1, its actual passive
channel sources b_z and nonnegative weights lambda_z. Write

```
S   = oddMass * oddVariance(F)       (ORIGINAL partition and OWN center)
Q   = sum_z lambda_z * H[(b_z*F)^2]
l   = localLower(w,4*qs.length)
u   = localUpper(w,4*qs.length)
rho = l*l*recipPos(u*u)             (constructed positive scalar)
```

The same actual projected family spectator R occurs in BOTH source bands.
For B=channelMass(R)*H[F^2], the checked comparisons are

```
l^2*B <= Q
S <= originalRawSecond(q,F^2) <= u^2*B
l^2*S <= u^2*Q
rho*S <= Q.
```

The first comparison orders the WHOLE weighted channel sum, not individual
signed channel sources. The second uses the original uncentered moment to
bound OWN variance; it does NOT compare Haar norms after changing the mean.
The original positive partition normalization is cleared through existing
marginal/projected-source pins. No excitation norm, channel mass or variance
is inverted. Signed coefficients, repeated faces, empty families and zero
variance require no exception.

The existing complete-energy estimate retains -48*t*Q, where h=1-w and
t=h^2/2. The new direct consumer pays the square by

```
E + 48*t*rho*S <= (h+t)*C*S - t*Curvature + ErrorBudget.
```

E is the COMPLETE original temporal energy. Curvature is still signed;
the entire actual cubic/omitted-cutoff error remains. The nome, cutoff,
depth, action, source, channel schedule, partition and OWN mean are unchanged.
The payment is strictly positive for 0<w<1 at each finite family size. Its
definition names w and size; no useful uniform lower bound along a changing
coupling/observable family is asserted.

| Declaration | Source | Role |
| --- | --- | --- |
| `original_variance_le_projected_square` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:88` | SAME OWN variance bounded by the original raw second moment. |
| `familyChannelObservableSquare_eq_channelSquare` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:142` | Exact original retained-square/channel insertion pin. |
| `family_channel_square_variance_credit_cleared` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:166` | Actual bands with one common spectator prove l^2*S<=u^2*Q. |
| `channelObservableSquareVarianceCredit` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:262` | Computed l^2/u^2, nome/family-size dependent. |
| `channelObservableSquareVarianceCredit_positive` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:270` | Strict positivity from actual scalar band witnesses. |
| `family_channel_observableSquare_variance_credit` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:280` | Original variance-relative retained-square comparison. |
| `channelSquareEnergyVariancePayment` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean:40` | Computed 48*t*rho coefficient. |
| `channelSquareEnergyVariancePayment_positive` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean:45` | Positive fixed-member payment. |
| `padded_family_energy_paid_channel_square` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean:62` | Direct COMPLETE original-energy consumer, with signed curvature/error retained. |
| `localLower`, `localUpper` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`, `:47` | Original floor/cap powers; dependence is explicit. |
| `padded_family_energy_le_retainedChannelVariance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare.lean:357` | Existing actual energy bound consumed without a new analytic premise. |

## Backward meet and remaining obligations

The retained negative-square comparison is now supplied, not assumed. The
signed curvature and complete error are not yet bounded jointly with the
leading term by a useful SAME-variance coefficient on the justified changing
family. The actual chronological signed-window reserve remains unsupplied:
`aggregate_window_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:181`.
The existing band-leading coefficient fence remains in force:
`channelLeadingCoefficient_ge_ninetySix`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelCoefficientFence.lean:81`.
This new finite credit does not assert that the corrected total coefficient
is scaling-small. Nontrivial continuum survival, physical calibration,
same-object OS/QFT limits, every compact simple group and Clay remain OPEN.
Partial A03 support only; exact canonical chart claims are unchanged.

## Verification boundary

Accepted logs, each exit 0 without warnings/errors and all gates within
{propext, Quot.sound}:

- `/private/tmp/ym-channel-square-credit-20261004-6.log`: six printed gates.
  SHA256 `b7a3870620f13e980b08cee4f9118408d92f3a193cdcfbbdde8051c14928b0d4`.
- `/private/tmp/ym-channel-paid-square-20261004-1.log`: three printed gates.
  SHA256 `a65531529758cfc025cc2643008162e7fd5c3ab6e89e0caf247fd3d56e3a888f`.

Final source SHA256:

- `BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean`:
  `9d59c76735933f8b169b5410a72d67e64552acf51d6e528134688fdbdfa1eaa8`.
- `BF4ExactSlabFixedSpatialFamilyChannelPaidSquare.lean`:
  `800e041318f4e3c39c7d453b3ee87d57739e8e8f23390dd6338b01c0955d4774`.

Earlier failed elaborations are rejected evidence. Scoped opacity fixes
required no heartbeat increase or unsafe reducibility. Final checks used ONE
monitored 20-GiB worker and a 12-GiB reserve, with fresh process/pressure/swap
preflights; swap was zero. Frozen source and logs passed independent review.
No new sorry, axiom, Classical/native_decide/noncomputable declaration,
analytic field or weakened frontier. Root import registration is NOT root
verification. No full/root build, full audit, guard or broad metrics run;
CI remains off. No ASCII or paper-list reprint.
