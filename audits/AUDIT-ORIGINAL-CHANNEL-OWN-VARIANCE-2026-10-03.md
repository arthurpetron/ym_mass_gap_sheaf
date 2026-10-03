# Complete original channel increment versus OWN interacting variance

The whole-project goal remains OPEN: nontrivial continuum Yang--Mills on
R^4 for every compact simple group, SAME-theory QFT axioms and a finite
positive physical mass gap. This checkpoint proves finite SU(2) estimates,
not the missing filtered changing-family rate or continuum construction.

## Mathematical increment

Keep T=P M_V and ell(p)=H_N[V*p], with the original spatial factor V once
in ell and unchanged inside T. The actual selected-link heat form is
positive semidefinite and preserves the constant vector. Its constructed
Gram identity and Cauchy--Schwarz imply, for every supported signed h,

    ell(h)^2 <= ell(h*T h).

This statement needs only w>=0 and arbitrary finite cutoff K. The actual
active-block range and Nodup guards are proved, not new hypotheses. No
positive source, stationary law or pointwise channel sign is assumed.

For the original padded-square trace f, take g=g_n and
psi=oddCentered(f) at the OWN odd-marginal mean at depth n. Put

    Z=oddMass_n, v=oddVariance_n(f),
    J=ell((g*psi)*T(g*psi)), L=ell(g*psi),
    I=squareChannelIncrement_n, B=exactChannelHeatCost_n.

The existing centered identity is E+J=Z*v and the exact channel identity
is 4E+I=2B. Combining them gives the new checked OWN-variance identity
and inequality:

    I+4Z*v = 2B+4J,
    2B+4L^2 <= I+4Z*v.

The latter retains a favorable, actually computed correction rather than
discarding J as merely nonnegative. OWN centering is NOT an assertion
L=0: the centering density is V*g_n*g_(n+1), not V*g_n. Neither raw
channel moments nor channel-centered laws are substituted for v.

## Exact source anchors

All paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
|---|---|---|
| `transferStep_quadratic_ge_mean_square` | `BF4DyadicWilsonSquareChannelOwnVariance.lean:65` | Constructed actual original mean-square floor. |
| `paddedSquare_channel_ownVariance_identity` | `BF4DyadicWilsonSquareChannelOwnVariance.lean:103` | Exact complete increment versus SAME OWN variance and original transfer quadratic. |
| `paddedSquare_channel_ownVariance_lower` | `BF4DyadicWilsonSquareChannelOwnVariance.lean:128` | Actual retained-square lower estimate, with no new analytic premise. |
| `original_quadratic_pin` | `BF4ExactSlabFixedSpatialTransferPositive.lean:56` | Same original transfer identified with selected-product heat. |
| `channelMeanSquares_pin` | `SU2QuaternionProductHeatChannelMeanGram.lean:78` | Exact kinetic-form Gram pin. |
| `channelMeanSquares_ge_haar_square` | `SU2QuaternionProductHeatChannelMeanGram.lean:108` | Constructive constant-vector test. |
| `activeBlocks_lt` | `BF4ExactSlabFixedSpatialKineticMarginals.lean:86` | Actual link range guard. |
| `activeBlocks_nodup` | `BF4ExactSlabFixedSpatialKineticMarginals.lean:92` | Actual distinct selected links. |
| `centered_transfer_quadratic_pin` | `BF4ExactSlabFixedSpatialCenteredTransferReserve.lean:65` | Existing E+J=Z*v at the actual OWN center. |
| `paddedSquare_channel_exact_cost` | `BF4DyadicWilsonSquareChannelExactResponse.lean:181` | Existing complete nonperturbative 4E+I=2B. |

The square results retain 0<w<1, headCutoff(w)<=K, K>=2, arbitrary depth,
and side(scale)<width. All parameter guards remain in their types.

## Forward/backward boundary

This supplies the finite comparison previously derived only in
`audits/MATH-NOTE-CHANNEL-RELATIVE-FRONTIER-2026-10-03.md`, now with a
retained mean-square correction. It is a constant-one energy ceiling;
the theorem does not establish an O(1/side) rate, a quantitative lower
fraction of J, or the filtered norm required by the scaling consumer.
The exact J identity is retained so subsequent estimates need not restrict
themselves to its constant mode.

The actual unmet input is still s*D<=C*Z1*ell(b*b) on a JUSTIFIED changing
family, with A=g_(n+t), b=T^t(g_n*(f-c_n)), and the chronological center
at n. Existing completed pins are `originalOwnBlockVariance_converges`
and `originalOwnBlockCost_converges` in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136,157`.
An existing literal finite-budget necessary-rate consumer is
`originalOwnBlock_budget_rate_constraint` in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredRateConstraint.lean:131`.
The existing relative-budget-to-macro implication is the private
`response_anchor_bridge` in
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedAnchorContinuity.lean:175`.
At start=m=side>=4C, it gives kappa_C*R(side)<=R(2*side), without an
independent positive floor on the shrinking response. These are existing
source-reviewed consumers, not additional new verification targets.
No additional conditional survival wrapper was added.

## Verification boundary

One accepted focused check exited zero with one worker, a 20 GiB worker
ceiling, 12 GiB OS reserve and the monitored launcher. Live preflight
found no competing compiler/runner and no swap. The accepted log has
exactly three printed gates, each using only {propext, Quot.sound}, and
no error, warning or sorryAx. No heartbeat/resource increase.

Target: `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelOwnVariance.lean`.
Accepted log: `/tmp/ym-original-channel-own-variance-20261003-b.log`.

Source SHA256:

    db80cad21c5d73806748286e4aa0c7e52258d55036cee8ce76dbb4d77e0b8362

Accepted-log SHA256:

    4e4cd2dcad3d8b836ef0a647e64664e088c6acca591a7a89642d51b113ba4cf0

The first check failed on the local projection notation precheck; it is
NOT accepted proof evidence. The only retry correction was the existing
`quotPrecheck false` notation pattern, with no mathematical statement change.
Independent source and accepted-log reviews checked the original objects,
guards, hashes and gates. No sorry, axiom, classical shortcut, surrogate
or frontier weakening was introduced. Root import registration only;
no aggregate build/full audit/broad guard. Canonical ASCII block and CI
are unchanged. Scaling, canonical OS, continuum survival, physical
calibration, full QFT, every-group construction and Clay remain OPEN.
