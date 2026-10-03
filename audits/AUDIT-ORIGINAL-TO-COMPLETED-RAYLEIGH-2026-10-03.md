# Original Rayleigh numerator and variance meet the SAME completed response

The whole-project continuum Yang--Mills/Clay target remains OPEN. This
checkpoint closes a fixed-parameter finite-to-completed identification,
not the signed relative estimate or a continuum construction.

## Checked mathematical increment

Keep the original transfer T=P_w M_V, g_n=T^n 1 and ell(p)=H[V*p].
The loop is the literal padded dyadic square, f its fundamental character,
and c_n=middleRatio(n+1,n,f) its ACTUAL finite odd-window mean. Set

    A=g_(n+t), b=T^t(g_n*(f-c_n)),
    Z0=ell(A^2), Z1=ell(A*T A),
    D=Z1*ell(b^2)-Z0*ell(b*T b).

Both Z0 and Z1 are constructed positive under the unchanged late-cutoff
guard. They are DISTINCT original chronological partitions. The earlier
block/window identities now have literal finite scalar consumers:

    originalOwnBlockVariance = ell(b^2)/Z0 = Q_(2t),
    originalOwnBlockCost = D/(Z0*Z1) = Q_(2t)-Q_(2t+1).

Each Q uses the SAME c_n at both endpoints and both lags. No finite
stationary vacuum or bare-heat eigenvalue is substituted.

Let J_L be the EXISTING lower-first originalJointLimit of
`.mul (.loop 0 loop 1) (.loop L loop 1)`, x the existing literal loopState,
mu=intrinsicForm(x,unit), N the existing dyadicOriginalNorm, alpha the
existing dyadicNormalizer, and R_L the existing dyadicUnitResponse. The
new completed pins prove

    centeredTimeMoment_L(x,x) = J_L-mu^2,
    R_L = alpha*(alpha*(J_L-mu^2)),
    N*R_L = J_L-mu^2,
    N*(R_L-R_J) = J_L-J_J.

These equalities are CReal.Equiv. The normalizer is cleared by its existing
constructive normalization theorem, not a new norm-floor hypothesis.

The finite OWN-centered difference also receives Type-level QCauchy data.
At delta=epsilon/4 its explicit M is

    max(max(jointModulus_L(delta),jointModulus_J(delta)),
        geometricCutoff(mixRate(w,width),(2*polynomialCap(f))^2,delta)).

Two raw-pair quarter errors and two mean-correction quarter errors pay the
whole epsilon. The rational-embedded diagonal converges to J_L-J_J, with
no additional limit object.

The denominator is checked separately: the OWN mean equals the lower
endpoint mean at lag one, by actual transfer symmetry. Every endpoint
mean approaches the SAME zero-window singleton limit. A maximum of its
existing joint modulus and the mean-error geometric cutoff is the computed
endpoint convergence threshold. Expanding Q_L=P_L-2*c_n*M_L+c_n^2 BEFORE
taking limits proves Q_L converges to the EXISTING centeredTimeMoment.

Thus, on the literal diagonal K=headCutoff(w)+k, n=k,

    originalOwnBlockCost_k --> N*(R_(2t)-R_(2t+1)),
    originalOwnBlockVariance_k --> N*R_(2t).

These are ConvergesTo statements on the original finite scalars. Nome,
width, dyadic scale and t remain FIXED. At an even dyadic side s and
t=s/2 the lags are s and s+1; side=1 is not silently identified with 2t.

## Declaration-to-source map

Names are local to the namespace matching each filename under YMGap.Continuum.
Every row has an accepted printed axiom gate.

| Declaration | Source | Role |
| --- | --- | --- |
| `centeredTimeMoment_chronological_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicChronologicalResponse.lean:67` | Actual lower-first original source minus the SAME mean square. |
| `dyadicUnitResponse_chronological_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicChronologicalResponse.lean:96` | Retains the existing normalizer twice. |
| `dyadicUnitResponse_cleared_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicChronologicalResponse.lean:118` | N times actual response equals the original centered moment. |
| `dyadicUnitResponse_difference_cleared_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicChronologicalResponse.lean:126` | SAME mean square cancels exactly across lags. |
| `ownCenteredLagDifference` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy.lean:74` | Literal finite moving-OWN-center stream. |
| `ownCenteredLagDifferenceCauchy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy.lean:140` | Explicit Type-level diagonal modulus. |
| `ownCenteredLagDifference_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy.lean:184` | Converges to the two EXISTING raw limits' difference. |
| `endpointMean_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:84` | Every fixed lag mean reaches the SAME singleton. |
| `ownMean_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:135` | Actual odd-window mean, not a supplied mean. |
| `own_centeredPair_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonOwnCenterLimit.lean:159` | Denominator-side centered pair reaches the SAME completed centered moment. |
| `originalOwnBlockVariance` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93` | Literal ell(b^2)/Z0. |
| `originalOwnBlockCost` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:98` | Literal D/(Z0*Z1). |
| `originalOwnBlockVariance_converges` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136` | Original finite denominator reaches N*R_(2t). |
| `originalOwnBlockCost_converges` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157` | Original finite numerator reaches N*(R_(2t)-R_(2t+1)). |

## Open analytic input and direction

The unpaid finite target is STILL

    s*D <= usefulConstant*Z1*ell(b^2)

on the actual growing square and a JUSTIFIED changing coupling/width family.
The corresponding completed target is

    s*N*(R_s-R_(s+1)) <= usefulConstant*N*R_s.

Neither inequality is proved here. No favorable sign of the combined source
cost, relative comparison with the half-smoothed response, cross-scale
comparison, spacing calibration, full QFT or every-group theorem is supplied.
All limit thresholds retain their fixed parameters; they are not a family-wide
uniformity claim. No new analytic hypothesis bundle is introduced.

The bounded parallel review found only an unsigned squared covariance bound
in `paddedSquare_own_commutatorGain_local_radial_bound`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainRadialCost.lean:258`.
The original full-source gradient is an identity with its mean residue in
`paddedSquare_commutatorGain_source_gradient`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainStein.lean:141`.
Neither statement is the missing signed relative producer.

The canonical AF scalar trajectory is defined in
`canonicalAFGeometricScalarTrajectory`,
`lean/YMGap/Continuum/BF4PhysicalCanonicalAFDynamicFamilyCompiler.lean:171`;
its family compiler still accepts `CanonicalAFGeometricLocalProducer`
as input (`:181`). Actual Wilson family sampling likewise accepts its nome
and width schedules and assumes the cross-sample inequalities in
`sample_table_tail_compare`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicResponseSampling.lean:196`.
These interfaces are not a constructed physical Wilson trajectory.

FORWARD: retain the combined SIGNED original energy/commutator and compare
it with ell(b^2). BACKWARD: use the actual normalized macroscopic-response
criterion, with the SAME response now pinned on both sides. The analytic
producer and justified family, not further normalization wrappers, are NEXT.

## Verification

Four accepted serialized monitored source checks passed 14 unique printed
gates, all within {propext, Quot.sound}, with zero errors/warnings. Fresh
preflights showed 86% free memory and zero swap. Each check used one worker,
12 GiB reserve and the unchanged 20 GiB worker cap. Preliminary failures were
notation, namespace, parameter-inclusion and explicit scalar-unfolding issues;
they are not accepted proof evidence. No limit or axiom ceiling was raised.

No sorry, axiom, classical shortcut, native_decide, guard weakening, CI change
or trusted external computation was added. Independent source/mathematical
review passed. Root imports are registered only, NOT aggregate-checked; no
full build or full axiom audit ran. No exact canonical chart node changed.

Accepted source and log SHA-256 pairs:

| Module stem | Source SHA-256 | Accepted log / SHA-256 |
| --- | --- | --- |
| `BF4WilsonAllNomeDyadicChronologicalResponse` | `ddb491b0e8aff198a1021e141d13e2f6c8eb89041cc6df09d0fa4c8920bd149e` | `/tmp/ym-dyadic-chronological-response-20261003-c.log` / `aa111c53bab0b32a119d76006028dce8a56df9be61bf309364b88b728a336d70` |
| `BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy` | `040eaf42851f1eab1b84c02bbc5d8dffd2653ec4cb2d42aa90f2c71d016c1f93` | `/tmp/ym-moving-center-lag-cauchy-20261003-a.log` / `ea94b099c03a36cfa10baec1fb6c68765005bdabe93ffe02450b24bdda36a923` |
| `BF4ExactSlabFixedSpatialWilsonOwnCenterLimit` | `8307e0284f265053e7638b7f6f5f8dbddd31fdf3c43772fab06e36a03bb425e2` | `/tmp/ym-own-center-limit-20261003-c.log` / `33e6fd35c784aa36068617dc9d4229d69f6879b816ad0adf443d7f378cf13d8e` |
| `BF4WilsonAllNomeDyadicOriginalRayleighLimit` | `cc4e387b51929dfd2e29cdc408cd1fcb8d70fae38bf1b8444973090ca9cb0957` | `/tmp/ym-dyadic-original-rayleigh-limit-20261003-e.log` / `d3420ba7a37a6187a5819679c291be272ffd7b0cf1041d56e838804386ecc0b0` |
