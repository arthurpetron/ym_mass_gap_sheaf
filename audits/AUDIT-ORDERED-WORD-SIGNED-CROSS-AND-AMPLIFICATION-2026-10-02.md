# Original word cross costs and the failed vector amplification

The original Wilson chord now has a linear diagonal cost plus its exact
signed cross cost. That sum reaches the complete filtered OWN-variance
ceiling without changing the source, mean or partitions. The cross cost
is not estimated: a linear TOTAL cost or useful scaling budget is not proved.
An exact one-link counterexample also excludes amplifying scalar kinetic
alignment to arbitrary quaternion-valued sources.

## Ordered word estimate

Keep the existing ordered replacement increments, each with its literal
lower prefix and upper suffix. The squared norm of their sum is the sum
of their norms plus twice the positional pair sum in all four coordinates.
No factors commute, and repetitions are not removed.

`word_norm_cross_expansion`,
`lean/YMGap/Continuum/QuaternionHaarWordSignedCross.lean:123`, proves the
coefficient-level identity. `word_weighted_cross_identity` at line 137
integrates it against the ENTIRE original weight. `terms_diagonal_pin`
at line 154 cancels unit prefixes and suffixes ONLY in diagonal norms.
`word_diagonal_bound` at line 187 charges those diagonals by length times
the literal per-link estimate. No cross term is assigned a sign.

Let X be `normalizedWordCross`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSignedChord.lean:58`.
Its numerator is the actual ordered cross insertion in the ORIGINAL
matched edge density; its denominator is the SAME oddMass.
`matched_word_signed_chord_identity` at line 65 retains the exact
diagonal plus twice that numerator. `matched_word_signed_chord_cleared`
at line 77 and `matched_word_signed_chord_bound` at line 130 give

    matched chord moment <= 6*(1-w)*length + 2*X.

All spatial weights and terminal messages remain. Actual cutoff K>=1,
sufficientCutoff(w)<=K and active physical links are explicit; headCutoff
is separately required for normalization. The old K0+1 kinetic API is
used with K0=K-1 and its equality to K proved.

## Same mixed window and complete signed source

The original cap-four right common-tail comparison carries the ENTIRE
matched estimate, including its signed X, into window(n,1,n+1). With
E the SAME evenPartition, `mixedChordMoment_signed_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredSignedChord.lean:79`, gives

    mixedChordMoment <= [6*(1-w)*length+2*X+8*mixRate^n]*E.

There is no bilinear heat-order comparison between unequal terminal
sources. `mixedChordMoment_signed_tolerance_bound` at line 116 pays only
the boundary error at the EXISTING mixedQuarticDepthCutoff.

Write S for the original filtered numerator, V for OWN oddVariance,
c for its original odd mean, U,Y,D for the existing radial-centered,
Young and drift corrections, and b for the already paid whole-word
quartic rate. `filtered_loop_own_young_signed_chord` at line 138 proves

    t*S+2*t*U+2*Y+2*t*D
      <= 2*E*[t^2*(V+epsilon)+(t+c^2)*b
               +t*(4-c^2)*(6*(1-w)*length+2*X+epsilon)].

The actual c^2<=4 is used before multiplying the chord estimate.
The source, OWN variance and all three corrections remain. The earlier
fully paid length-squared bound remains valid as a separate estimate;
this alternative is not claimed numerically stronger without control of X.
Its quartic cost still carries the explicit length^4 factor.

## Refuted amplification step

For the actual original one-link quaternion u=(a,b,c,d), take
v=(3a,b,c,d). The literal uv has components
(3a^2-b^2-c^2-d^2,4ab,4ac,4ad), each a trace-free degree-two mode.
Both Haar squared norms are three. At EVERY inclusive prefix K>=2,
the exact original heat pairings are 3*w^3 for v and 3*w^8 for uv.

`vectorSource_heat_pin` and `productSource_heat_pin`,
`lean/YMGap/Continuum/SU2QuaternionHeatAlignmentAmplificationObstruction.lean:187`
and line 193, pin those pairings. The supported sources and
arbitrary-retained-boundary transmission theorems precede them.
`quaternion_vector_amplification_fails` at line 217 proves

    pairing(uv) < w^3*pairing(v),  for 0<w<1 and K>=2.

This refutes the proposed quaternion-vector lift of scalar alignment.
It does NOT refute the narrower scalar-source distinct-word target or
the actual positive BF4 terminal source. Scalar alignment cannot be
silently substituted for this false vector statement.

## Verification and next input

Four focused checks exited zero, with 14, 7, 6 and 3 printed gates.
All accepted dependencies are empty or {propext,Quot.sound}; final logs
contain no errors, warnings or sorryAx. Independent mathematical review
and source/log/gate/hash review are recorded with the milestone.
Preliminary failures were a source-path resolution error, namespace opens,
parentheses and an explicit Haar block argument; no statement was weakened.

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionHeatAlignmentAmplificationObstruction.lean` | `dc8e84c76e9e6620ded0f0c256cd9d79ab36f5d821d67f14d94da9486a065891` |
| `/tmp/ym-alignment-amplification-20261002-third.log` | `31b45a275b6a9bfe8215bccd0812766c1edd7674f3919ee89d14e9c5bc56dd7c` |
| `QuaternionHaarWordSignedCross.lean` | `aa157b4d4080ed57ab18108ad881d79c3b3af87bc83c099ffc684e0bcbcb8f3a` |
| `/tmp/ym-word-signed-cross-20261002-fourth.log` | `120c1ff406e0cb9330751b9b97db49065c55742d35791c60151afecc4bd11c48` |
| `BF4ExactSlabFixedSpatialWilsonSignedChord.lean` | `035534e49a6a142067d99bffc478e5eafa2e8c850d39b7758dd62c609c479925` |
| `/tmp/ym-wilson-signed-chord-20261002-first.log` | `428f650f91c0438ca2c162a211e495a23483f21a5d8c6aa6aa0b9db362ac7cf9` |
| `BF4ExactSlabFixedSpatialFilteredSignedChord.lean` | `0fc7192d28529293f07adf7af55fecc67508e53ca6e377d0e8dfdc747a3756f0` |
| `/tmp/ym-filtered-signed-chord-20261002-first.log` | `1ce567b6c48b03bee6f11a32d3af563ae4ad4203ab84e01d28f76b263a4fde70` |

Every launch had a fresh dynamic process/memory preflight, one worker,
a 20-GiB ceiling and a 12-GiB OS reserve. Observed pressure-free capacity
was 83--86 percent, with zero swap. Root imports are registered, NOT
aggregate-checked; root/tree, broad audit/guard and progress metric were
NOT run. No new sorry, axiom, classical shortcut, analytic hypothesis,
frontier field weakening, surrogate source or CI change was introduced.
The documentation skill kept the diagonal and total-cost claims distinct.

NEXT: control the COMPLETE signed source against the SAME connected
lag-one response, or its full retained cross/correction expression,
with a fixed finite relative budget and positive reserve on a justified
changing family. The conditional consumer is
`dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`.
The new cross insertion is computed, not a supplied analytic conclusion.
Spatial/spacing control, continuum survival, physical mass calibration,
full SAME QFT, every compact simple group and Clay remain OPEN.
No exact canonical chart claim changed; no ASCII reprint.
