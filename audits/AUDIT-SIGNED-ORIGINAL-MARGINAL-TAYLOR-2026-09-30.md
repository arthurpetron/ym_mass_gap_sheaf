# Signed-family Taylor identity in the original odd marginal

Date: 2026-09-30. Scope: the original finite-cutoff, finite-width,
finite-terminal-depth SU(2) transfer with arbitrary signed padded plaquette
families. This is an exact identity, not a scaling estimate or Clay closure.

## Corrected source review

The preceding `AUDIT-SIGNED-ANGULAR-ORIGINAL-WEIGHT-SEAM-2026-09-30.md`
overlooked existing `energy_projected_source` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialProjectedSourceEnergy.lean:102`
and `energy_taylor_angular` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceTaylor.lean:132`.
They already pin the Taylor formula to ORIGINAL energy for fringe-independent
observables and q=P_fringe(V*g). Those joins need not be reconstructed.
The leading q^2 weight is not the odd marginal without a signed correction.
This milestone supplies that correction and the actual normalized family join.

## Checked increment

Let g=g_n be the original terminal message, V the original spatial weight,
q=P_fringe(V*g), P the full-product heat map after exact inactive integration,
W=V*g_n*g_(n+1), Z the original odd-chain mass, and Gamma_i(f) the six-plane
angular square in original block i. Then

    A_square = sum_i H[q^2 Gamma_i(f)]
    A_odd    = sum_i H[W Gamma_i(f)]
    D        = sum_i H[q*(Pq-q)*Gamma_i(f)]
    A_square + D = A_odd.

Evidence: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAngularMarginal.lean:104`,
`angular_weight_identity`; definitions `marginalAngular`, line 51, and
`angularWeightDefect`, line 56; original moment join `angular_moment_pin`,
line 65. No invariant-source equation or sign for D is assumed.

Formal zero derivatives can retain zero-coefficient terms. Thus inactive
blocks use coefficientwise zero, not an invalid syntactic independence claim:
`lean/YMGap/Continuum/SU2QuaternionAngularSquareLocality.lean:78`,
`blockAngularSquare_zero`. Distinct blocks use actual syntactic independence:
`blockAngularSquare_independent_of_ne`, line 57.

For h=1-w, the pre-existing Taylor formula consequently becomes

    E/Z = h*(A_odd/Z) + R_effective/Z,
    R_effective = R_mixed - R_diagonal - h*D.

Evidence: `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMarginalTaylor.lean:64`,
`signedRemainder`; line 71, `energy_taylor_marginal`; line 107,
`normalizedEnergy_taylor`. Definitions at lines 97 and 102,
`normalizedAngular` and `normalizedRemainder`, use the SAME positive
`oddMass`, not a new q^2 partition. The effective remainder is NOT asserted
to be O(h^2); its weight correction still needs control, and q varies with
w, cutoff, width and terminal depth.

The whole signed family, including arbitrary coefficients and repeated faces,
has proved fringe independence after strict padding:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyFringeIndependent.lean:30`,
`spatialSpan_fringe_independent_after_padding`.
`MarginalTaylor.padded_family_normalized_taylor`, line 127, consumes it with
no extra analytic premise. `finite_family_increment_taylor`, line 141,
pins the result to the EXISTING `originalWindowScalar`, with the unchanged
cutoff `headCutoff(w)+stage`, terminal depth and partition. All signed cross
terms remain. The squared increment is twice E, NOT the norm square of v-Tv.

## Verification boundary

Four final focused checks exited 0 via the monitored launcher, one worker,
20 GiB ceiling, 12 GiB reserve, live telemetry and 300-second status setting.
Preflight found no competing compiler/test/runner and zero swap use. No
safety limits changed. Sol supplied the two locality helpers; the main
agent serialized every compiler run.
Sol also independently reviewed the final signs, normalization and complete
signed-family window pin; no mathematical scope issue was found.

All 15 printed gates report exactly `{propext, Quot.sound}`. No new sorry,
axiom, classical dependency, native decision procedure or canonical-field
change. No full-tree/root build, audit or guard. Root imports were registered
after focused verification without recompiling the large root file.

| Final log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-angular-square-locality-20260930.log` | `3dee8602e666251bd80e3fb83266c2a6f5f981e5bfc7ef40226116ca34bba0ca` |
| `ym-family-fringe-independent-20260930.log` | `055dfb169b0304b0302e2394352315be9f669a900eb9e60dba4f335c1ab9a713` |
| `ym-angular-marginal-20260930.log` | `f97b9816832f4bbb86027c53c06fdcaf43bba9f7557fe4e362d1b1fbae2f23fa` |
| `ym-marginal-taylor-20260930.log` | `d0b3a71fdab9554ddb67a44de5d1943edd864307745c47b9893d7979041eba74` |

## Remaining mathematics

Control the leading ORIGINAL marginal angular term together with the effective
signed remainder relative to the SAME centered interacting variance on one
justified scaling family. Existing centered Ward identities retain complete-
weight derivatives; those signed terms may not be discarded. Do not return
to a separately normalized q^2 variance or bound every term absolutely before
examining cancellation. No physical spacing law, scaling survival, uniform
every-state decay, physical OS identification, continuum QFT, every-group
result or Clay theorem is supplied. The canonical chart is unchanged.
