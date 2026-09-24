# Active Casimir-square contraction and the remaining second-moment join

2026-09-24 UTC. Follows `1c646d6` (exact spectator-remainder contraction).
The continuum Yang--Mills / Clay target remains OPEN.

## Checked quantitative result

Write H for the original finite product-Haar functional and
`C_A p = sum_(i in A) -Delta_i p` for the literal positive angular Casimir.
For the actual spectator heat channels `(lambda_c,h_c)`, set
`b_c=P_S(u*h_c)`, with the COMPLETE original source u. Then

    sum_c lambda_c H[(C_A b_c)^2] <= H[(C_A u)^2].

The derivative commutes through the conditional projection and each channel
multiplier because A and S are disjoint. One family-Bessel application to
the COMPLETE polynomial C_A u retains all inter-block and inter-plane cross
terms. No triangle inequality, channel-count factor or number-of-blocks
factor is introduced. The coefficient is exactly one.

Blockwise integration by parts and constructive polarization identify the
computed first-Casimir pairing with the literal operator. In particular, for
the original full cyclic differential sweep C_sweep,

    H[(C_sweep p)^2] = H[(C_all p)^2].

For p independent of S and a covering partition S++A, the latter is exactly
H[(C_A p)^2]. Consequently the ACTUAL computed sweep-square budget satisfies

    sum_c lambda_c H[(C_sweep b_c)^2] <= H[(C_A u)^2].

An S-independent insertion r is retained in every channel:

    sum_c lambda_c H[(C_sweep (b_c*r))^2] <= H[(C_A (u*r))^2].

These statements require finite support, distinct valid spectator slots,
disjointness and the stated covering partition. They allow every finite K
and `0<=w<=1`. The source, channel data and right side still depend on the
original coupling, cutoff, width and terminal depth. H is raw Haar, not the
interacting normalized variance. C_sweep is an auxiliary link differential
operator, NOT the physical Hamiltonian or the completed OS transfer.

## Separately checked remainder estimate -- do not join silently

Let M2(p) denote the actual computed full-path sum

    leafSum tail (tail+1) p p (fun ds => totalCasimir ds * totalCasimir ds).

Nonnegative full-path pairings and the scalar remainder inequality give

    R(p,p) <= (1-w)^2 * M2(p),

for `0<=w<1` and the explicit `sufficientCutoff w<=K` guard. Omitted modes
are retained; no cutoff-dominates-source-degree assumption is added.

**OPEN JOIN:** `M2(p) = H[(C_sweep p)^2]` is NOT proved in this checkpoint.
The first-moment identity and positivity alone do not establish it. In
particular, this checkpoint does NOT claim
`R(p,p) <= (1-w)^2*H[(C_sweep p)^2]`.

The next concrete route uses the actual character kernels, not an assumed
commuting projector family. Checked ingredients now include the selected
endpoint character Casimir eigenaction, independent-factor differentiation,
Casimir commutation with exact head integration, valid-path kernel pairing
and ragged-tree reassembly. The full product/path eigenaction and its
second-moment consumer remain to be composed and checked.

Even that join would not prove useful SAME-variance control along changing
scales. The complete signed remainder combination, ONE surviving excitation,
the separate EVERY-vector scaling gap, controlled SAME continuum limits,
full Hilbert/OS/QFT/local YM/UV identification, physical Hamiltonian mass and
EVERY compact simple group remain OPEN. No canonical frontier field changes.

## Declaration map

Paths below are under `lean/YMGap/Continuum/`.

| Module:line | Declaration | Checked content |
| --- | --- | --- |
| `SU2QuaternionChannelCasimirSquare.lean:199` | `activeCasimir_channelSource` | Complete literal Casimir pulls through the actual channel. |
| `SU2QuaternionChannelCasimirSquare.lean:233` | `channelSource_activeCasimir_square_le` | Coefficient-one complete-square contraction. |
| `SU2QuaternionChannelCasimirLocality.lean:112` | `activeCasimirPolynomial_range_eq_active` | Passive independence removes only passive derivatives. |
| `SU2QuaternionLiteralCasimirPairing.lean:211` | `pairCasimir_eq_literal` | Arbitrary supported signed test; constructive polarization. |
| `SU2QuaternionLiteralCasimirPairing.lean:300` | `casimirSweep_square_eq_literal` | Computed sweep square equals the literal full square. |
| `SU2QuaternionLiteralCasimirPairing.lean:326` | `casimirSweep_square_eq_active` | Exact active reduction for a passive-independent source. |
| `SU2QuaternionPassiveChannelCasimirSquare.lean:49` | `channelSource_casimirSweep_square_le` | Actual computed channel-sweep consumer. |
| `SU2QuaternionPassiveChannelCasimirSquare.lean:101` | `channelSource_mul_casimirSweep_square_le` | Consumer retaining an independent insertion. |
| `SU2QuaternionDiagonalRemainderMoment.lean:110` | `exactRemainderPair_diagonal_le_squareMoment` | Remainder bounded by the PATH second moment, not yet a differential norm. |
| `SU2QuaternionRelativeCharacterCasimir.lean:69` | `normalizedCharacterAt_zero_one_angularCasimir` | Exact head-character eigenaction. |
| `SU2QuaternionSelectedCharacterEigenaction.lean:96` | `normalizedCharacterAt_blockAngularLaplacian` | Exact selected first-endpoint eigenaction. |
| `SU2QuaternionCharacterCasimirLocality.lean:77` | `blockAngularLaplacian_mul_independent` | Differentiate only the dependent factor. |
| `SU2QuaternionCyclicPathReassembly.lean:71` | `full_path_pairing_kernel` | Original valid path equals its doubled-character pairing. |
| `SU2QuaternionCasimirHeadIntegration.lean:75` | `activeCasimirPolynomial_partialHaarHeads` | Complete differential sum commutes with exact input integration. |

## Verification boundary

Final checks used `python3 scripts/safe_lean_build.py --jobs 1 --check`,
matching `.olean` outputs and `--check-worker-limit-gib 4`. No concurrent
build, safety-limit change, new axiom, analytic premise or source `sorry`.

| Target suffix | Accepted log in `/tmp/` | Printed gates |
| --- | --- | --- |
| `SU2QuaternionDiagonalRemainderMoment` | `ym-gap-diagonal-remainder-moment-check-3.log` | 3 |
| `SU2QuaternionChannelCasimirSquare` | `ym-gap-channel-casimir-square-check-3.log` | 6 |
| `SU2QuaternionChannelCasimirLocality` | `ym-gap-channel-casimir-locality-check-3.log` | 5 |
| `SU2QuaternionLiteralCasimirPairing` | `ym-gap-literal-casimir-pairing-check-4.log` | 7 |
| `SU2QuaternionPassiveChannelCasimirSquare` | `ym-gap-passive-channel-casimir-square-check-2.log` | 2 |
| `SU2QuaternionRelativeCharacterCasimir` | `ym-gap-relative-character-casimir-check-5.log` | 3 |
| `SU2QuaternionSelectedCharacterCasimir` | `ym-gap-selected-character-casimir-check-3.log` | 3 |
| `SU2QuaternionSelectedCharacterEigenaction` | `ym-gap-selected-character-eigenaction-check-4.log` | 1 |
| `SU2QuaternionCharacterCasimirLocality` | `ym-gap-character-casimir-locality-check-1.log` | 2 |
| `SU2QuaternionCyclicDiagonalRemainder` | `ym-gap-path-character-public-check-1.log` | 6 existing proofs, one newly public |
| `SU2QuaternionCyclicPathReassembly` | `ym-gap-cyclic-path-reassembly-check-2.log` | 3 |
| `SU2QuaternionCasimirHeadIntegration` | `ym-gap-casimir-head-integration-check-2.log` | 2 |

All 43 printed gates stay within `{propext, Quot.sound}`; accepted logs
contain no error, warning or sorryAx. Failed draft checks are not proof
evidence. One local theorem uses 400000 heartbeats after an explicit
negation/scalar orientation repair; worker memory and safety limits did not
change. There was no safety interruption in this increment.

Semantic imports were added for the checked modules. No full-root
build/audit/guard/progress-metric run was performed. Independent Sol review
confirmed cross-term retention and the still-open second-moment equality.
