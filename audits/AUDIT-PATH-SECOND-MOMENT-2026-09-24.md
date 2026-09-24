# Actual second moment and original active-derivative energy bound

2026-09-24 UTC. Follows `483deca`. The continuum Yang--Mills / Clay target
remains OPEN. The finite second-moment join marked open in the preceding
active-Casimir-square audit is now checked.

## Mathematical result and actual consumer

For the original full cyclic degree-path sum M2 and supported polynomial p,

    M2(p) = H[(C_sweep p)^2] = H[(C_all p)^2].

H is the finite product-Haar functional. C_all is the literal sum of positive
link angular Casimirs; it is NOT the physical Hamiltonian. The proof uses the
actual normalized character kernels: endpoint symmetry gives right-endpoint
eigenaction, disjoint-factor differentiation gives product eigenaction, and
exact input integration gives full-path eigenaction. Integration by parts
moves C to the test. Weighted reassembly stays on the SAME original source
tree and valid-path witnesses. No projector family or joint eigenbasis is
assumed, and all cross terms in the square remain.

Combining with the checked scalar/path remainder bound gives

    R(p,p) <= eps^2 H[(C_sweep p)^2], eps = 1-w,

for 0<=w<1 and sufficientCutoff(w)<=K. This does not require the source degree
to lie below K; the existing omitted-mode remainder is retained.

The complete spectator family, with actual nonnegative weights lambda_c and
b_c=P_S(q*h_c), now satisfies

    sum_c lambda_c R(b_c*r,b_c*r) <= eps^2 H[(C_A(q*r))^2]

for supported q,r, spectator-independent r, and the stated distinct valid
spectator list / disjoint covering partition. The version without r is also
proved. Coefficient-one contraction applies to the complete differential
polynomial, not to separate blocks followed by a triangle inequality.

The ORIGINAL padded-plaquette energy consumes the bound:

    2*s*E_original <= 2*s*eps*angular(q,f)
      + s^2*eps^2 H[(C_A q)^2] + eps^2 H[(C_A(q*f^2))^2]
      - 2*s*sum_c lambda_c R(b_c*f,b_c*f).

Here s>=0; f is the literal plaquette character; q=P_fringe(V*g), with the
original spatial action V and terminal message g. Strict spatial padding
supplies fringe independence; the literal plaquette supplies spectator
independence. The energy equality, common partition, action and source are
unchanged. Only the POSITIVE remainder sums are bounded. The favorable
negative channel sum is retained verbatim. No new analytic hypothesis.

## Declaration map

Paths are under `lean/YMGap/Continuum/`.

| Module:line | Declaration | Content |
| --- | --- | --- |
| `SU2QuaternionCharacterEndpointSymmetry.lean:46` | `normalizedCharacterAt_symm` | Actual endpoint symmetry. |
| `SU2QuaternionCharacterEndpointSymmetry.lean:53` | `normalizedCharacterAt_blockAngularLaplacian_right` | Right-endpoint eigenaction. |
| `SU2QuaternionCharacterProductCasimir.lean:135` | `characterProduct_upperCasimir` | Consecutive product eigenaction. |
| `SU2QuaternionCharacterProductCasimir.lean:226` | `characterProduct_full_upperCasimir` | Full upper range. |
| `SU2QuaternionCyclicPathCasimir.lean:82` | `full_path_activeCasimir_carrier` | Actual full-path eigenaction. |
| `SU2QuaternionCyclicCasimirSquare.lean:70` | `full_squareMoment_eq_literal` | SAME-tree second moment equals literal square. |
| `SU2QuaternionCyclicCasimirSquare.lean:91` | `full_squareMoment_eq_sweep` | Second moment equals computed sweep square. |
| `SU2QuaternionCyclicCasimirSquare.lean:101` | `exactRemainderPair_diagonal_le_sweepSquare` | Differential remainder estimate. |
| `SU2QuaternionPassiveChannelRemainderSobolev.lean:104` | `exactRemainderPair_channel_sum_le_activeCasimir_square` | Complete-channel remainder contraction. |
| `SU2QuaternionPassiveChannelRemainderSobolev.lean:147` | `exactRemainderPair_mul_channel_sum_le_activeCasimir_square` | Independent-insertion consumer. |
| `SU2QuaternionPassiveChannelRemainderSobolev.lean:198` | `sourceEnergy_le_angular_add_activeCasimir_diagonals` | Signed source-energy bound. |
| `BF4ExactSlabFixedSpatialPassiveChannels.lean:338` | `padded_plaquette_energy_le_angular_add_activeCasimir_diagonals` | Original padded-plaquette consumer. |

## Explicit remaining boundary

The source q still depends on coupling, cutoff, width and terminal depth.
H[(C_A q)^2] and H[(C_A(q*f^2))^2] are raw Haar norms of derivatives of that
COMPLETE source, not the SAME interacting centered variance. No uniform
scaling bound or universal improvement over earlier numerical bounds is
claimed. Active differentiation is not source localization.

The next analytic problem is useful control of the complete signed remainder
combination and angular cost relative to SAME variance for ONE justified
changing-scale excitation, or its direct response. A diagonal upper bound
cannot replace the retained negative remainder by a negative Casimir square;
the inequality reverses. Signed mixed-remainder control before domination is
a mathematical target, not a proved theorem in this checkpoint.

ONE surviving excitation and the EVERY-vector scaling gap remain separate
requirements. Controlled SAME continuum limits, full Hilbert/OS/QFT/local
YM/UV, physical-time Hamiltonian and finite positive mass, and EVERY compact
simple group remain OPEN. No canonical frontier field changes.

## Verification

Each accepted check used `scripts/safe_lean_build.py --jobs 1 --check`,
matching `.olean` output, one 4 GiB worker and the unchanged 12 GiB OS reserve.

| Target suffix | Accepted log in `/tmp/` | Printed gates |
| --- | --- | --- |
| `SU2QuaternionCharacterEndpointSymmetry` | `ym-gap-character-endpoint-symmetry-check-1.log` | 2 |
| `SU2QuaternionCharacterProductCasimir` | `ym-gap-character-product-casimir-check-3.log` | 2 |
| `SU2QuaternionCyclicPathCasimir` | `ym-gap-cyclic-path-casimir-check-2.log` | 3 |
| `SU2QuaternionCyclicCasimirSquare` | `ym-gap-cyclic-casimir-square-check-2.log` | 3 |
| `SU2QuaternionPassiveChannelRemainderSobolev` | `ym-gap-passive-channel-remainder-sobolev-check-1.log` | 3 |
| `BF4ExactSlabFixedSpatialPassiveChannels` | `ym-gap-plaquette-active-casimir-check-1.log` | 9 (eight existing) |

All 22 printed gates stay within {propext, Quot.sound}; accepted logs contain
no error, warning or sorryAx. No new source hole, axiom, analytic premise,
safety interruption or raised limit. Existing semantic imports include all
five new modules through the actual BF4 consumer. No full-root build, audit,
guard or progress-metric run. Independent Sol review checked actual-source
preservation, cross terms, signs and the remaining variance/scaling boundary.
