# Exact spectator-remainder contraction and original-source energy bound

2026-09-24 UTC. Follows `6b607ef` (positive exact remainder and polarized
energy). This closes the finite spectator-remainder contraction proposed in
that checkpoint. The continuum Yang--Mills / Clay target remains OPEN.

## Mathematical result and its guards

Let H be the finite product Haar functional, T the ORIGINAL full-product
finite-cutoff heat map, eps=1-w, and C the cyclic Casimir pairing. Retain

    R(p,p) = H[p*T(p)] - H[p^2] + eps*C(p,p).

Partition the supported coordinate blocks into distinct spectators S and
active blocks A. Use the actual finite heat Gram channels `(lambda_c,h_c)`
and `b_c=P_S(q*h_c)`, with P_S the in-place conditional Haar projection.
Every weight is nonnegative; individual channel sources need not be positive.
Write `C_S(q)=sum_(i in S) H[Gamma_i(q)]`, similarly for A. The new proof uses

    sum_c lambda_c H[b_c*T(b_c)] = H[q*T(q)],
    H[q^2] - sum_c lambda_c H[b_c^2] <= eps*C_S(q),
    sum_c lambda_c C(b_c,b_c) <= C_A(q),
    C(q,q) = C_S(q)+C_A(q).

The first line is EXACT original kinetic recombination, instantiated from
the existing moment identity with insertion one. The other lines now give

    sum_c lambda_c R(b_c,b_c) <= R(q,q).

For an S-independent supported insertion r, projection pull-through gives
the same bound for `b_c*r` against `q*r`. No assumed joint eigenbasis,
commuting spectral projectors or abstract operator-order subtraction is used.
The conditional norm-loss proof iterates actual Cartesian channel lists;
derivative contraction controls the other-block angular terms at each step.

The remainder and norm-loss statements require `0<=w<1` and the explicit
guard `sufficientCutoff w<=K`, with valid finite support and block partition.
The angular channel estimates alone allow `0<=w<=1` and every finite K.
Coefficient one adds no channel-count factor, but q, K, the channels and
the cutoff onset can depend on coupling, width and terminal depth. This is
not a coupling/volume/spacing-uniform interacting-variance estimate.

## Original-action consumer and sign discipline

For the original padded plaquette, q=P_fringe(V*g) with the actual terminal
message g and literal observable f. For every rational s>=0, the consumer is

    2*s*E_original <= 2*s*eps*angular(q,f)
      +s^2*R(q,q)+R(q*f^2,q*f^2)
      -2*s*sum_c lambda_c R(b_c*f,b_c*f).

Only the two POSITIVE channel sums have been contracted. The same upper
bound on the third channel sum would give the WRONG direction after
multiplication by -2*s. It is therefore retained exactly, with its original
weights. No common partition or mean is replaced by channelwise probability
laws. The original action, observable, cutoff, width and depth are preserved.

The global positive diagonals may still contain bulk-source costs. This
upper bound is not asserted numerically sharper than the preceding channel
bound on every input; the earlier signed and fully polarized bounds remain
available. The proof supplies a finite compatibility result, not continuum
survival, an EVERY-vector scaling estimate or a physical Hamiltonian gap.

## Important operator distinction

`SU2QuaternionProductHeatMarginals.productMap` integrates UNSELECTED variables
against Haar; `productMap_nil` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:84` returns the
constant Haar average. It is not the conditional heat map that leaves those
variables shared. Consequently the empty selected list cannot be identified
with the identity on arbitrary supported sources through partial productMap.

`familyChannelQuadratic` instead retains the actual shared-coordinate
conditional channels, including the empty-list norm. The proof never makes
the false partial-product identification. This paragraph records a source
semantic check, not a new kernel-checked counterexample theorem.

## Declaration map

Paths are relative to the repository root.

| Declaration | Source | Content |
| --- | --- | --- |
| `heatChannels_project_square_loss_le_at` | `lean/YMGap/Continuum/SU2QuaternionSelectedHeatGramBessel.lean:359` | Literal selected-link loss, transported through the head swap. |
| `angularListSum` | `lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:53` | Explicit finite angular cost. |
| `angularListSum_append`, `angularListSum_perm`, `angularListSum_range` | `lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:75`, `:82`, `:96` | Exact finite-list algebra. |
| `channelSource_blockAngularSquare_le` | `lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:163` | Full-family derivative contraction outside S. |
| `heatChannels_project_blockAngularSquare_le_at` | `lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:199` | Literal one-link version for the loss induction. |
| `pairCasimir_diagonal_eq_angularListSum` | `lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:236` | Casimir equals the full angular sum. |
| `pairCasimir_eq_angular_partition` | `lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:252` | Exact passive/active splitting. |
| `pairCasimir_channel_le_active` | `lean/YMGap/Continuum/SU2QuaternionChannelAngularContraction.lean:317` | Complete channel Casimir cost is bounded by active cost. |
| `familyChannelQuadratic` | `lean/YMGap/Continuum/SU2QuaternionFamilyChannelLoss.lean:46` | Actual shared-spectator channel square sum. |
| `productChannels_familyProject_loss_le` | `lean/YMGap/Continuum/SU2QuaternionFamilyChannelLoss.lean:219` | Coefficient-one full-family norm loss. |
| `exactRemainderPair_channel_sum_le` | `lean/YMGap/Continuum/SU2QuaternionRemainderChannelContraction.lean:106` | Exact-remainder contraction by recombination plus loss control. |
| `exactRemainderPair_weighted_channel_sum_le` | `lean/YMGap/Continuum/SU2QuaternionRemainderChannelContraction.lean:168` | Independent-insertion consequence. |
| `sourceEnergy_le_angular_add_original_diagonals` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRemainder.lean:187` | Generic signed energy consumer. |
| `padded_plaquette_energy_le_angular_add_original_diagonals` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveChannels.lean:284` | ORIGINAL padded-plaquette consumer. |

## Remaining analytic input and next-action review

The full signed combination and angular cost still need a useful comparison
with SAME centered variance for ONE justified changing-scale observable
family, or a useful direct sampled response. Positive original-source costs
need quantitative control, or negative channel costs need a useful lower or
cancellation estimate. Neither follows from coefficient-one contraction.

A source review also rejects adding a mere exact remainder-defect wrapper as
the next advance. `exactRemainderPair_polarization` in
`lean/YMGap/Continuum/SU2QuaternionExactRemainderEnergy.lean:50`, combined with
`sourceEnergy_eq_polarized_channels` in
`lean/YMGap/Continuum/SU2QuaternionPassiveChannelRemainder.lean:89`, already
returns the original energy after recombination. Repeating that equality
does not estimate it. Channel sources are signed, so positivity of Gram
weights alone does not justify a pointwise positive edge-density argument.
This is an execution review, not an additional proved obstruction theorem.

The separate EVERY-vector spatial/spacing gap, controlled SAME continuum
limits, full Hilbert/OS/QFT and local YM/UV identification, physical-time
Hamiltonian, finite positive physical mass and every compact simple group
remain OPEN. No canonical frontier field was changed or marked closed.

## Verification boundary

Six final serialized monitored checks with one 4 GiB worker returned exit 0:

| Target suffix | Accepted log | Printed gates |
| --- | --- | --- |
| `SU2QuaternionSelectedHeatGramBessel` | `/tmp/ym-gap-selected-channel-loss-check-2.log` | 2, including 1 existing |
| `SU2QuaternionChannelAngularContraction` | `/tmp/ym-gap-channel-angular-contraction-check-4.log` | 9 |
| `SU2QuaternionFamilyChannelLoss` | `/tmp/ym-gap-family-channel-loss-check-2.log` | 2 |
| `SU2QuaternionRemainderChannelContraction` | `/tmp/ym-gap-remainder-channel-contraction-check-1.log` | 2 |
| `SU2QuaternionPassiveChannelRemainder` | `/tmp/ym-gap-contracted-channel-energy-check-1.log` | 4, including 3 existing |
| `BF4ExactSlabFixedSpatialPassiveChannels` | `/tmp/ym-gap-original-diagonal-energy-check-1.log` | 8, including 7 existing |

Each command used `python3 scripts/safe_lean_build.py --jobs 1 --check`
with the named source under `lean/YMGap/Continuum/`, its matching `.olean`
output, `--check-worker-limit-gib 4` and the listed `--log-file`.
All 27 gates (11 existing, 16 new) stay within {propext, Quot.sound}; accepted
logs contain no error, warning or sorryAx. Failed draft checks are not proof
evidence. A scoped source scan found no sorry, new axiom, classical shortcut
or native_decide in the six changed/new proof modules.

No safety interruption occurred in this increment; limits were unchanged,
no concurrent Lean build ran, and no unrelated process was killed. Sol
agents supplied the selected-link, angular and family-loss proofs and the
BF4 consumer; root repaired/integrated them, proved remainder contraction
and the generic energy consumer, and ran serialized verification. Independent
source review checked sign directions and warned against inferring a uniform
numerical improvement. Existing semantic imports cover all three new modules.
No full-root build, full-tree audit, guard or progress-metric run was performed.
No new hole, analytic premise or canonical-field change was introduced.
