# Original growing-square spectator channels and signed geometric budget

Date: 2026-09-24 UTC. Scope: finite original-Haar SU(2) identities and
source-dependent bounds for the literal growing square. The constructive
continuum Yang--Mills / physical mass-gap goal for every compact simple
gauge group remains OPEN.

## Mathematical increment

Let L=2^scale, with strict spatial padding L<width. The active block list is
computed from the actual ordered square word; its complement is the spectator
list S. Let q be the ORIGINAL fringe-projected terminal endpoint source.
For each computed Gram channel (weight c, polynomial h) of the spectator
heat, define q_h = familyProject S (q*h). All spectator heat remains in these
weights and sources. No source is declared to be a probability law.

The ORIGINAL terminal energy is exactly

    E = sum_h weight(h) * sourceEnergy(fullHeat, q_h, f).

The same decomposition preserves arbitrary supported spectator/fringe-
independent insertions in the ORIGINAL odd marginal. In each channel, the
remaining heat can be restricted to the actual active blocks. In particular,

    oddMass = sum_h weight(h) * H[q_h * P_active(q_h)].

This is NOT sum_h weight(h)*H[q_h^2]. Original centering must use the one
aggregate mean; no channelwise recentering or partition substitution is made.

Set

    A = sum_h weight(h) * H[q_h^2],
    M = sum_h weight(h) * H[q_h^2*f^2],
    D_ch = sum_h weight(h) * sourceIncrementCost(fullHeat,q_h,f),
    a = w^(12*L), b = w^(32*L).

A is definitionally the existing familyChannelQuadratic with spectator list
S and ORIGINAL projected source q. At every rational w and K>=2, the two
proved square heat images give the exact identity

    4*E + D_ch = 2*((1-2*a+b)*M + (1-b)*A).

D_ch is the correction for these computed channels, not an asserted alias
of the preceding unchannelized sourceIncrementCost. Neither A nor M is
identified with its preceding raw-source counterpart.

For w>=0, a constructed Haar-unit certificate for the actual Wilson word
gives the sharp fundamental square cap four. Inserting each actual supported
channel-source square and summing with the computed nonnegative channel
weights proves A>=0 and 4*A-M>=0, without any cutoff positivity premise.

For 0<=w<=1 and K>=2, the existing scalar curvature estimate at u=w^L
therefore supplies the new concrete cancellation-preserving bound

    4*E + D_ch <= 2*(8*(1-u)*(4*A-M) + 960*(1-u)^2*A).

The signed correction is retained, not assumed nonnegative or dropped.
The two power implementations used by the heat-image and scalar-budget
modules are explicitly proved equal before applying the power-of-power law.

## Declaration evidence

| Declaration | Source | Content |
|---|---|---|
| `BF4DyadicWilsonSquareChannelPartition.loopSlots_length` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelPartition.lean:53` | Ordered actual slot list has length 4*L. |
| `BF4DyadicWilsonSquareChannelPartition.spectator_observable_cover` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelPartition.lean:86` | Computed disjoint full-carrier partition. |
| `BF4DyadicWilsonSquareChannelPartition.sourceCharacter_spectator_independent_allSpin` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelPartition.lean:121` | Actual word character is independent of all complementary blocks. |
| `BF4DyadicWilsonSquarePassiveChannels.squareChannelSource_supported` | `lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:68` | Computed channel sources stay on the same carrier. |
| `BF4DyadicWilsonSquarePassiveChannels.paddedSquare_energy_eq_channels` | `lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:109` | Exact ORIGINAL energy with all spectator heat retained. |
| `BF4DyadicWilsonSquarePassiveChannels.oddMoment_eq_active_square_channels` | `lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:173` | Same arbitrary insertion and original marginal; active heat only after proved independence. |
| `BF4DyadicWilsonSquarePassiveChannels.oddMass_eq_active_square_channels` | `lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:190` | Original mass equals active heat moments, not raw squares. |
| `BF4DyadicWilsonSquareChannelCost.paddedSquare_terminal_channel_cost` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelCost.lean:135` | Exact signed aggregate 4E+D_ch, with existing familyChannelQuadratic. |
| `BF4DyadicWilsonSquareChannelGeometry.paddedSquareSquareBound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:99` | Constructed cap-four certificate on actual square. |
| `BF4DyadicWilsonSquareChannelGeometry.squareChannelMass_nonnegative` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:201` | Actual conditional channel quadratic is nonnegative. |
| `BF4DyadicWilsonSquareChannelGeometry.squareChannelMoment_le_four_mass` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:220` | Actual weighted square insertion is at most 4*A. |
| `BF4DyadicWilsonSquareChannelGeometry.squareChannelGeometricCost_nonnegative` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:245` | Actual geometric defect 4*A-M is nonnegative. |
| `BF4DyadicWilsonSquareChannelBudget.collected_cost_le` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelBudget.lean:57` | Cancellation-preserving scalar budget at u=w^L. |
| `BF4DyadicWilsonSquareChannelBudget.paddedSquare_terminal_signed_geometric_budget` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelBudget.lean:98` | Concrete ORIGINAL energy budget with all channel premises constructed. |

## Remaining causal work

The useful SAME interacting centered-variance comparison along a justified
changing-scale family remains OPEN. Control the complete signed budget,
or the actual A and 4*A-M aggregates sufficiently sharply, relative to the
original normalization and centered vector norm. In particular, the
existing plaquette channel first-moment/heat-floor comparison is not already
a normalized growing-loop estimate. Bare product heat remains distinct from
the interacting completed transfer. No completed scaling improvement,
continuum survival, cross-width identification, physical Hamiltonian/mass,
full QFT/YM/UV or all-group conclusion follows from this milestone.

## Verification

Five final serialized narrow checks exited zero, with 31 printed gates within
{propext, Quot.sound}. All use `scripts/safe_lean_build.py --jobs 1 --check`
with explicit output olean, a 2 GiB worker cap, default elaboration limits and
the unchanged 12 GiB OS reserve. No full-root/tree build, axiom audit, guard
or progress suite was run. Initial failed drafts are not accepted evidence.
The first budget launch was refused below the 12 GiB reserve. Compilation
paused; fresh memory/process checks preceded resumption under the same
thresholds. Missing namespace/type wrappers and an explicit rational-power
recoding were repaired. A typed channel-sum target avoided an unfolding
timeout at the unchanged default heartbeat limit. No source hole, new axiom,
analytic premise or canonical-field change was introduced. Independent
source/scope review found no mathematical blocker.

| Final local log | Gates | SHA-256 |
|---|---:|---|
| `/tmp/ym-gap-dyadic-square-channel-partition-check-2.log` | 13 | `2459ab9fcd0f54563fb15a1db1f9061228c5b15cd47945237fcad48a378e27d0` |
| `/tmp/ym-gap-dyadic-square-passive-channels-check-1.log` | 8 | `915da2bbd308527cd391c7f8855e7616aa52094ed8c85043cd05ee660ba0d68d` |
| `/tmp/ym-gap-dyadic-square-channel-cost-check-2.log` | 1 | `7cf17dc60cc4d162a5a615891a4c807c0cf6f23a811756760c9539ab8e437a71` |
| `/tmp/ym-gap-dyadic-square-channel-geometry-check-3.log` | 7 | `d88fa3c1ad62efa942963351de9e6796074208928a1e5dae60ced3a53252f43c` |
| `/tmp/ym-gap-dyadic-square-channel-budget-check-3.log` | 2 | `bbcfa7c0664351fd9e8e94aa1c2fa6be1d4d64eda7003898e20d824a48a5f525` |

The semantic root imports the new budget, with the preceding heat-image
consumer retained transitively. Schema 1 snapshot 20 records partial A03
evidence only. The exact canonical chart block, symbols, labels, layout,
permanent scope registry and every goal-node marker remain unchanged.
