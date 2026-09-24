# Spectator heat retained: geometric energy budget and SAME four-link moments

2026-09-24 UTC. Finite original-action refinement of `12a8294`.
The SAME-variance/scaling comparison and continuum Clay target remain OPEN.

## Mathematical change

Let q=P_fringe(V*g_n) be the complete original endpoint source, f the actual
fundamental plaquette character, and eps=1-w. Retain spectator heat through
its computed positive Gram channels (lambda_c,c). The actual channel source is

    b_c = P_spectator(q*c),
    A_ch = sum_c lambda_c H[b_c^2],
    C_ch = sum_c lambda_c H[b_c^2*(4-f^2)],
    B_ch = 8*eps*C_ch + 960*eps^2*A_ch.

The channel energy identity followed by the geometric Young estimate proves

    4*E_original + D_ch <= 2*B_ch.

D_ch is the weighted sum of the channel source-increment costs. It is NOT
identified with the old global-source increment D. The signed bound requires
0<=w<=1, K>=2, a genuine face, and strict spatial padding. Under 0<w<1 and
headCutoff(w)<=K, the positive-heat version proves

    2*E_original <= B_ch.

The new contraction theorem proves, on 0<=w<=1 at every finite cutoff,

    A_ch <= H[q^2],
    C_ch <= H[q^2*(4-f^2)],
    B_ch <= 8*eps*H[q^2*(4-f^2)] + 960*eps^2*H[q^2].

Thus this is a coefficient-one refinement, not merely a different source
bound. No strict improvement for every source is asserted. The geometric
contraction does NOT subtract two Bessel inequalities: actual plaquette unit
norm writes 4-f^2 as four times the sum of its three nonscalar component
squares under every Haar insertion. Weighted Bessel applies to each square.

## SAME moments and the remaining comparison

For every supported insertion p independent of the fringe and spectators,
the ORIGINAL odd marginal satisfies

    H[marginalWeight*p]
      = sum_c lambda_c sourceMoment(observableBlocks,b_c,p).

This is the SAME identity for partition, mean and second moment; there is no
replacement normalization or channelwise centering. The full heat moment of
each b_c is exactly its observable-block heat moment because both b_c and p
are spectator-independent. For a genuine spatial face,
`observableBlocks.length = 4`, independently of width.

Selected `productMap` is not conditional heat: it Haar-averages unselected
coordinates. The independence proof is essential. In particular the channel
raw moments are NOT identified with `H[q*productMap(spectators,q)*p]`.

The unresolved comparison is now between these channel-aggregated raw moments
and the SAME active-heat, globally centered moments for the actual sources.
The channel sources may be signed, and individual channels are not declared
probability laws. No channelwise variance inequality is assumed. Width, depth,
cutoff and nome dependence remain in sources and weights despite the four-link
operator count. This does not prove a scaling-uniform relative energy bound,
ONE-state survival, or EVERY-state decay after scaling.

## Declaration map

| Declaration | Source | Role |
|---|---|---|
| `plaquetteVector_independent_index` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceIndependence.lean:153` | Public projection of existing component locality; no old statement changed. |
| `observableBlocks_length` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelActiveMoments.lean:61` | Exactly four active slots under genuine-face membership. |
| `plaquetteChannel_moment_active` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelActiveMoments.lean:121` | Full heat equals active heat on each actual projected channel moment. |
| `oddMoment_eq_active_plaquette_channels` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelActiveMoments.lean:146` | ORIGINAL odd-marginal consumer, SAME insertion and normalization. |
| `padded_terminal_plaquette_passive_signed_geometric_budget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveGeometricBudget.lean:164` | Original energy with the distinct channel correction retained. |
| `padded_terminal_plaquette_passive_energy_geometric_budget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPassiveGeometricBudget.lean:203` | Positive-heat energy-only bound with explicit cutoff guards. |
| `channelGeometricCost_le_raw` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelGeometricContraction.lean:225` | Gap-weighted contraction via the three actual vector squares. |
| `channelSourceMass_le_raw` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelGeometricContraction.lean:261` | Companion raw mass contraction. |
| `channelBudget_le_raw` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelGeometricContraction.lean:284` | Complete budget comparison for supported sources. |
| `passiveGeometricBudget_le_original` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChannelGeometricContraction.lean:312` | Actual terminal-source refinement consumer. |

## Verification and scope

Four final narrow serialized checks passed 26 printed gates (including retained
gates in the one changed dependency), all within {propext, Quot.sound}:

- `/tmp/ym-gap-face-vector-independence-check-1.log`: 8 gates.
- `/tmp/ym-gap-channel-active-moments-check-4.log`: 6 gates.
- `/tmp/ym-gap-passive-geometric-budget-check-1.log`: 4 gates.
- `/tmp/ym-gap-channel-geometric-contraction-check-4.log`: 8 gates.

Final logs have no errors or warnings. Draft namespace, coefficient-transport
and channel-sum elaboration errors were repaired without raising limits.
One requested check was refused by the safety reviewer as possibly concurrent;
the preceding session had returned exit 0, and fresh process inspection confirmed
no competing compiler before proceeding. No reserve/pressure cutoff occurred.
Checks used one worker, 2 GiB ceiling, unchanged 12 GiB reserve. Independent
read-only review checked correction identity, moment/normalization, four-block
guard and scope boundaries. No new hole, axiom, analytic premise or canonical
field; no full-root/full-tree build, audit, guard or progress script was run.

The semantic root imports the new leaves. Canonical chart schema 1 is unchanged;
snapshot 4 records partial A03 evidence only. No goal-node status changes.

Next: prove a useful channel-aggregated comparison with SAME centered variance
for ONE justified changing-scale observable family, or its direct response.
The separate EVERY-vector scaling and SAME continuum/QFT/YM/UV, physical
Hamiltonian/mass and every-group requirements all remain OPEN.
