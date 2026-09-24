# Derivative-free geometric budget for the original plaquette energy

2026-09-24 UTC. A quantitative finite original-action estimate, not the
missing interacting-variance comparison or a continuum gap.

## Objects and exact statement

Use the actual spatial face with strict padding, its fundamental character f,
and the COMPLETE projected source q=P_fringe(V*g_n), where g_n is the original
terminal message. H is the original base-link product Haar functional. Define

    eps = 1-w,
    A = H[q^2],    F = H[q^2*f^2],    C = 4*A-F = H[q^2*(4-f^2)].

The new strongest bound is

    4*E_original + D <= 2*(8*eps*C + 960*eps^2*A).

It holds for every finite cutoff K>=2, every 0<=w<=1, every terminal depth n,
and every actual spatial face embedded with strict padding into the width.
It retains the exact source-increment correction D; its nonnegativity is NOT
asserted throughout this closed nome interval at arbitrary cutoff.

Under 0<w<1 and the additional computed headCutoff(w)<=K guard, the existing
positive-heat theorem allows D to be discarded, giving

    2*E_original <= 8*eps*C + 960*eps^2*A.

Both statements use the ORIGINAL energy, not a heat-bath gap, a surrogate
variance, or a replacement stationary source.

## Short mathematical argument

The checked actual heat images previously gave

    J = (1-w^32)*A + (1+w^32-2*w^12)*F,    4E+D=2J.

Set theta=2*w^12-1-w^32 and gamma=5-8*w^12+3*w^32. Then

    J = theta*C + gamma*A,
    3*theta = 2*(1-w^12)-gamma.

The existing curvature theorem proves 0<=gamma<=960*eps^2, and the elementary
power bound gives 1-w^12<=12*eps. Thus theta<=8*eps. The actual plaquette
square-cap certificate gives C>=0 under the full q-squared insertion; A>=0
is a Haar square. These two facts justify the coefficient inequalities even
when theta is negative. No derivative, degree/Casimir bound, positivity of q,
or eigenvector premise is used in the signed estimate.

## Declaration map

| Declaration | Source | Claim |
|---|---|---|
| `theta_le_eight_margin` | `lean/YMGap/Continuum/SU2HeatPlaquetteGeometricBudget.lean:46` | Signed linear coefficient bounded by 8eps on the closed nome interval. |
| `plaquette_geometric_cost_le` | `lean/YMGap/Continuum/SU2HeatPlaquetteGeometricBudget.lean:106` | Scalar cost bound given A>=0 and 4A-F>=0. |
| `rawSourceMass_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.lean:58` | Nonnegative raw source mass for every supported source. |
| `geometricSourceCost_eq_haar_gap` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.lean:68` | Exact Haar representation C=H[q^2*(4-f^2)]. |
| `geometricSourceCost_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.lean:96` | Actual plaquette square certificate supplies C>=0. |
| `plaquetteChannelCost_collected` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSourceGeometry.lean:106` | Exact original channel-cost algebra. |
| `plaquetteChannelCost_le_geometricBudget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.lean:57` | Applies the scalar bound with both hypotheses proved. |
| `padded_terminal_plaquette_signed_geometric_budget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.lean:77` | ORIGINAL energy consumer retaining D and complete q. |
| `padded_terminal_plaquette_energy_geometric_budget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.lean:96` | Positive-heat corollary, with both cutoff guards explicit. |

## Dependence and open comparison

The constants 8 and 960 do not depend on width, depth or cutoff. The nome
margin is EXPLICIT. A and C, however, depend on the complete source and hence
on nome, cutoff, depth and width. This is not a bound uniform in those
parameters on the normalized energy. In particular H[q^2] is not H[q*P(q)],
and C is not an interacting centered variance.

The geometric factor retains vanishing at f=2 and f=-2 instead of replacing
it by an absolute cap. No concentration estimate for the original source at
these values, no comparison with its original partition, and no normalized
changing-scale smallness follows here. The bound is not asserted uniformly
sharper than every preceding estimate. The remaining A03 task is useful
control of the complete signed budget relative to SAME interacting variance
on ONE justified changing-scale family, or direct response control.

## Verification

Three narrow serialized checks passed at a 2 GiB worker ceiling, unchanged
12 GiB host reserve, and default elaboration limits. All 13 printed gates
report only {propext, Quot.sound}; final logs contain no error or warning.

- `/tmp/ym-gap-plaquette-geometric-scalar-check-1.log`: 2 gates.
- `/tmp/ym-gap-plaquette-source-geometry-check-2.log`: 7 gates.
- `/tmp/ym-gap-original-source-geometric-budget-check-2.log`: 4 gates.

Initial missing namespace references were repaired; the original-consumer
draft's resulting timeout was resolved without raising limits. There was no
safety interruption in this turn. Independent read-only review checked the
coefficient signs, nonduplication and open variance boundary separately from
these compiler checks. No new hole, axiom, analytic premise or canonical-field
change. Semantic import added; full-root/full-tree build, audit, guard and
progress script NOT run. No canonical chart node is marked complete by this
partial A03 result. All continuum/Clay obligations remain open.
