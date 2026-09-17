# Actual product-kinetic strict contraction and the surviving spatial action

Date: 2026-09-17 UTC. Base revision: `889c75d`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4 for
every compact simple gauge group, with the required same-theory QFT structure
and positive physical Hamiltonian gap, within the constructive axiom gate
{propext, Quot.sound}. The whole-project goal remains OPEN.

## Mathematical result

`lean/YMGap/Continuum/SU2QuaternionProductHeatTensorization.lean:152`,
`kineticMap_centered_square_bound`, proves for the ORIGINAL kinetic map K:

    H[f] = 0  ==>  H[(K f)^2] <= (1-headFloor(w))^2 H[f^2].

This holds for every supported polynomial, every original spatial width
(including zero), every rational 0<w<1 and every representation cutoff
Kcut>=headCutoff(w). The squared rate is independent of width, degree and
late cutoff, but explicitly depends on w. Strictness is the existing
`squaredHeatRate_lt_one`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatContraction.lean:104`.
No coupling/spacing-uniform physical margin is asserted.

The actual list of paired temporal links is used, not a replacement
character-diagonal space. `activeBlocks_nodup` and the literal
`kineticWeight_eq_indexedProduct` are at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:92`
and `:118`. Unselected fringe links are integrated against Haar; they are
not identity channels.

## Causal proof and equality levels

1. `independent_iff_degree_zero`,
   `lean/YMGap/Continuum/SU2QuaternionHaarBlockConditionalAlgebra.lean:137`,
   connects the concrete block mask to the exact zero-degree condition
   used by the original heat-vacuum theorem. This module also proves
   coefficientwise conditional-integration algebra, without a mixing input.
2. `productHeat_upper_marginal` and `productHeat_lower_marginal`,
   `lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:226` and
   `:236`, prove both unit marginals on every supported endpoint polynomial
   for a valid NODUP active list. These identities hold at every rational
   w and every cutoff; positivity guards enter only the norm bound.
3. `head_removal` and `cross_orthogonal`, same file `:338` and `:388`,
   remove a selected factor on the projected input and prove orthogonality
   of projected and fluctuating outputs. Head removal is SupportedHaarEqv,
   not a false free-polynomial coefficient identity. The output polynomial
   is independent of an unselected coordinate by
   `productMap_independent_of_not_mem`, same file `:306`.
4. `productMap_conditional_pair_bound`,
   `lean/YMGap/Continuum/SU2QuaternionProductHeatContraction.lean:171`,
   uses the constructed positive residual

       R = (heat_i - headFloor(w)) * productHeat(rest).

   EVERY remaining heat factor stays present. The exact marginals of both
   the full and rest kernels give the two residual diagonals
   (1-headFloor)*H[f^2] and (1-headFloor)*H[g^2].
   `removed_pair_zero`, same file `:151`, kills the removed cross pairing
   by actual conditional centering and independence of the whole remaining
   kernel times the lifted test. Weighted Cauchy--Schwarz then gives the
   squared one-link rate. `productMap_conditional_square_bound`, same file
   `:230`, tests against the SAME output and treats zero norm constructively.
5. `productMap_square_split` and `productMap_centered_square_bound`,
   `lean/YMGap/Continuum/SU2QuaternionProductHeatTensorization.lean:80`
   and `:115`, use exact output orthogonality and input Pythagoras in a
   finite induction. The rate appears once, not once per link. Its private
   `square_congr` at `:51` tests supported-Haar equality against both
   supported outputs; it does not upgrade that equality to coefficientwise
   equality. The base case uses `productMap_nil`,
   `lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:84`, which
   returns the original total Haar mean.

This proof eliminates the previously planned sequential coordinate-map
recoding construction as an unnecessary route to this kinetic theorem.
It introduces no unsupplied analytic assumption.

## Actual original-action consumer

Let V be the full original spatial weight, m(f)=H[V f], and
F=m(g)f-m(f)g. In
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredKineticBound.lean`:

- `centeredInput` at `:49` constructs F without division.
- `centeredInput_weighted_mean_zero` at `:73` proves H[V F]=0.
- `transferStep_centeredInput` at `:86` pins T F to m(g)T f-m(f)T g,
  using the two ORIGINAL input masses, not recomputed output masses.
- `centered_transfer_square_bound` at `:96` proves

      H[(m(g)T f-m(f)T g)^2] <= squaredHeatRate(w) H[(V F)^2].

The literal T=K(V f) is the existing `transferStep_kineticMap`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticContraction.lean:72`.
No spatial factor is discarded. The displayed right-hand side retains V
twice after squaring. No positive mass or reciprocal is required, and g
need not be positive. This weighted centering is NOT identified with the
stationary physical OS vacuum projection.

## Remaining direction and audit boundaries

The strict pure-kinetic task is now closed. Spatial-action cancellation
and its comparison with the SAME physical OS norm remain open. Generic
product-kernel inequalities do not supply non-abelian mass generation.
In particular this result does not repair the excluded guard in the older
interacting small-nome estimate or prove a changing-scale physical gap.

The next existing signed consumer is `response_identity`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:90`:

    C_(S+a) Z_S^2 - C_S Z_(S+a)^2 = response_S.

`finite_response_bound`, same file `:209`, consumes a bound with the exact
denominator. The updated plan seeks a bound for the ACTUAL spatial-face
response, summable over the required faces with parameter dependence
explicit. It does not assume such coefficients have been supplied. Both
original partitions and signed cancellations must survive. The existing
original-action comparison consumer remains `insertion_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean:86`.

Physical time/mass calibration, same-theory continuum QFT construction,
and every compact simple group remain open. No canonical frontier atom,
old analytic guard or frontier statement changes in this increment.

## Verification

Five final focused checks pass, each serialized through the monitored
launcher with one worker and a 20 GiB ceiling after process/swap preflights.
All 46 public axiom gates are within {propext, Quot.sound}; productHeat is
axiom-free. Final logs contain no errors or warnings. No sorry, new axiom,
classical shortcut or machine-safety relaxation was introduced. A scalar
normalizer timeout was repaired by factoring the generic rational identity
before instantiating physical masses, not by raising limits.

Parallel source review checked the full residual, supported-Haar transport,
original index specialization and parameter scope. The root import list was
updated; root/full-tree/full audit/guard were NOT run. CI remains manual-only.
No competing Lean/Lake/pytest/runner was observed. Preflight swap ranged
from 6797.19 MiB to 6789.19 MiB without growth.

Final log SHA-256:

- `/tmp/ym-haar-conditional-algebra-20260917.log`:
  `92165b3d38a32c6b1588d486b1b8519aa49e55c26f150d1c1fbecebd727aa66e`.
- `/tmp/ym-product-heat-marginals-20260917.log`:
  `1d01da2f7cd4da27eda52f62a45dfe28f07f659b90844b0e46eca7d3630538ed`.
- `/tmp/ym-product-heat-contraction-20260917.log`:
  `a7d6cc753b14550338c5d3801c5e971a6b67060f9409118f58c29e21e1572da4`.
- `/tmp/ym-product-heat-tensorization-20260917.log`:
  `6bf045b7d6e0fd39d5e8778ff37642cc507ba2a67a404fa309ee3cb3eff6cb4a`.
- `/tmp/ym-centered-kinetic-bound-20260917.log`:
  `7c3329b8bdc57e465a49dac403e04a3474e13c77495db27232381685dd8e9010`.
