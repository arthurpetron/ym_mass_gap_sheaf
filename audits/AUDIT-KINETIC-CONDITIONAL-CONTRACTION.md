# Actual kinetic contraction and the conditional tensorization inputs

Date: 2026-09-17 UTC. Base revision: `50a2190`.
Whole-project goal: construct continuum Yang--Mills on R^4 for every compact
simple group, with the required same-theory QFT structure and positive
physical Hamiltonian gap, constructively within {propext, Quot.sound}.
That goal remains OPEN.

Successor checkpoint: `AUDIT-PRODUCT-HEAT-TENSORIZATION.md` closes the
strict pure-kinetic join listed below and records its original weighted
transfer consumer. This report preserves the earlier verification boundary.

## Proved on the original kinetic layer

All Lean paths below are relative to `lean/YMGap/Continuum/`.

- `BF4ExactSlabFixedSpatialKineticMarginals.lean:83`, `activeBlocks`, and
  `:92`, `activeBlocks_nodup`, give the actual selected link list and its
  distinctness, not an assumed bijection with all source links.
- Same file `:118`, `kineticWeight_eq_indexedProduct`, is a literal equality
  with the original product of heat kernels between i and N+i. It retains
  every packet coefficient and original factor ordering.
- Same file `:198`, `kineticWeight_upper_marginal`, and `:211`,
  `kineticWeight_lower_marginal`, give exact unit marginals for every
  supported endpoint polynomial, at every rational nome and cutoff.
  The empty active list is handled by the empty-product branch. Unused
  fringe links remain normalized Haar variables.
- `BF4ExactSlabFixedSpatialKineticContraction.lean:46`, `kineticMap`, is
  the actual partial integration of kineticWeight times the original input.
  `kineticMap_mean` at `:55` preserves its Haar mean.
- Same file `:62`, `kineticMap_square_contraction`, gives
  H[(K f)^2] <= H[f^2], for every spatial width, all 0<w<1 and every
  Kcut>=headCutoff(w). The numerical bound one has no width or nome penalty;
  its positivity threshold still depends on w. This is nonexpansivity,
  not a strict centered bound or a theorem computing the exact operator norm.
- Same file `:72`, `transferStep_kineticMap`, is the exact original identity
  T f=K(V f). At `:76`, `transferStep_square_le_spatialSquare` proves
  H[(T f)^2] <= H[(V f)^2]. Every original spatial interaction remains.
  This removes the kinetic cap from the prior ordinary-Haar estimate in
  `BF4ExactSlabFixedSpatialTransferBound.lean:93`, `transferStep_square_bound`;
  it does not bound the spatial potential uniformly or identify an OS norm.

## Proved local strict estimate with every spectator retained

`SU2QuaternionHaarBlockProjection.lean` uses the original coefficientwise
block integration, not a diagonal-character carrier:

- `project` at `:44`, `fluctuation` at `:47` construct P_b f and f-P_b f.
- `project_idempotent` at `:115` and `project_comm` at `:132` hold
  coefficientwise, not merely after total integration.
- `fluctuation_orthogonal` at `:211` and `square_decomposition` at `:240`
  prove orthogonality and H[f^2]=H[(P_b f)^2]+H[(f-P_b f)^2].
- `partialHaarHead_fluctuation_zero` at `:198` supplies exact conditional
  centering in the ordered-head convention; `fluctuation_head_output_independent`
  at `:91` preserves the unused output coordinate's independence.
- `project_square_contraction` at `:270` supplies actual Haar projection
  nonexpansivity, including the kind needed for unpaired fringe links.

`SU2QuaternionRelativeHeatConditionalContraction.lean:58`, `conditionalHeat`,
integrates only block zero of the actual relative heat packet times f.
The output contains original block one and all original blocks after one.
The input must not depend on the unused output block one; it can share
arbitrary spectator dependence with the output test.

`conditionalHeat_square_contraction` at `:148` gives norm bound one.
`conditionalHeat_centered_square_bound` at `:244` gives squared rate
(1-headFloor(w))^2<1 when the CONDITIONAL head mean is coefficient-zero.
Its `residualCertificate` at `:93` is constructed on the full ambient
carrier. The constant cross term vanishes by conditional Fubini; the two
residual diagonal terms are exactly (1-headFloor(w)) times the original
square norms. No absolute whole-kernel cap appears.

`conditionalHeat_fluctuation_square_bound` at `:271` applies this to the
actual constructed f-P_0 f. No centering witness is left unsupplied.
The strict rate and its proof are the previous `squaredHeatRate` and
`squaredHeatRate_lt_one` in `SU2QuaternionRelativeHeatContraction.lean:83`
and `:104`. The rate is independent of spectator count, polynomial degree
and late cutoff, but depends on w; no positive coupling-uniform margin
is asserted. Global zero mean alone is not conditional zero mean.

## Exact remaining mathematical join

The literal kernel product and conditional strict estimate do not yet prove
a strict norm bound for every globally centered input of the full kinetic
map. Remaining work: identify its sequential local maps under explicit
coordinate recodings; prove the heat/projection commutation preserving
orthogonality; then perform the finite orthogonal product induction,
including unpaired Haar projections. The intended bound uses the ONE-link
rate, rather than multiplying it once per spatial link. This paragraph
states the next proof target, not a proved implication.

Even that pure kinetic theorem would not remove the interacting potential
comparison or supply the physical OS vacuum. Changing-scale spatial control,
physical time/mass calibration, continuum QFT structure and all compact
simple groups remain open. Generic Markov/projection inequalities are not
themselves a non-abelian mass-generation mechanism.

## Verification

Four final focused monitored checks pass. The 44 public axiom gates and
one retained private regression gate depend only on {propext, Quot.sound}.
All final logs have no errors or warnings. Parallel agents supplied the
original index/marginal argument and the conditional projection argument;
the parent supplied the heat contraction and original transfer consumer.
Independent read-only mathematical review found no defect.

The axiom gate caught omega generating Classical.byContradiction for an
impossible zero-block NON-arithmetic goal. The elaborated proof trace located
that dependency; explicit False.elim (Nat.not_lt_zero i hi) removed it.
No classical dependency remains in the final checked results. This was a
development repair, not a relaxed axiom gate or an open analytic premise.

Every compiler launch was serialized with one worker and a 20 GiB ceiling,
after process and swap preflights. No competing compiler/runner/test process
was found; swap stayed at 6797.19 MiB. No safety limit, old guard, canonical
frontier statement, sorry or new axiom changed. Root imports added;
root/full-tree/full audit/guard unrun. CI remains manual-only.

Final log SHA-256:

- `/tmp/ym-haar-block-projection-20260917.log`:
  `879946e0aa3955e35151475cdea2c4710d594fc66a975c1eedb8e3205d74fa89`.
- `/tmp/ym-relative-heat-conditional-contraction-20260917.log`:
  `25406b3ddbe37394ddf3fdbb8934b218ae9dd89db64cb5ce87a2c899f83daec9`.
- `/tmp/ym-fixed-spatial-kinetic-marginals-20260917.log`:
  `5258b9351d8ba6d3b13309b68032b77080841f19d372873e357a1c496dd6b08b`.
- `/tmp/ym-fixed-spatial-kinetic-contraction-20260917.log`:
  `c70fb7b0cc44348e165a58264410c46dd6a93bf894708fcb330567a3111c51c1`.
