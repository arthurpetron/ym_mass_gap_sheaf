# Actual blocked endpoint marginal and remaining signed producer (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms and
a positive physical Hamiltonian mass gap. Continuation of `b883de91`.

## Completed exact join: the actual middle action, not a heat surrogate

Write K01 and K12 for the original kinetic layers, V1 for the original
middle spatial weight, and J for the actual `gluedMiddle`. The outside
endpoint weights V0 and V2 are NOT part of J. For every supported original
slice polynomial p, every rational nome w and finite cutoff K:

```
H_ambient[(E0 p)*J]  =  H_slice[p*(T 1)].
J = integral_middle K01*V1*K12.
```

Here equality means the existing rational equivalence, and T is the
original `transferStep`. No positivity, normalization or late-cutoff guard
is needed. Width<=extent and start+2<=extent are explicit geometry guards.

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGluedEndpointMarginal.lean:79`,
  `placed_image_local`, proves a supported placed polynomial is local to
  its actual embedding image, retaining all source coordinates.
- Same file `:91`, `endpoint_test_gluing`, pulls only the endpoint-local
  test through the actual middle integration. Neither V0 nor V2 is introduced
  or canceled.
- Same file `:105`, `chronological_middle_pairing`, integrates the tested
  three-slice polynomial: lower-slice Fubini, exact upper-endpoint kinetic
  marginal, then kinetic symmetry. V1 occurs exactly ONCE throughout.
- Same file `:145`, `chronological_middle_pin`, places those three factors
  into the original ambient coordinates using the existing chronological
  and pair-carrier pins, with original fringe links retained.
- Same file `:169`, `glued_lower_endpoint_pairing`, composes those checked
  arrows into the displayed actual ambient identity.
- Same file `:218`, `compressed_lower_endpoint_pairing`, transports the SAME
  tested identity to the preexisting compressed boundary kernel. The test
  itself is explicitly compressed; both it and the kernel are reconstructed
  before Haar transport. No consecutive lower/upper ordering is assumed for
  the boundary list.

## A genuine blocked-action heat-only obstruction

At width 2, K=1 and w>0, the original first face P gives

```
H_ambient[(E0 P)*J] = w^12*(alpha+alpha^5/16) > 0,
alpha = 2*w^3.
```

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction.lean:50`,
  `glued_firstFace_exact`; same file `:62`, `glued_firstFace_positive`.
- Same file `:73`, `glued_endpoint_not_free`, excludes equality of these
  actual ambient endpoint tests to the free kinetic vacuum marginal for
  EVERY replacement free nome and cutoff.
- Same file `:91`, `compressed_endpoint_not_free`, proves the identical
  obstruction on the actual compressed boundary kernel and compressed test.
- Exact witness input:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.lean:91`,
  `tested_original_one_exact`; `:99`, `tested_original_one_positive`; `:126`,
  `original_one_not_free`.

Scope: unnormalized finite endpoint tests, not positivity of the entire
cutoff-one action, a normalized probability law, or an obstruction to EVERY
interacting coarse action. This supplies the previously missing ambient
join; it does not supply a useful quantitative cross-action estimate.

## Parallel source review: approximation payment versus unpaid bulk

The existing source-relative approximation payment should be reused:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost.lean:246`,
  `original_block_lastStep_correctionPaid_cost_relative_tolerance`, bounds
  the actual cleared cost by the paired bulk plus
  `(zeta+delta+epsilon)*Z1*m(b^2)`, with explicit original-action onsets.
  Here A=T^(n+r+1)1, b=T^(r+1)((T^n1)*psi), Z0=m(A^2), Z1=m(A*T A).
  The three errors are reciprocal correction, terminal drift and source
  reconstruction; no source norm is inverted in the theorem.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131`,
  `clearedRayleighCost`, is `Z1*m(b^2)-Z0*m(b*T b)`. Its normalized error
  after positive Z0*Z1 division is therefore
  `(zeta+delta+epsilon)*m(b^2)/Z0`. This is a one-step Rayleigh pairing cost,
  NOT already the fine two-step squared-norm or cross-action dissipation.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost.lean:165`,
  `originalBlockLastStepPairedBulkBudget`, retains
  `Z0*((1-w)*Lpaired + R(q,q*phi^2)-R(q*phi,q*phi))`.
  Neither the leading paired score nor this SIGNED remainder difference is
  paid by the correction theorem. The action, projected terminal source,
  reciprocal approximation and fringe spatial mass remain explicit.
- `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136`,
  `originalOwnBlockVariance_converges`, pins the actual denominator-side
  variance to Norm*Response(2t). Same file `:157`,
  `originalOwnBlockCost_converges`, pins its cost to
  Norm*(Response(2t)-Response(2t+1)). These are SAME-object scalar pins,
  not all-vector changing-action comparison producers.
- `lean/YMGap/Continuum/BF4WilsonAllNomeSignedMultiplicationLimit.lean:387`,
  `dampedDropLimit_nonpositive`, invokes the EXISTING fixed-parameter
  `mixedMoment_evenTime_geometric` at line 389. Its consumer at `:470`,
  `original_signed_baseline_damping`, is therefore valid fixed-action
  damping, not an independent proof of a useful AF relative-error budget.

Planning consequence, NOT a new checked bound: the constructed numerical
margin (`lean/YMGap/Continuum/BF4WilsonAllNomeRGDissipationBudget.lean:232`,
`relativeRate_margin_lower`) provides a positive tolerance target at each
scale. Approximation tolerances can be chosen against that target without
assuming the missing fine contraction. Separate fixed-parameter onsets
must not be described as a uniform changing-scale diagonal modulus. The
original paired bulk, actual coarse action/map, normalization alignment and
all-vector dissipated-form estimate remain the analytic work.

## Verification boundary

Two serialized final focused checks passed all 6+4 printed new declaration
gates within {propext, Quot.sound}, emitting their local oleans. The existing
heat-only witness dependency was separately checked/cached, with 5 permitted
gates. Independent read-only Sol review confirmed the mathematics, compressed
ordering, geometric guards and exact finite scope.

Final logs, SHA-256:

- `/private/tmp/ym-oct7-glued-endpoint.log`:
  `87bdab651146d3d60e0e964f1fd90a32c7c4bbe1ca98d71fe3504df75916ced1`.
- `/private/tmp/ym-oct7-cube-glued-obstruction.log`:
  `b2ccc6081294dc723460abf71b4e499db0e2fe3c408a8b6b70a95925ff134943`.

One monitored 20-GiB worker and 12-GiB reserve; dynamic capacity checked before
each launch, no competing compiler and zero swap. No new holes, axioms,
classical input, canonical-field changes or raised heartbeats. Initial local
elaboration failures are not evidence. No full-root/tree build or audit,
hashed-baseline regeneration or CI enablement.

NEXT: estimate the combined original signed bulk in useful SAME-form units
and construct the actual interacting comparison, reusing the already-paid
approximation terms and scalar pins. Independent AF survival, useful ordinary
delta budget, physical scaling/volume control, SAME limiting OS/QFT theory,
every group and the Clay target remain OPEN. Broad chart unchanged; no reprint.
