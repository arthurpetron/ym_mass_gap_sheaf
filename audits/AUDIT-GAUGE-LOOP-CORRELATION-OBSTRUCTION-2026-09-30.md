# Gauge-invariant loops do not repair the shared-factor-only budget

Date: 2026-09-30 UTC. Three focused targets passed all 24 public axiom gates
within {propext, Quot.sound}. This is a finite three-path heat-law result,
not an original full-slab bound or a Yang--Mills counterexample.

## Exact construction and proof

Use three path holonomies with the same two endpoints: C, A, B, in blocks
0, 1, 2. The weight is the COMPLETE finite relative heat packet of A/B,
independent of C. The two tests are the closed-loop scalars C*A^-1 and
C*B^-1 (half the fundamental trace). All original packet spins through K
are retained. No numerical truncation of this finite packet is performed.

| Claim | Declaration and source |
| --- | --- |
| Actual weight and two loop tests | `weight`, `leftLoop`, `rightLoop`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:47` |
| Lifted weight is the A/B relative packet, up to explicit padding | `weight_pair_pin`, `lean/YMGap/Continuum/SU2QuaternionGaugeLoopCorrelationObstruction.lean:49` |
| The pin holds beneath every supported three-block insertion, with both support premises constructed | `weight_pair_haar`, `lean/YMGap/Continuum/SU2QuaternionGaugeLoopCorrelationObstruction.lean:70` |
| Two common endpoint gauges cancel in each closed loop | `parallel_loop_gauge_scalar`, `lean/YMGap/Continuum/SU2QuaternionParallelLoopGauge.lean:42` |
| Both literal moment tests use those SAME endpoint gauges | `loops_gauge_invariant`, `lean/YMGap/Continuum/SU2QuaternionGaugeLoopCorrelationObstruction.lean:77` |
| Every character of the A/B heat weight has the same invariance | `heat_character_gauge_invariant`, `lean/YMGap/Continuum/SU2QuaternionGaugeLoopCorrelationObstruction.lean:90` |
| Exact conditional integration over common C | `integrate_common`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:53` |
| Mixed C integral is one quarter of the A/B relative scalar | `mixed_partial`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:82` |
| Relative scalar has heat expectation w^3 | `relative_scalar_moment`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:102` |
| Weight mass is one | `mass`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:129` |
| Both means are zero | `left_mean`, `right_mean`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:132`, `:137` |
| Both variances are 1/4 | `left_variance`, `right_variance`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:157`, `:161` |
| Covariance is w^3/4, for every K>=1 | `covariance`, `lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:165` |
| A symmetric correlation bound must have rho>=w^3 | `coefficient_lower_bound`, `lean/YMGap/Continuum/SU2QuaternionGaugeLoopCorrelationObstruction.lean:125` |
| Positive weight at w=7/8 and the explicit late cutoff | `testWeightCertificate`, `lean/YMGap/Continuum/SU2QuaternionGaugeLoopCorrelationObstruction.lean:135` |
| That bound cannot satisfy degree*rho<1 for degree>=2 | `test_degree_budget_obstruction`, `lean/YMGap/Continuum/SU2QuaternionGaugeLoopCorrelationObstruction.lean:142` |

The calculation is short mathematically: integrate the common path, retaining
the two interacting holonomies, then use the already-proved full-packet
fundamental transmission. Haar-unit norms give the diagonal moments. Endpoint
gauge cancellation proves that the tests are closed loops, not disguised
non-invariant open-coordinate tests. The norm assumptions on endpoint gauges
are explicit arbitrary-insertion Haar-carrier hypotheses in the gauge lemmas.

## What this eliminates, and what it does not

It eliminates a universal shared-heat-only symmetric correlation estimate
with the stated degree budget, EVEN after restricting its test pair to these
gauge-invariant closed loops. The earlier coordinate obstruction did not
establish that invariant-test version. Gauge-sector preservation is therefore
not itself a repair of this factor-only quantitative route.

The three-path graph is not the full four-dimensional slab action. The new
theorems neither identify these loops with its auxiliary recurrence states,
nor remove its one-sided action factors, nor bound its prediction covariance.
They do not refute an original-action invariant-sector estimate, collective
signed control, physical mass, continuum Yang--Mills or the Clay target.

NEXT quantitative work must retain the original one-sided factors and actual
normalizer, or use a collective signed estimate. The existing sufficient
consumer remains `residual_pair_lower_of_prediction_bound` at
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionAngle.lean:53`; its useful
original-action bound on justified scaling is still missing. A fixed
dimensionless gap is not being imposed as a necessary physical condition.

## Parallel Ward-route source review (not a new proof)

`totalScore_cost_le` at
`lean/YMGap/Continuum/BF4ExactSlabWardFamilyCost.lean:115` requires each test
to be local to its selected link's star; its factor 25 follows from deleting
off-star score pairings under that hypothesis. The restriction is on the
score tests, not on the signed observable paired against the total score.

The actual recurrence DOES have growing-cone locality:
`coupled_second_succ_localized` at
`lean/YMGap/Continuum/BF4ExactSlabChebyshevAuxiliaryCone.lean:67`,
and literal local representatives `firstRep`/`auxiliaryRep` in
`lean/YMGap/Continuum/BF4ExactSlabLocalCauchyCone.lean:109` and
`lean/YMGap/Continuum/BF4ExactSlabLocalCauchyCone.lean:148` (using the
`LocalRep` type in `BF4ExactSlabLocalCauchyRepresentative.lean`).
`auxiliary_coercivity` at
`lean/YMGap/Continuum/BF4ExactSlabLocalAuxiliaryCoercivity.lean:74`
already consumes that route. Growing-cone locality is not fixed-star
locality or a uniform angular-derivative cap. The gauge-preservation
checkpoint supplies neither of the latter properties.

The Ward angular energy and conditional residual-generator energy are
distinct existing forms. No new comparison or useful lower response is
proved here. Applying the factor-25 theorem to arbitrary auxiliary gradient
tests without its locality premise is not justified by the current review.

## Verification and unchanged frontier

The safe launcher checked `SU2QuaternionParallelLoopGauge` (3 gates),
`SU2QuaternionSharedHeatLoopMoments` (14), and
`SU2QuaternionGaugeLoopCorrelationObstruction` (7), one worker at a time,
with the 20 GiB worker cap and continuous memory telemetry. Every final check
exited successfully. No new sorry, axiom, classical/noncomputable declaration,
analytic bundle or weakened frontier was introduced. No full root build,
full-tree build, audit, guard or progress-metric run was performed.
Sol reviewed the mathematical normalization and supplied the generic loop
gauge proof; Luna independently reviewed positivity, normalization, same-loop
joins and the bounded scope. The Ward review was corrected to include the
existing growing-cone locality results before recording its conclusions.

The canonical chart is unchanged: its broader A03 estimate remains open,
as do justified scaling/nontrivial survival, thermodynamic control and
same-theory OS/QFT/physical mass/every-group requirements.
