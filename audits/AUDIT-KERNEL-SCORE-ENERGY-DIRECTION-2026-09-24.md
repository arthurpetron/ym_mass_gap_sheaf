# Kernel-score response is not an upper temporal-energy estimate

Date: 2026-09-24 UTC. Constructive finite SU(2) result, not Clay closure.

## Outcome and route decision

The preceding whole-product score/variance theorem is valid. A universal
reverse domination of temporal energy by its one-end score responses is not:
the actual one-link product heat with flat positive source has ZERO such
responses in every angular direction and POSITIVE normalized jump energy.
The example satisfies the score theorem's late-cutoff guard at every strict
nome. Park this reverse-domination route; work directly on the full signed
temporal form relative to the same actual variance.

This is not a counterexample to Yang--Mills, to an estimate specific to a
physical Wilson source, or to a direct coefficient-square energy bound. The
probe is a coordinate on one link, not a claimed physical closed Wilson loop.

## New exact source identity

For W=`productHeat n w K ids`, R=a(x)*a(y), lower supported f, and the
actual signed angular direction D,

```
H_2n[R*(D_y W)*f(x)] = -B(D a, a*f),
B(u,v) = H_n[u*P(v)].
```

`productHeat_lower_score_eq_source_pair` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatScoreSource.lean:47` proves
this by signed Haar integration by parts, the actual `upperDirection_source`
identity, and `productMap_pairing`. There is no source positivity, spectral,
or large-cutoff hypothesis; support and the valid selected-list interface
are retained. For a=1, `signedAngularDirection_one` at the same file's line 36
gives D a=0. Hence `productHeat_flat_lower_score_zero` at line 88 proves
vanishing for every supported lower test and every finite signed direction.

## Guarded positive-energy witness

The following declarations are in
`lean/YMGap/Continuum/SU2QuaternionProductHeatScoreEnergyObstruction.lean`:

| Declaration | Line | Content |
| --- | --- | --- |
| `probe` | 46 | Nonconstant coordinate x_0. |
| `sourcePair` | 47 | Both flat endpoint sources, 1*lift(1). |
| `kernel` | 48 | Actual one-link `productHeat 1 w K [0]`. |
| `mass` | 49 | The same H_2[R W]. |
| `jumpEnergy` | 51 | H_2[R W*(f(x)-f(y))^2]. |
| `score` | 54 | H_2[R*(D_y W)*f(x)] for the whole supplied direction. |
| `bare_jump_square` | 74 | Before inserting W, the original Haar square is exactly 1/2. |
| `mass_positive` | 79 | Actual edge mass is strictly positive at the displayed guard. |
| `jumpEnergy_positive` | 93 | Actual jump energy is strictly positive at the same guard. |
| `score_zero` | 112 | Every angular direction gives zero one-end response. |
| `normalized_score_energy_domination_false` | 118 | No scalar B bounds normalized jump energy by B times the squared normalized score. |

The common guard is `0<w<1` and `relativeCutoff w 32 <= K`.
Both positivity results follow from the constructed heat floor and an actual
Haar square; no scalar positivity premise is supplied. The normalized
refutation uses r=1/mass with that proved positivity:

```
0 < r*jumpEnergy,
r*score = 0,
not (r*jumpEnergy <= B*((r*score)*(r*score)))   for every rational B.
```

There is no low-cutoff escape: for example w=1/2 and its computed
`relativeCutoff w 32` meet the guards, as do all larger cutoffs. The result
does not rely on evaluating that cutoff numerically.

## Actual downstream consumer and remaining input

The required survival input is a sufficiently small upper one-step loss
relative to the SAME centered variance, for an explicitly justified
changing-spatial/coupling/spacing observable family. The existing whole-test
lag theorem is `BF4WilsonTimeZeroMomentConvexity.timeIncrement_linear` in
`lean/YMGap/Continuum/BF4WilsonTimeZeroMomentConvexity.lean:185`; the signed-pair
consumer `combinedTimeIncrement_linear` is at
`lean/YMGap/Continuum/BF4WilsonSignedPairTimeControl.lean:106`.
Neither produces the missing small relative one-step input.

Concrete inputs still available:

- `link_displacement_bound` at
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonKineticIncrement.lean:90`
  controls a single actual active-link displacement with both terminal sources.
- `word_increment_bound` at the same file's line 178 uses a literal ordered-word
  telescope and finite Cauchy. Its path-length-square bound is not a uniform
  operator bound for a growing family of different words.
- `full_jump_pairing` at
  `lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:245`
  identifies the whole mixed temporal form without discarding cross terms.
- `family_joint_variance_floor` at
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean:136`
  supplies a fixed-nome actual centered norm floor; its near-one calibration
  must not be assumed adequate.
- `energy_eq_bare_add_correction` at
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`
  keeps the finite-P source correction explicit. It has no sign conclusion.

Next evaluate a direct cancellation-preserving bound for the full temporal
Gram form versus the actual covariance form. A useful occurrence-Gram bound
or a proved same-source conditional tensorization is a possible sufficient
producer, not an established theorem or a newly assumed field. Bounded link
overlap alone supplies no cross-link orthogonality. Do not replace the target
by the easy coefficient-1 stability bound or another scalar response bound.

Spatial/scaling passage, nontrivial continuum survival, physical time and
generator calibration, finite positive physical mass, full same-theory QFT/YM
fields, every compact simple group, and the Clay target remain OPEN.

## Verification

Two focused serialized checks, one worker with an 8 GiB ceiling through
`scripts/safe_lean_build.py`, completed with exit status zero:

```
/tmp/ym-gap-product-score-source-check-1.log
/tmp/ym-gap-product-score-energy-obstruction-check-2.log
```

Eight printed gates contain only {propext, Quot.sound}; no error, warning,
`sorryAx`, or `Classical.choice` in the accepted logs. No new hole or axiom,
canonical field change, or physical/continuum closure. The semantic import
was added, but no full-root build/audit/guard or progress-metric run was made.
Sol drafted the general source identity and reviewed the direction issue;
Luna independently checked the consumer and diagnostic scope. Root proved
the guarded normalized obstruction, checked both modules, and repointed the
live plan without changing the whole-project goal.
