# Positive response on the actual spatial union: corrected analytic frontier

## Completion addendum (2026-09-16)

The geometry, action/probe pins, normalized three-moment comparison and
unchanged-diagonal limit proposed below are now implemented and checked.
`BF4SpatialUnionResponseFiniteComparison.covariance_bound`,
`lean/YMGap/Continuum/BF4SpatialUnionResponseFiniteComparison.lean:110`, proves
the displayed `6*c*c*A*rho^depth` estimate. The computed original-index
threshold is `BF4SpatialUnionPositiveResponse.comparisonModulus`,
`lean/YMGap/Continuum/BF4SpatialUnionPositiveResponse.lean:75`.
`lagThree_floor` and `lagTwo_floor` in the same module at lines 113 and 119
preserve the FULL old floor, not merely its half. The carrier, pairing,
excitation and physical discrete time are the existing union objects.
See [the checked proof and verification record](AUDIT-SPATIAL-UNION-POSITIVE-RESPONSE.md).
The plan below is retained as dated history; its unproved-status statements
describe the earlier checkpoint, not the current response frontier.

## Historical review and proof plan

2026-09-16. Sections 1–4 are a source review and mathematical proof plan, not
new Lean theorems. Section 5 has a focused new Lean implementation checked
by the parent agent: exit 0, all four public gates within `{propext, Quot.sound}`.
This reviewer ran no compiler. The old
full-slab action is not identified with the selected-chain action by definition.

## 1. The physical-time offset matters

For the union's actual centered plaquette excitation `v`, the desired next
fact is a witnessed rational lower bound on `B(v,T_2 v)`. The existing exact
consumer is `BF4SpatialUnionExcitation.excitation_correlator_pin`,
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:69`.

The tempting old source is
`BF4ExactSlabThermodynamicPositiveResponse.original_response_floor`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveResponse.lean:50`.
But its scalar is **not** the union's lag-two scalar. The old lower/upper
plaquette endpoints have separation THREE:

- `BF4ExactSlabShiftedProbeTubeGeometry.lower_shifted_probe_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTubeGeometry.lean:51`;
- `BF4ExactSlabShiftedProbeTubeGeometry.upper_shifted_probe_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTubeGeometry.lean:62`;
- `BF4ExactSlabShiftedProbeTubeGeometry.endpoint_separation`,
  `lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTubeGeometry.lean:77`.

The old reflection plane lies between slices. The union's site-reflected
`upperProbe` and `lowerProbe`, at observation radius `R=0`, have endpoint
separation exactly `n`; see
`BF4ExactSlabFixedSpatialSeparatedProbeControl.upperProbe`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedProbeControl.lean:69`, and
`lowerProbe`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedProbeControl.lean:72`.
Therefore the correct scalar comparison is old response versus union **lag
three**, followed by an actual contraction inequality. This corrects the
initial suggested lag-two comparison in the parallel excitation review.

## 2. A concrete aligned exhaustion, with no action substitution

The following arithmetic is a proposed specialization of the existing
definitions; these specialized identities have not yet been formalized.
Let `s : Nat`, use the union diagonal at `base=1`, `H=3`, and spatial margin,
boundary-time buffer, and heat stage all equal to `s+1`.
Compare it with the old response at margin `s`, embedded by spatial shift
`1` and time shift `2*s+7`.

| Quantity | Old response before translation | After translation / current chart |
| --- | --- | --- |
| Ambient extent | `2*s+3` | current extent `6*s+20` |
| Spatial probe coordinates | `(s+1,s+1,s+1)` | `(s+2,s+2,s+2)` |
| Lower endpoint time | `s` | `3*s+7` |
| Upper endpoint time | `s+3` | `3*s+10` |
| Current spatial width | — | `2*s+5` |
| Current action start | — | `2*s+6` |
| Current action steps | — | `2*s+8` |

The defining declarations are:

- `BF4ExactSlabShiftedProbeTubeGeometry.responseExtent` and `sliceFace`,
  `lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTubeGeometry.lean:40` and
  `lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTubeGeometry.lean:42`;
- `BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialRecenter.lean:89`;
- `BF4ExactSlabFixedSpatialAlignedBoxes.chartExtent` and `chartIds`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAlignedBoxes.lean:38` and
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialAlignedBoxes.lean:41`;
- `Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry.adjacentEvenExtent`,
  `lean/YMGap/Continuum/Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry.lean:32`;
- `Z4HalfTimeReflectionGeometry.centralExtent`,
  `lean/YMGap/Continuum/Z4HalfTimeReflectionGeometry.lean:734`;
- `BF4ExactSlabBulkEmbeddingGeometry.shiftFace`,
  `lean/YMGap/Continuum/BF4ExactSlabBulkEmbeddingGeometry.lean:36`.

The translated old full slab occupies spatial anchor coordinates
`1 <= x_i <= 2*s+4`, spatial-face times
`2*s+7 <= t <= 4*s+10`, and temporal-face times
`2*s+7 <= t < 4*s+10`. This lies inside the selected chain just specified.
The chain's exact orientation-dependent membership test is
`BF4ExactSlabFixedSpatialChainGeometry.chainIds_mem_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChainGeometry.lean:35`.

Take the root to be the lower probe face at `(s+2,s+2,s+2,3*s+7)`.
An omitted selected-chain face has either a spatial anchor outside the old
translated cube or a time outside its orientation-dependent window. Its
L-infinity distance from this root is at least `s+1`: the closest temporal
omission is the lower slice `2*s+6`; the closest spatial omission is anchor
coordinate zero. At the upper endpoint, temporal faces are excluded already
at `4*s+10`, still a distance `s+3` from the root. This explicitly retains the
temporal-face endpoint case.

These statements are the bounded geometry obligations to implement, not an
assumed identity of finite measures.

## 3. The remaining finite comparison is quantitative and local

Define `keep` by membership in the translated old full-face list and use the
current selected chain as `ambient`. The actual source translation mechanism
already exists:

- `BF4ExactSlabTranslatedHaarEmbedding.Placement`,
  `lean/YMGap/Continuum/BF4ExactSlabTranslatedHaarEmbedding.lean:42`;
- `Placement.character_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabTranslatedHaarEmbedding.lean:180`;
- `BF4ExactSlabTranslatedSelectedAction.finiteValue_pin_of_prefix`,
  `lean/YMGap/Continuum/BF4ExactSlabTranslatedSelectedAction.lean:153`.

The two room inequalities for the proposed placement are
`(2*s+3)+1 <= 6*s+20` and `(2*s+3)+(2*s+7) <= 6*s+20`.
After proving inclusion and the filtered-list permutation, these existing pins
identify the **filtered** current action with the old full action, including
both numerator and partition. They do not identify the unfiltered action.

For the comparison with that unfiltered action, an existing fixed-support box
suffices. `chartProbe_local` uses `boxSize(base,H)=max base (2*H+1)`, so here
one may use size `7` without a new optimized support proof:

- `BF4ExactSlabFixedSpatialPlacedProbeControl.boxSize`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:244`;
- `chartProbe_local`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:337`;
- `chartProbe_interval`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlacedProbeControl.lean:219`.

Its carrier size is `S = 6*7^4 = 14406`; this is a fixed support loss, not an
ambient-volume loss. The omitted-face separation above gives active core size
at least `s+1-S` (a safe weakened form of the returned inequality) through
`BF4ExactSlabCoreDistanceFloor.active_core_linf_floor`,
`lean/YMGap/Continuum/BF4ExactSlabCoreDistanceFloor.lean:56`.

The existing analytic consumers are
`BF4ExactSlabUniformCoreBudget.mixedNumerator_tail_bound`,
`lean/YMGap/Continuum/BF4ExactSlabUniformCoreBudget.lean:105`, and
`BF4ExactSlabAllNomeFaceSetComparison.finite_comparison_bound`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean:51`.
They retain and cancel both actual partitions. Their rate is
`rho = entropyRate 625 (adjustedCoreRate w hd)`, with the already supplied
small-nome guards; no new nome-independent estimate is proposed.

Consequently the proposed specialized proof yields geometric differences
for the joint moment and its two marginal moments. If their common
single-probe interval cap is `c` (chosen from the actual face-character
intervals and transported to both placements, with joint cap `c*c`), and `A` is
`BF4ExactSlabFixedSpatialBoxBoundary.boxAmplitude w hd hs 7`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoxBoundary.lean:56`), the budgets
are `2*c*c*A*rho^(s+1-S)` for the joint moment and
`2*c*A*rho^(s+1-S)` for each marginal. The source and target expectations
have absolute marginal bound `c`; the needed finite normalized interval
argument is exemplified by
`BF4ExactSlabSiteInwardTestNorm.finite_upper`,
`lean/YMGap/Continuum/BF4ExactSlabSiteInwardTestNorm.lean:88`.
Its present wrapper is the small-nome `FaceSetExpectation.finiteValue`; the
current chart uses `AllNomeFaceSetExpectation.finiteValue`. Their same-cutoff
normalization pin or a direct two-sided interval derivation is still required.

Using `ab-a'b' = a(b-b')+(a-a')b'`, the resulting covariance error is bounded
by `6*c*c*A*rho^(s+1-S)`. This displayed constant is the arithmetic budget of
the proposed three-moment comparison, **not an existing Lean declaration**.

## 4. Finite floor first; no interchange of regulator limits

At `w=1/1024`, the old full numerator satisfies the floor
`c0 = (1/16)*w^36` for every `K>=1` and every margin:
`BF4ExactSlabOriginalResponseNumeratorFloor.responseFloor`,
`lean/YMGap/Continuum/BF4ExactSlabOriginalResponseNumeratorFloor.lean:37`, and
`original_numerator_floor`,
`lean/YMGap/Continuum/BF4ExactSlabOriginalResponseNumeratorFloor.lean:43`.
Use the same heat cutoff `headCutoff(w)+(s+1)` on both sides of the finite
translation/comparison. This avoids comparing nested limiting cutoffs.

The finite comparison above would then give, on the current **unchanged**
diagonal, `connectedScalar >= c0 - C*rho^(s+1-S)`, with
`C=6*c*c*A`. An explicit sufficient threshold is
`S + geometricCutoff rho C (c0/2)`, using
`PositiveContractionResidual.geometricCutoff` and `geometric_bound`,
`lean/YMGap/Continuum/PositiveContractionResidual.lean:119` and
`lean/YMGap/Continuum/PositiveContractionResidual.lean:126`.

The existing limit consumer is
`BF4ExactSlabFixedSpatialSpatialCenteredForm.originalConnected_diagonal_converges`
at `n=H=3`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredForm.lean:127`.
The shift to `s+1` is a cofinal shift of that same diagonal. After the finite
estimate is supplied, eventual-order passage gives a positive lag-three
union floor, and the existing excitation correlator pin puts it on the actual
completed vector. No equality of completed carriers is needed.

## 5. From lag three to lag two without assuming one-step positivity

There is a short algebraic argument, now implemented in the new
`BF4SpatialUnionOddEvenResponse.lean` and kernel-checked by the parent agent. Put
`y=T_1 v`, `z=T_1 y`, and `N(x)=B(x,x)`. Actual norm contraction gives
`N(z)<=N(y)`, while positivity of the actual difference gives

`0 <= N(y-z) = N(y)+N(z)-2*B(y,z)`.

Hence `B(y,z)<=N(y)`. Self-adjoint time balance and the semigroup law identify
these scalars as `B(v,T_3 v)` and `B(v,T_2 v)`, respectively. Thus a positive
lag-three floor also bounds lag two from below, with no loss and **without**
asserting that the one-step transfer is positive.

The requisite already proved declarations are:

- `BF4SpatialUnionCompletedDistance.completedDist_time_contraction`,
  `lean/YMGap/Continuum/BF4SpatialUnionCompletedDistance.lean:144`;
- `BF4SpatialUnionPairingData.completedInner_nonnegative`,
  `lean/YMGap/Continuum/BF4SpatialUnionPairingData.lean:120`;
- `BF4SpatialUnionBilinear.completedInner_sub_left` and
  `completedInner_sub_right`,
  `lean/YMGap/Continuum/BF4SpatialUnionBilinear.lean:140` and
  `lean/YMGap/Continuum/BF4SpatialUnionBilinear.lean:145`;
- `BF4SpatialUnionGeometry.completedInner_time_balance`,
  `lean/YMGap/Continuum/BF4SpatialUnionGeometry.lean:98`;
- `BF4SpatialUnionSeminorm.completedTime_add`,
  `lean/YMGap/Continuum/BF4SpatialUnionSeminorm.lean:137`.

The new implementation contains:

- Actual all-vector time norm contraction:
  `BF4SpatialUnionOddEvenResponse.completedTime_norm_le`,
  `lean/YMGap/Continuum/BF4SpatialUnionOddEvenResponse.lean:63`.
- The signed bound `B(x,T_n x) <= B(x,x)` without positivity of `T_n`:
  `BF4SpatialUnionOddEvenResponse.completedTime_form_le`,
  `lean/YMGap/Continuum/BF4SpatialUnionOddEvenResponse.lean:74`.
- For every natural `n`, `B(x,T_(2*n+1) x) <= B(x,T_(2*n) x)`:
  `BF4SpatialUnionOddEvenResponse.odd_response_le_even`,
  `lean/YMGap/Continuum/BF4SpatialUnionOddEvenResponse.lean:87`.
- The direct floor consumer, with no new hypothesis structure:
  `BF4SpatialUnionOddEvenResponse.lagTwo_floor_of_lagThree`,
  `lean/YMGap/Continuum/BF4SpatialUnionOddEvenResponse.lean:96`.

The parent agent's focused check passed with exit 0 and no errors or warnings.
All four public axiom gates report only `[propext, Quot.sound]`; the log is
`/tmp/ym-union-odd-even-response-20260916.log`. This verification covers the new
odd/even module, not the unimplemented finite-action comparison in sections
1–4 or a full-tree build/audit.

## Status and smallest next implementation

No positive-response theorem on the union is claimed. The useful reduction
is now specific: prove the translated-full-box inclusion and omitted-face
separation above, pin the three actual probe polynomials, and instantiate the
existing signed boundary comparison. The key analytic tail estimate and old
finite positive floor already exist; a new assumption-only response scaffold
would not advance this step.

With the odd/even algebra now implemented, the next bounded proof module
should contain that geometry and its actual placement, not an interface
assuming the missing covariance inequality.
The lag-three/lag-two distinction must remain explicit. The whole proposal is
fixed-spacing SU(2) at the certified nome; it supplies no AF/continuum
nontriviality, continuous-time generator, physical mass calibration or
all-compact-simple-group claim.
