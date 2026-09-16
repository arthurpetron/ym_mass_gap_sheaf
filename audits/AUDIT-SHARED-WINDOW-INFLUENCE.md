# Shared-face geometry and the absolute-window inference

Date: 2026-09-15 (America/Los_Angeles). Base: `3f3f975`.

The whole-project goal remains constructive continuum Yang--Mills with the
required QFT axioms and a positive physical Hamiltonian gap for every compact
simple group. This increment tests a proposed intermediate estimate. It does
not prove spatial decay, an OS transfer gap, or any continuum statement.

## 1. The proposed inference and its precise boundary

The existing original conditional projections commute when the links share
no physical plaquette. The prospective next argument compares neighboring
updates after deleting only their shared face factors, retaining the other
interactions. Before constructing reference completions or transporting their
conditional projections, we tested whether the existing absolute one-face
window can even force a small conditional correlation in a general positive
law.

It cannot force a squared conditional norm at most one half: a computed
positive two-state law in that same numerical window violates that bound.
This is a counterexample to the inference from the window ALONE. The law is
not identified with Yang--Mills, and its correlation is not a lower bound on
the original Yang--Mills conditional influence. No claim is made that every
pair/block approach, every sharper window, or every contraction below one
is impossible.

## 2. Geometry: one shared face, not six

`BF4ExactSlabSharedFaceUniqueness.sharedIds_length_le_one`,
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceUniqueness.lean:24`, proves

    left != right  ==>  length(sharedIds extent left right) <= 1.

It uses literal two-link plaquette rigidity and injectivity of physical face
identifiers. Distinctness is essential; one link can belong to six faces.
The old unconditional six-face theorem is preserved. The existing original
product split is `BF4ExactSlabSharedFaceGeometry.heatProduct_shared_partition`,
`lean/YMGap/Continuum/BF4ExactSlabSharedFaceGeometry.lean:99`; the retained
left-only/right-only/neither split is `retainedHeat_partition` at line 145
of the same file. These are polynomial factorizations, not independence of
the law after integrating its exterior.

## 3. The existing all-nome constants

Let m=`headFloor(w)` and M=`prefixCap(w)`. Their definitions are
`BF4ExactSlabRetainedHeatHeadComparison.headFloor`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:50`, and
`BF4ExactSlabAllNomeTailInterval.prefixCap`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:117`.
The weighted product lower and upper bounds are respectively
`headProduct_weighted_floor` and `headProduct_weighted_upper`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:186` and
`:205`. Their cutoff threshold remains `headCutoff(w)` at line 55.

For every rational 0<w<1 the new results are:

| Declaration | Source | Result |
|---|---|---|
| `BF4ExactSlabSharedWindowFloorBound.headFloor_le_oneThirtySecond` | `lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46` | m <= 1/32. |
| `BF4ExactSlabSharedWindowFloorBound.thirtyTwo_mul_headFloor_le_prefixCap` | `lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:57` | 32*m <= M. |

Thus removing the old exponent-six loss does not make THIS absolute window
narrow. These are upper/lower facts about chosen comparison constants, not
claims that the actual heat density attains either endpoint. The constants
and cutoff still depend on w; no beta-uniform physical gap is asserted.

## 4. A computed finite witness

All declarations in this section are in
`lean/YMGap/Continuum/RationalTwoStateWindowWitness.lean`, namespace
`RationalTwoStateWindowWitness`.

| Declaration | Line | Result |
|---|---|---|
| `weight` | 27 | Literal table [[M,m],[m,M]] on Bool x Bool. |
| `weight_window`, `weight_positive` | 61, 69 | Every entry lies in [m,M] and is positive when 0<m<=M. |
| `mass_eq`, `mass_positive` | 87, 93 | Actual four-term mass is 2*(M+m)>0. |
| `normalizer`, `normalization` | 99, 122 | Computed rational inverse of that mass. |
| `row_probability`, `column_probability` | 136, 141 | Both normalized marginals are uniform. |
| `sign_means`, `sign_squared_norms` | 169, 185 | Both sign probes are centered and have squared norm one. |
| `correlation` | 194 | Their normalized correlation is rho=(M-m)/(M+m). |
| `conditionalSign`, `conditionalSign_eq` | 109, 207 | Literal conditional row average equals rho times the row sign. |
| `conditional_squared_norm` | 220 | Its normalized squared norm is rho*rho. |

The conditional average uses the actual row weights and their proved row
mass. Its norm is computed with the same joint law and actual normalizer.
There is no supplied correlation hypothesis and no physical-model claim.

The numerical specialization is in namespace
`BF4ExactSlabSharedWindowInfluenceObstruction`, file
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowInfluenceObstruction.lean`:

| Declaration | Line | Result |
|---|---|---|
| `conditionalSquaredNorm` | 66 | Evaluated conditional norm for m=headFloor(w), M=prefixCap(w). |
| `witness_weight_window` | 75 | Strict positivity and both window bounds for every actual entry. |
| `conditionalSquaredNorm_lower` | 85 | Squared conditional norm >=961/1089. |
| `conditionalSquaredNorm_gt_sevenEighths` | 100 | It is strictly greater than 7/8. |
| `not_absolute_window_half_norm_inference` | 112 | A universal half-of-input-squared-norm bound already fails on this explicit finite family. |

The arithmetic is division-cleared: 33*(M-m)-31*(M+m)=2*(M-32*m)>=0.
Hence rho>=31/33 and rho^2>=961/1089. The final negation uses the actual
conditional expectation, actual window and proved unit input norm, rather
than only an inequality for a proposed coefficient. Its universal premise
ranges over the symmetric two-state laws; failure even on that subclass
also excludes an inference intended for all positive weighted laws using
only the same absolute density window.

## 5. Route decision and remaining consumer

Do not construct a shared-deleted completion solely to feed this coarse
absolute window into a small-neighbor estimate. The current original
`conditionalProjection`,
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:220`, acts
on `BF4ExactSlabStarFullActionProbe.fullData`,
`lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`, using ALL
physical face factors. The non-neighbor theorem is not already a theorem
about arbitrary retained-action projections on an identified completion.

Sharper small-nome estimates are NOT refuted. In particular,
`BF4ExactSlabSmallNomeHaarComparison.insertFace_lower` and
`insertFace_upper`,
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:147` and
`:135`, give the one-face factors 1-delta(w),1+delta(w), under their
explicit small-nome guard. Here delta(w)=128*w^3 by
`QuaternionHaarCharacterInterval.heatRemainderBound_eq`,
`lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean:85`.
These sharper statements carry information absent from [headFloor,prefixCap].

The next missing analytic input remains a spatially decaying bound on the
SIGNED original response, with its exact partition factors, or on the
original two-partition boundary determinant. The existing consumers are
`BF4ExactSlabConnectedFaceResponse.covariance_response_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`, and
`BF4ExactSlabBoundaryLimitNormalization.expectationDifference_bound_of_prefix_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabBoundaryLimitNormalization.lean:230`.
Both accept supplied coefficients; neither constructs spatial decay.

The parallel read-only review found no proved, action-specific spatial
cross-ratio or blocked retained-interaction estimate supplying those inputs
in the inspected modules:

- `BF4RoundedPositiveAFWindows.retainedHarnack`,
  `lean/YMGap/Continuum/BF4RoundedPositiveAFWindows.lean:155`, constructs a
  comparison for a supplied completed heat-factor product, not its equality
  with the original interacting physical kernel.
- `BF4PhysicalHalfAmplitudeRetainedHarnackBridge.physicalHalfAmplitude_crossRatio_of_retainedRealization`,
  `lean/YMGap/Continuum/BF4PhysicalHalfAmplitudeRetainedHarnackBridge.lean:235`,
  consumes retained Harnack data AND an entrywise physical identification.
  Its scale package additionally assumes bounded spread and physical
  identification at lines 322 and 327 of the same file.
- `BF4RetainedGramReferenceOrder.retainedSU2Quadratic_reference_sandwich_of_boundaryWeightComparison`,
  `lean/YMGap/Continuum/BF4RetainedGramReferenceOrder.lean:415`, consumes the
  boundary-weight inequalities at lines 419 and 424; it does not prove them.
- `RationalCrossRatioDiameter.FiniteCrossRatioDiameterCertificate`,
  `lean/YMGap/Continuum/RationalCrossRatioDiameter.lean:55`, carries the
  cross-ratio bound as a field.

Another fixed small-nome estimate does not itself settle the matched
physical route: `BF4SmallNomeAFGuardObstruction.blocked_guard_fails`,
`lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:97`, proves failure
of that old guard after one matched blocking step under its explicit
small-g chart hypotheses. A physical-regime estimate or a justified passage
to a controlled regime is still needed. No such passage is supplied here.

## 6. Verification

All four new modules passed their first focused check, serialized through
`scripts/safe_lean_build.py` with one worker and the mandatory 20 GiB ceiling.
All 31 public gates report only subsets of {propext, Quot.sound}; the four
raw finite-weight definitions are axiom-free. Direct import artifacts were
checked as newer than their sources; no dependency rebuild was performed.
No limit was raised, no literal hole or custom axiom was introduced, and no
old statement or canonical frontier field was changed. Four root imports
were added; root/full-tree compilation and a full axiom audit were NOT run.

Final local log SHA-256 values:

- `/tmp/BF4ExactSlabSharedFaceUniqueness.log`:
  `079a759c4fe8f24f934f6ed05fc6e8f66588d85891e32937138dcac7d37c649b`.
- `/tmp/BF4ExactSlabSharedWindowFloorBound.log`:
  `a531d61634d4b5a67cf3c5ab73454a23fcf2d428713f8abc1085b02333f66531`.
- `/tmp/RationalTwoStateWindowWitness.log`:
  `19140ca8fef6e22a06303be93e639d86eb161683df361bcc23bb9ed86bb2b495`.
- `/tmp/BF4ExactSlabSharedWindowInfluenceObstruction.log`:
  `bfaa79a97e02ead9c5a2ec28d0bfd09f219974b4e3ea0d87a1bc29462a70798a`.

Parallel branches produced the geometry, generic witness and constant
specialization; the source review identified the still-unsupplied physical
input. The parent reviewed all new sources and alone ran the four checks.
CI remains manual-only. The goal remains active.
