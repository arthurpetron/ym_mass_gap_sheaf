# Same-operator Wilson range approximation checkpoint

## Scope

This checkpoint records the bidirectional join from the backward requirement
of a same-operator approximate-preimage interface to a forward construction
on the current completed SU(2) Wilson carrier. It is fixed-spacing data only.

## Forward declaration

`lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.lean`

- `evenOrbitSum` constructs the finite vector
  `sum_{k<n} T^(2*k) x` using the existing `completedAdd`, `completedTime`,
  and `completedZero`.
- `evenOrbitSum_sub_twoStep` proves
  `(I - T^2) (sum_{k<n} T^(2*k) x) = x - T^(2*n) x`
  on the same `UnionCompletion` carrier.
- `evenOrbitSum_error_bound` identifies the actual approximation error with
  `T^(2*n)x` and bounds its squared norm for an existing vacuum-complement
  vector by the existing `norm_decay` at exponent `2*n`.
- `evenOrbitSum_modulus` packages the explicit cutoff
  `geometricCutoff (q*q) (normCap X) epsilon`, and
  `evenOrbitSum_error_small` proves the resulting late-tail estimate for
  every `n` above that cutoff.
- `evenOrbitSumCauchy` and `evenOrbitSumCauchy_pin` retain the preimage as
  supplied Cauchy data and identify its quotient with the finite sum.
- `evenOrbitSum_range_data` returns the same-completion approximate-preimage
  witness, with vacuum-complement orthogonality retained as an input.
- `evenOrbitResidual` names the actual `(I-T^2)` defect, and
  `evenOrbitResidual_kernel` proves its kernel is trivial on the completed
  vacuum complement.
- `evenOrbitResidual_selfAdjoint` proves the defect is symmetric for the
  completed pairing, which is the operator-side condition needed by a future
  dense-range consumer.
- `evenOrbitSumStage` and `evenOrbitSumStage_pin` retain the finite geometric
  preimage as a strict `Stage`, and `evenOrbitStage_error_small` transfers the
  explicit modulus to that finite-stage carrier.
- `evenOrbitStage_range_data` packages the cutoff, strict stage preimage, and
  error proof as one dependent witness.
- `evenOrbitResidual_center` proves that the defect commutes with the existing
  same-carrier vacuum-centering projection.
- `evenOrbitCentered_range_data` applies the range certificate to the existing
  center of any supplied representative, retaining the same carrier and no
  uncentered-decay claim.
- `evenOrbitResidual_centered_pairing` identifies the defect pairing with the
  difference of the existing connected lag-zero and lag-two correlators.
- `evenOrbitResidual_form_nonnegative` consumes the strict two-step form bound
  to prove nonnegativity of the actual defect pairing on the supplied completed
  vacuum complement, and `evenOrbitCenteredResidual_form_nonnegative` transports
  the same conclusion through the existing center projection.
- `evenOrbitCentered_correlator_difference_nonnegative` expresses that
  positivity directly as nonnegativity of the connected lag-zero minus lag-two
  correlator difference for the same centered observable.

The rate is explicit: `q = twoStepRate w hd`. No inverse, spectral theorem,
choice, auxiliary transfer, or continuum/spacing hypothesis is introduced.
The modulus is representative-dependent through the existing `normCap X`;
it is a fixed-spacing consumer contract, not a uniform-in-observable or
continuum modulus.

## Verification boundary

Command:

```text
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.olean \
  --log-file /tmp/ym-range-approx-20260918ah.log
```

Result: passed. The twenty-two public declarations printed only
`{propext, Quot.sound}`. No `sorryAx`, `Classical.*`, `native_decide`, or
new axiom appears. Log SHA-256:

`9839a02f895377eceb39fd734e5c654667b24396d40f080346d2b77bcd243d1a`.

The full root, full-tree build, axiom audit, guard and progress runs were not
performed. The result does not supply strict density of strictly-past
observables, a completed spectral gap beyond existing fixed-spacing decay,
changing-spacing control, physical mass calibration, continuum survival, or
the Clay theorem.

## Existing-resolvent carrier seam

An attempted direct bridge to the older named resolvent was rejected by Lean.
The present module's `V` is
`BF4WilsonSpatialUnionSeminorm.UnionCompletion`, declared through the Wilson
namespace at `lean/YMGap/Continuum/BF4WilsonSpatialUnionRangeApproximation.lean:27,53`.
The resolvent module's `V` is
`BF4SpatialUnionSeminorm.UnionCompletion`, opened at
`lean/YMGap/Continuum/BF4SpatialUnionResolvent.lean:23,40`.
The failed focused attempt therefore produced type mismatches when applying
`resolvent_right_inverse` and `resolvent_left_inverse`; it was removed rather
than coerced. The failed log is `/tmp/ym-range-approx-20260918ai.log`.
This is an unclosed carrier-identification obligation, not evidence that the
two completions are definitionally equal.

## Current-carrier resolvent join, checked 2026-09-18

The carrier seam was closed by a port, not by coercion: the following modules
all quantify over `BF4WilsonSpatialUnionSeminorm.UnionCompletion` and import
the current Wilson transfer and pairing.

- `BF4WilsonSpatialUnionWeightedNorm.budget` (`lean/YMGap/Continuum/BF4WilsonSpatialUnionWeightedNorm.lean:31`) defines the explicit
  `K=(1-q)⁻²` budget; `norm_weighted_identity` (:122) and
  `series_step_bound` (:146) prove the weighted square estimate.
- `BF4WilsonSpatialUnionResolventPartial.partialSum`
  (`lean/YMGap/Continuum/BF4WilsonSpatialUnionResolventPartial.lean:111`),
  `partialCauchy` (:192), and `seriesRows` (:247) construct the finite sums
  and their supplied Cauchy moduli. `partial_tail_small` (:214) is the explicit
  cutoff consumer.
- `BF4WilsonSpatialUnionResolvent.resolvent`
  (`lean/YMGap/Continuum/BF4WilsonSpatialUnionResolvent.lean:85`) defines the
  diagonal-limit operator. `resolvent_equation` (:152),
  `resolvent_right_inverse` (:204), `resolvent_left_inverse` (:221), and
  `resolvent_sub` (:259) prove its same-carrier Poisson and inverse identities;
  `defect_selfAdjoint` (:269) and `resolvent_selfAdjoint` (:278) add the
  completed-pairing symmetry needed by an operator-side consumer.
- `BF4WilsonSpatialUnionResolventBound.resolvent_norm_bound`
  (`lean/YMGap/Continuum/BF4WilsonSpatialUnionResolventBound.lean:133`) and
  `resolvent_distance_bound` (:139) give the explicit current-carrier norm and
  distance bounds.

Focused serialized checks passed with no `sorryAx`, `Classical.*`, or
`native_decide`; every printed gate in the three modules depends only on
`{propext, Quot.sound}`. Evidence logs and hashes:

| target | log | SHA-256 |
| --- | --- | --- |
| `BF4WilsonSpatialUnionResolventPartial.lean` | `/tmp/ym-wilson-resolvent-partial-current4.log` | `e6b8d3b731bfc94086f1cd16ef3dee718dbf8f45dc5354982301002614b586cf` |
| `BF4WilsonSpatialUnionResolvent.lean` | `/tmp/ym-wilson-resolvent-current6.log` | `8f416ac340b40b24aa3d356261686ccf16ae8e42bec581aa1cb362015c69af29` |
| `BF4WilsonSpatialUnionResolventBound.lean` | `/tmp/ym-wilson-resolvent-bound-current2.log` | `c86a1e5349d5595fb626f90e786a8e811c5ee8efe73e99b9e437a8b50f7ed9f8` |

This closes the fixed-spacing same-carrier represented resolvent branch. It
does not prove strict dense-observable range, a spacing-uniform rate, physical
time/mass calibration, a continuum limit, QFT reconstruction, or the Clay
theorem. The older legacy resolvent remains a separate carrier and was not
reused.
