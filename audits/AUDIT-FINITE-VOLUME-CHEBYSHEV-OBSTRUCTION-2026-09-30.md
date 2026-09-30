# Existing finite-volume Chebyshev factor: proved volume-cost limitation

Date: 2026-09-30 UTC. Whole-project goal remains OPEN: constructive continuum
Yang--Mills on R^4 for every compact simple group, with same-theory QFT
axioms and a positive finite physical mass gap.

## New mathematical result

Let F be the number of original physical slab faces. The previously
constructed coefficient is delta=headFloor(w)^F/prefixCap(w)^F, and the
actual covariance multiplier is

`f(w,extent,n) = 1/T_n(1 + (2/625)*delta)`.

The new theorem proves, for every rational 0<w<1 and n<=F,

`1-(1/8)^F <= f(w,extent,n) <= 1`.

The original head floor is <=1/32 and the prefix cap >=1, so delta<=32^-F.
Writing e=(2/625)*delta gives 0<=e<=1/2 and e*4^n<=8^-F. The existing
Chebyshev recurrence bound gives 1<=T_n(1+e)<=1+8^-F; elementary reciprocal
order gives the result. All comparisons retain the ACTUAL coefficient.

A literal row of distinct physical plaquettes proves extent<=F. Hence
`1-8^-extent <= f <= 1`. Given positive rational epsilon, every
extent>=epsilon.den has `1-epsilon <= f <= 1`, uniformly in nome and in
all degrees n<=F. In particular the window includes n<=extent. This is
an explicit modulus, not an erased existence claim.

## Declaration evidence

Paths in this table are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `coercivity` | `BF4ExactSlabFiniteVolumeCoercivity.lean:88` | Existing original-action floor/cap coefficient. |
| `reverseCoefficient` | `BF4ExactSlabFiniteVolumeReverseEnergy.lean:92` | Actual 2+(2/625)*delta, not a substitute. |
| `covarianceFactor`, `finiteCovariance_sq_bound` | `BF4ExactSlabFiniteVolumeChebyshevCovariance.lean:59`, `:65` | Existing multiplier and original normalized covariance/variance consumer, with explicit `16*n` disjointness. |
| `extent_le_physicalFaces_length` | `BF4ExactSlabPhysicalFaceCount.lean:21` | New literal full-slab geometry. |
| `reciprocal_band`, `nearOne_reciprocal_bounds` | `ChebyshevReciprocalNearOne.lean:22`, `:52` | New scalar reciprocal bounds; the former is the actual consumer's helper. |
| `coercivity_le_face_power` | `BF4ExactSlabFiniteVolumeChebyshevObstruction.lean:72` | Existing coefficient <=32^-F. |
| `denominator_bounds`, `factor_bounds` | `BF4ExactSlabFiniteVolumeChebyshevObstruction.lean:94`, `:134` | Actual denominator and multiplier, for n<=F. |
| `factor_extent_bounds`, `factor_bounds_of_degree_le_extent` | `BF4ExactSlabFiniteVolumeChebyshevObstruction.lean:147`, `:158` | Extent conversion with explicit degree guards. |
| `factorModulus`, `factor_approaches_one` | `BF4ExactSlabFiniteVolumeChebyshevObstruction.lean:166`, `:169` | Returned tolerance cutoff and its uniform bound. |

## Exact scope and route decision

This is a lower bound on an UPPER-BOUND MULTIPLIER, not a lower bound on
actual covariance. It rules out extracting decay from this factor on
growing slabs within the stated degree window. It does not refute a sharper
interacting estimate, conditional-generator gap, OS transfer gap or
Yang--Mills mass gap. No statement identifies that auxiliary conditional
operator with physical OS time.

We do NOT prove that geometric disjointness forces n<=F, nor that every
degree in the window is geometrically admissible. Both restrictions must
be checked if applying the original covariance theorem. The result differs
from `BF4ExactSlabLocalChebyshevObstruction.factor_bounds`: that existing
theorem concerns the degree-dependent LOCAL cone coefficient, not the
global finite-volume coefficient tested here.

Stop optimizing this coefficient as a spatial-decay producer in the
proved window. The missing useful original signed estimate remains open.
No canonical frontier field or displayed chart state changed.

## Source review: the exact response algebra already exists

The following were inspected, not newly proved in this checkpoint. Paths
are relative to `lean/YMGap/Continuum/`.

- `BF4ExactSlabFaceInsertionDeterminant.lean:59`,
  `face_insertion_determinant`, retains the actual appended plaquette factor
  in the partition-cleared change of expectation.
- `BF4ExactSlabBulkBoundaryResponse.lean:68`,
  `boundaryNumerator_covariance`, retains the entire cutoff-dependent added
  exterior weight in the original target Haar integral.
- `BF4ExactSlabAllNomeFaceSetComparison.lean:64` and `:86`,
  `comparison_bound_eventually` and `insertion_bound_eventually`, consume
  finite determinant bounds and pass to cutoff-removed expectations.
- `BF4ExactSlabConnectedFaceResponse.lean:188`, `:209`, `:224`,
  `finite_response_cleared`, `finite_response_bound`,
  and `covariance_response_bound_eventually`, retain both
  endpoint partition squares and the connected response before taking a
  bound and its cutoff limit. These do not produce the missing bound.
- `BF4ExactSlabProbeRootedBoundaryExpansion.lean:80`,
  `mixedNumerator_active_expansion`, retains the signed active expansion.
  The absolute budget begins in
  `BF4ExactSlabMixedFiniteBoundaryBudget.lean:114`,
  `mixedNumerator_budget_bound`; the tail consumer
  `BF4ExactSlabUniformCoreBudget.lean:105`, `mixedNumerator_tail_bound`,
  and geometric comparison
  `BF4ExactSlabCoordinateBoundaryComparison.lean:119`, `expectation_bound`,
  retain their small-nome/entropy guards.

Thus another normalization identity is not the missing producer. Continue
with a useful signed original-action response or collective-energy bound,
with its actual parameter range and endpoint partitions intact. Existing
strong-coupling guards are not estimates on a nome approaching one.

The completed small-nome residual-pair estimate is also already consumed:
`BF4ExactSlabTwoLinkResidualLowerBound.lean:68`,
`conditional_residual_pair_lower`, feeds
`BF4ExactSlabConditionalGeneratorLowerBound.lean:71`,
`signedNeighborEnergy_lower`, and its existing positive pilot margin.
Reapplying that estimate to rational approximants is not a new producer.
`BF4ExactSlabTwoLinkFeatureWedge.lean:89`, `covarianceVector_wedge_pin`,
is an exact cancellation identity, not size control on the minors.
`BF4ExactSlabFixedSpatialBoxBoundary.lean:96`, `determinant_bound`,
requires localized polynomial insertions with interval certificates;
it does not quantify over arbitrary completed conditional residuals.
A short new collective-bound producer was NOT FOUND in those four modules.
The next analytic task must address that missing quantitative estimate,
not duplicate the already closed small-nome pair-to-generator chain.

## Verification

Root proved the actual coefficient bound; Sol supplied scalar reciprocal
algebra and independently reviewed scope; Luna supplied full-slab geometry.
All final checks were serialized through `scripts/safe_lean_build.py`,
one worker, 20 GiB worker ceiling, 12 GiB OS reserve, dynamic telemetry,
`--status-seconds 300`. Preflight reported 79% memory free and no competing
compiler/test/runner process. All checks finished in their initial calls;
there was no long-job polling.

| Focused checked file | Result | Printed gates |
| --- | --- | --- |
| `ChebyshevReciprocalNearOne.lean` | PASS | 3 |
| `BF4ExactSlabPhysicalFaceCount.lean` | PASS after missing namespace repair | 1 |
| `BF4ExactSlabFiniteVolumeChebyshevObstruction.lean` | PASS | 7 |

All eleven final gates are empty or within {propext, Quot.sound}. No new
sorry, axiom, analytic hypothesis, frontier weakening, or classical input.
Full-root/full-tree build, audit and guard were NOT run. Root imports were
registered, not separately compiled as a full library check.

Logs: `/tmp/ym-chebyshev-reciprocal-near-one-20260930.log`,
`/tmp/ym-physical-face-count-20260930.log`,
`/tmp/ym-finite-volume-chebyshev-obstruction-20260930.log`.
