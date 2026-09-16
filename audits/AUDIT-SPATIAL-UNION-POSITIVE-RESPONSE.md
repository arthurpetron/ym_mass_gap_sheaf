# Positive original response on the same completed spatial union

Date: 2026-09-16. Base checkpoint: `da1df7c`, committed and pushed before
this increment. The preceding reduced-inverse/translation checkpoint is
classified **PROGRESS**. This checkpoint proves the response comparison
identified by that review; it does not add an assumed positive-response field.

## Whole-project goal and status

For every compact simple gauge group, construct a nontrivial continuum
Yang--Mills theory on R^4 satisfying the required QFT axioms, with an isolated
vacuum and positive physical Hamiltonian mass gap. Keep the constructive,
Mathlib-free MLTT/HoTT gate, explicit witnesses/moduli, and SAME physical
objects at every join. **The continuum/all-group Clay target remains OPEN.**

The new result is a positive raw connected response for the existing centered
plaquette in the existing SU(2) spatial union, at fixed nome `1/1024` and fixed
lattice spacing. If `v` is that excitation, `B` its completed pairing and `T`
its actual physical discrete time, then

`(1/16)*(1/1024)^36 <= B(v,T_3 v) <= B(v,T_2 v)`.

The lower floor and its proof are returned as Type-valued data by
`BF4SpatialUnionPositiveResponse.positiveResponse`,
`lean/YMGap/Continuum/BF4SpatialUnionPositiveResponse.lean:123`.
The two lower-bound theorems are `lagThree_floor` and `lagTwo_floor`, in the
same module at lines 113 and 119. Neither changes the earlier strict bound.

## Causal proof: expand the missing comparison, then compose it

### 1. Actual geometry, including orientation-dependent endpoints

`BF4SpatialUnionResponseGeometry.responsePlacement`,
`lean/YMGap/Continuum/BF4SpatialUnionResponseGeometry.lean:50`, embeds the old
extent `2*s+3` into current extent `6*s+20`, with spatial shift `1` and time
shift `2*s+7`. `sourceExtent_eq` and `targetExtent_eq` at lines 42 and 46
prove those formulas. The current diagonal has base `1`, horizon `3`, and
spatial margin/time buffer `s+1`.

`translatedIds_subset` (same file:133) includes every translated old full-action
face in the actual selected chain. `filter_perm` (:145) identifies the filtered
chain with that translated full action by permutation, not by replacing the
ambient action. `translatedIds_mem_iff` (:124) retains the different closed
spatial-time and strict temporal-time endpoints. `omitted_separation` (:175)
proves each omitted face lies at L-infinity distance at least `s+1` from the
actual lower root; `active_core_floor` (:186) supplies the analytic consumer.

### 2. Keep both partitions through the signed estimate

The fixed connected support box has side `7`; its carrier size is
`S=6*7^4=14406`, independent of ambient margin. The actual depth is the natural
subtraction `s+1-S` (zero at small margins),
`BF4SpatialUnionResponseBoundary.depth`,
`lean/YMGap/Continuum/BF4SpatialUnionResponseBoundary.lean:47`.
`core_floor` (:55) and `determinant_bound` (:75) discharge the existing
boundary-tail inputs for the current chart. `finiteValue_bound` (:94) cancels
both actual partitions and bounds the normalized finite moment difference.

For nome `w`, the bound retains the named guards `0<w<1`,
`heatRatio w <= 1/2`, `heatRemainderBound w < 1`, and
`rho(w)=entropyRate 625 (adjustedCoreRate w hd) < 1`.
The amplitude is the existing `boxAmplitude w hd hs 7`. This is not a
beta-independent estimate, a spacing estimate, or a volume-dependent
reciprocal-partition penalty.

### 3. Pin the original probes and the original finite law

`BF4SpatialUnionResponseProbePins.centralProbe`,
`lean/YMGap/Continuum/BF4SpatialUnionResponseProbePins.lean:59`, is the value
of the EXISTING `BF4SpatialUnionExcitation.centralStage`, not a fresh observable.
`lower_translation_prefix` (:164) and `upper_translation_prefix` (:173)
identify its actual current placements with the translated old probes.
The interval objects `currentLower_interval` (:70), `currentUpper_interval`
(:74) and `joint_interval` (:258) give common cap `c=singleCap` and joint
cap `c*c`. `currentUpper_local` (:246), `currentLower_local` (:251) and
`joint_local` (:267) put all three moments on the same connected chart.

`BF4SpatialUnionResponseActionPin.finiteValue_pin`,
`lean/YMGap/Continuum/BF4SpatialUnionResponseActionPin.lean:73`, transports
the filtered target expectation to the old full-source expectation at the
same cutoff `headCutoff(w)+stage`. `finiteCovariance_pin` (:116) does this
for the connected expression. The unused-in-final-limit expectation/covariance
limit pins are also checked; the positive-floor proof uses the finite pin and
does NOT interchange two regulator limits.

### 4. Three moments give one connected error

`BF4ExactSlabAllNomeFiniteMomentBounds.finiteValue_abs_bound`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFiniteMomentBounds.lean:61`, derives
the normalized cap from the actual interval and positive finite action.
It requires `0<w<1`, not the small-nome comparison hypothesis.
`covariance_difference_bound` (:80) uses the exact difference of marginal
products; `covariance_six_bound` (:102) gives the factor `6*c*c`.
`finite_covariance_comparison` (:127) supplies both marginal caps from the
actual laws. `finite_covariance_floor` (:142) normalizes a supplied
partition-square-cleared connected numerator floor by its positive partition.

Consequently `BF4SpatialUnionResponseFiniteComparison.covariance_bound`,
`lean/YMGap/Continuum/BF4SpatialUnionResponseFiniteComparison.lean:110`, proves

`abs(ambientCovariance - filteredCovariance) <= C(w)*rho(w)^(s+1-S)`

for every margin `s` and finite stage, where
`C(w)=6*c*c*boxAmplitude w hd hs 7` is `errorAmplitude` (:82) and the full
error is `errorBound` (:86). No covariance estimate is assumed as an input.

The fixed-nome source is
`BF4ExactSlabOriginalResponseNumeratorFloor.original_numerator_floor`,
`lean/YMGap/Continuum/BF4ExactSlabOriginalResponseNumeratorFloor.lean:43`.
It supplies the old numerator floor for every cutoff `K>=1` and every margin.
`source_floor`, `filtered_floor` and `finite_lower_bound` in
`BF4SpatialUnionResponseFiniteComparison.lean` at lines 150, 164 and 175
normalize, transport and compare it. The lower/upper product order is restored
by coefficient/Haar commutativity, not an invalid termwise-prefix permutation.
The resulting finite assertion is

`responseFloor <= ambientCovariance + errorBound`.

### 5. Preserve the full floor on the unchanged diagonal

`BF4SpatialUnionResponseFiniteComparison.diagonal_pin`,
`lean/YMGap/Continuum/BF4SpatialUnionResponseFiniteComparison.lean:199`, pins
the ambient covariance at stage `s+1` to the EXISTING `connectedScalar`
diagonal. Its joint and both unit-marginal moments have one common action,
cutoff and chart. No new limiting scalar is substituted.

`BF4SpatialUnionPositiveResponse.diagonal`,
`lean/YMGap/Continuum/BF4SpatialUnionPositiveResponse.lean:61`, retains the
original spatial margin, time buffer and heat stage all equal to `r`.
`comparisonModulus` (:75) is the Type-valued function

`epsilon |-> S + geometricCutoff rho C epsilon + 1`.

`error_small` (:78) and `diagonal_floor_error` (:87) use `s=r-1`, proving
`r>=1` before applying the pin. The original-index threshold makes the finite
comparison error at most `epsilon`; it does not reschedule the regulators.
`diagonal_converges` (:97) uses the already constructed original spatial limit.
`spatial_response_floor` (:105) passes eventual order with every positive
tolerance and preserves the FULL floor, not only half of it.

Finally `lagThree_floor` (:113) uses
`BF4SpatialUnionExcitation.excitation_correlator_pin`,
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:69`, and the existing
centered-moment pin. `lagTwo_floor` (:119) consumes the previously checked
odd/even contraction inequality. One-step positivity is not assumed.

## Five-front parallel disposition

All five requested fronts admit some independent work; their final physical
joins are not independent. Four lanes (parent plus three agents) worked on
this increment: geometry/limit, action transport/composition, original probe
pins, and finite-moment inequalities plus independent geometry review.
Compilation remained serialized. The earlier three source reviews remain
the detailed inventory of Hilbert/OS, mass/spacing and all-group inputs.

| Requested front | Checked contribution available now | Remaining independent work and required join |
| --- | --- | --- |
| Nonconstant excitation | Existing actual nonzero vector; NEW positive lag-three/two response above. | Continuum survival of this actual excitation is open. The new raw floor is not a normalized canonical OS probe. |
| Full Hilbert/OS/QFT | Existing same-union rational operations, represented-row limits, strict bound and reduced inverse; no new completeness axiom. | Real scalar multiplication and representative independence can use supplied CReal rows. Arbitrary quotient-sequence completeness, full original-algebra coverage and QFT reconstruction are not supplied. The canonical rational-GNSData/CReal-form mismatch remains. |
| Spatial and spacing control | Existing positive diagonal spatial semigroup; NEW literal full-box/selected-chain comparison on the actual diagonal. | Signed/axiswise spatial translations and changing-action/spacing estimates are distinct tasks. The small-nome AF guard obstruction remains. |
| Positive physical mass calibration | Existing scalar calibration compilers; NEW nonzero response on the actual transfer carrier. | SAME-transfer physical-length pin, fixed-physical-distance estimates and finite physical rate control are still needed. The fixed lattice floor has no physical-unit calibration. |
| Every compact simple group | Existing global-form/descent and scalar group machinery, inventoried in the group review. | Actual representation/Haar/action and global-form producers can be developed separately and fed to reusable analysis. No physical group instance beyond the present SU(2) one is supplied by this increment. |

The detailed source inventories, explicitly historical where status has since
advanced, are [the five-front audit](AUDIT-PARALLEL-FRONTIERS-2026-09-16.md),
[excitation](AUDIT-PARALLEL-EXCITATION-2026-09-16.md),
[spacing and mass](AUDIT-PARALLEL-SPACING-MASS-2026-09-16.md), and
[all groups](AUDIT-PARALLEL-ALL-GROUPS-2026-09-16.md).

`CanonicalOSRoot.PositiveTimeOSRoot`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, still demands an actual
canonical supported/normalized probe and rational-valued GNS data. Its
`probeNormOne` and `probeRayleighLower` fields (same file:321 and :330)
are not inhabited by this raw CReal/RC response theorem. No canonical
frontier field, scorecard, or theory definition is weakened or declared closed.

## Verification and independent review

All seven modules passed focused `scripts/safe_lean_build.py --check` runs,
one worker with 20 GiB cap, process/swap preflight before each run. The 81
public printed gates depend only on a subset of `{propext, Quot.sound}`.
Final logs contain no errors, warnings, `sorryAx`, classical dependency or
native decision axiom. Counts include axiom-free reports and multiline lists.

| Module (under `lean/YMGap/Continuum/`) | Gates | Final log under `/tmp/` | SHA-256 |
| --- | ---: | --- | --- |
| BF4SpatialUnionResponseGeometry | 21 | `ym-union-response-geometry-20260916.log` | `029a5d56de52360f3d6ce13ab575d059cf5b6b15256d5fe3c6e54e636e9ce368` |
| BF4SpatialUnionResponseBoundary | 7 | `ym-union-response-boundary-20260916.log` | `586021f91e9b27e8ccb9bd6d1435a28acd5d2449d0b7b74ffd1d4c1b29e0cc08` |
| BF4SpatialUnionResponseProbePins | 21 | `ym-union-response-probe-pins-20260916.log` | `b8d7ab3baaa938513f990938009db19f67f800d53596ac1711e411643c242b6c` |
| BF4SpatialUnionResponseActionPin | 8 | `ym-union-response-action-pin-20260916.log` | `7e950dcf89fed0e5535ad1256d9506ee0db7c41c96be8bc1758c184b9d6ca9b0` |
| BF4ExactSlabAllNomeFiniteMomentBounds | 5 | `ym-allnome-finite-moment-bounds-20260916.log` | `b9d37ffc8b2da3f8b8066c82d1346c71333c6233e0b2fbc2701f23246c2ad679` |
| BF4SpatialUnionResponseFiniteComparison | 9 | `ym-union-response-finite-comparison-20260916.log` | `99b35fb51729cf645b839ad22765fa5b40db12e632f08ef2753de7e24f3753ea` |
| BF4SpatialUnionPositiveResponse | 10 | `ym-union-positive-response-20260916.log` | `cead53f10a03162ce31ec9476f0aa66c75aaf478a1d73287d7ab1cbe2c1911e6` |

Independent source review found no defect in the full-face orientation-aware
geometry, fixed support loss, both-partition comparison, original-index
modulus or same-carrier limit pins. Reviewers did not compile; the parent
performed all checks and read the contributed source. There is no full-tree
verification claim: semantic-root imports were added but the root, full build,
full axiom audit and guards were not run. No old Lean proof, sorry, axiom,
analytic guard, canonical field or safety limit changed. CI remains manual-only.
No literature scan occurred; the existing twelve-hour cadence is unchanged.
