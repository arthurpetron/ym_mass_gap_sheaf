# Same-carrier row limits and parallel causal frontiers

Date: 2026-09-16. Base checkpoint: `b84fa5e`, already committed and pushed.
That preceding goal turn is classified **PROGRESS**. This checkpoint adds
checked mathematical results, not merely a new schedule. The three auxiliary
reviews are source audits, not new kernel verification of historical modules.

## Whole-project goal

For every compact simple gauge group, construct a nontrivial continuum
Yang--Mills theory on R^4 satisfying the required QFT axioms, with an isolated
vacuum and positive physical Hamiltonian mass gap. Retain the constructive,
Mathlib-free MLTT/HoTT gate and identify the SAME group, action, observables,
limiting theory and physical operators throughout. **This target remains OPEN.**

## Answer to the five-front parallelization request

The five labels are not five serial prerequisites of the strict-bound proof.
The strict bound and fixed-spacing nonconstant excitation are already present.
The remaining work splits into independent investigations with shared physical
integration requirements; no evidence supports a percentage-to-completion.

| Requested front | Current evidence | Useful independent work / required join |
| --- | --- | --- |
| Nonconstant excitation | `BF4SpatialUnionExcitation.excitation`, `lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:57`; `excitation_norm_floor`, same file:92; closed instance `BF4SpatialUnionSmallNome.excitation`, `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:52`. | Fixed-spacing witness is already constructed. Positive nonzero-time response and continuum survival are distinct open tasks. The former is demanded by `CanonicalOSRoot.PositiveTimeOSRoot`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, including `probeRayleighLower` at line 330. See the excitation review below. |
| Full Hilbert/OS/QFT structure | Actual rational operations and centering already exist; the new represented-row results below now preserve time and centering under limits on the SAME carrier. | Shared constructive analysis can proceed independently of new group-specific bounds. Full real scalar structure, original-algebra coverage, continuous-time reconstruction and canonical pins are not supplied by these row limits. `PositiveTimeOSRoot.positive` uses `GNSData` (`lean/YMGap/Continuum/CanonicalOSRoot.lean:272`), whose form is rational-valued (`lean/YMGap/Continuum/GNSQuotient.lean:102`); the union form is CReal/RC-valued. This is an actual interface mismatch, not a license to substitute another carrier. |
| Spatial and spacing control | Fixed-nome spatial comparison: `chartScalar_spatial_bound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialComparison.lean:56`; base coherence: `spatialPairing_inclusion`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseCoherence.lean:294`. | Full spatial translation and changing-coupling/spacing comparison can be investigated separately. The old guard cannot supply the AF tail: `no_fine_guard_on_chart` and `no_blocked_guard_on_chart`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` and `:133`. See the spacing/mass review. |
| Positive physical mass calibration | Scalar calibration is already available: `FixedDistanceContraction.floorRate_le_marginRate`, `lean/YMGap/Continuum/FixedDistancePhysicalSeparator.lean:185`; `fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:108`. | Prove the SAME transfer's physical-length pin, fixed-distance macro-contraction and finite upper rate control. `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`, remains supplied data. A fixed dimensionless rate below one is not these physical inputs. |
| Every compact simple group | Global-form codes, quotient/descent and SU(3) scalar tail bounds already exist; see the all-groups review. `mass_gap_of_cartanType`, `lean/YMGap/MassGap/AllSimpleTypes.lean:280`, is a conditional scalar composition, not a physical group construction. | Global-form realization, actual representation/Haar/action data and another group's physical functional can proceed independently of SU(2) completion. The present spin-half observable does not even descend unchanged to SO(3): `so3_spinHalf_rejected`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`. Reuse generic analysis; construct each group's physical inputs. |

Four concurrent work lanes were used: parent implementation of completion and
relaxation; one excitation reviewer; one spatial/spacing-and-mass reviewer;
one all-group reviewer. Lean compilation remained serialized. The reviewers
did not add assumption-only wrappers for already existing scalar compilers.

Detailed source reports:

- [Excitation and positive-response rejoin](AUDIT-PARALLEL-EXCITATION-2026-09-16.md).
- [Spatial/spacing and physical-mass joins](AUDIT-PARALLEL-SPACING-MASS-2026-09-16.md).
- [Global forms and all-group physical producers](AUDIT-PARALLEL-ALL-GROUPS-2026-09-16.md).

## New mathematical component: computed limits, not assumed completeness

`CRealSeminormCompletedApproximation.DistanceData`,
`lean/YMGap/Continuum/CRealSeminormCompletedApproximation.lean:30`, stores
distance and geometric laws on an existing completion, **not completeness**.
Its dense approximation returns the original dense point and its error proof:
`approximationData`, same file:95. Sampling a supplied stream at its own
`invSucc n` tolerance is `approximant`, same file:102.

`CRealSeminormCauchyRows.CauchyRows`,
`lean/YMGap/Continuum/CRealSeminormCauchyRows.lean:50`, carries the rows
`Nat -> D.Cauchy` and outer modulus as Type-level data. The actual diagonal
has rate `max(outerModulus(epsilon/16), (epsilon/16).den)`:
`diagonalRate` at line 66 and `diagonalCauchy` at line 98. Its completion
class `rowLimit` (line 103) converges at `outerModulus(epsilon/16)` by
`rowLimit_bound` (line 109). `rowLimit_independent` (line 157) proves
independence of supplied representatives; `rowLimit_presentationRows`
(line 179) recovers the original class.

This does not choose representatives of an arbitrary sequence into a quotient.
The existing `GNSComplete.GeneralCompletionCauchy` has the same important
distinction: its `pt` field is `Nat -> CauchyGNS D`, not arbitrary quotient
points (`lean/YMGap/Continuum/GNSComplete.lean:323`). Neither interface is
used to erase a required representative or modulus.

The generic extraction is pinned back to the original thermodynamic
implementation: `BF4ExactSlabThermodynamicGenericRowsPin.rowLimit_pin`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicGenericRowsPin.lean:75`, is
definitional equality. The rows, modulus, diagonal and rates are unchanged.
This is not an equality between the old thermodynamic and union carriers.

## Actual union instance and consequences

`BF4SpatialUnionCompletedDistance.completedDist`,
`lean/YMGap/Continuum/BF4SpatialUnionCompletedDistance.lean:56`, is the
actual `B(x-y,x-y)`. Its dense-distance limit is proved by the common-base
difference identity (`representativeDist_converges`, line 65), not assumed
definitionally. Every field of `distanceData` (line 151) is supplied on
the existing `UnionCompletion`. `completedDist_time_contraction` (line 144)
is constant-one contraction for original physical discrete time.

The existing strict estimate gives squared-norm decay `q(w)^n` for the
centered vector: `BF4SpatialUnionRelaxation.centered_norm_decay`,
`lean/YMGap/Continuum/BF4SpatialUnionRelaxation.lean:61`. Its same-carrier
distance to the unit projection is bounded by that quantity:
`relaxation_centered_bound` (line 79). A scalar Cauchy ceiling from the
supplied representative (`normCap`, line 92) computes `relaxationModulus`
(line 110) and a Type-valued `relaxationCertificate` (line 128).
The rate retains its nome parameter; there is no beta-uniform or physical
mass assertion.

`BF4SpatialUnionCauchyRows.timeRows` and `centerRows`,
`lean/YMGap/Continuum/BF4SpatialUnionCauchyRows.lean:54` and `:79`, keep
the actual representatives and outer modulus. `rowLimit_time` (line 69)
and `rowLimit_center` (line 93) prove commutation with computed limits using
nonexpansiveness and uniqueness. `rowLimit_orthogonal` (line 102) proves
closure of the EXISTING unit complement under represented limits;
`orthogonalRowLimit` (line 111) returns its actual element.

The actual orbit is itself a represented Cauchy family, `relaxationRows`
(line 116), with outer modulus `relaxationModulus(X,epsilon/4)`.
`relaxationRows_limit` (line 132) identifies its computed diagonal limit
with the original unit projection. This joins the limit machinery to the
original operator; it is not a parallel abstract model.

## Next consumers and proof boundaries

The represented-row machinery can now consume computed partial sums for
the reduced inverse of `I-T_2`. The existing template
`BF4ExactSlabThermodynamicResolventPartial.lean` belongs to an older carrier
and uses its own numerical tail estimate. The new union needs a tail bound
depending on its actual `q(w)<1`; that proof and the actual union resolvent
are **not implemented in this checkpoint**. No old constant or stronger nome
guard is silently substituted.

An independent analytic task is a positive nonzero-time connected response.
The excitation report identifies both the current original-connected-scalar
limit consumer and an older positive-response theorem whose same-scalar pin
is absent. A scalar equality/comparison is the appropriate minimal bridge;
a full isomorphism of the two completions is not presumed necessary.

The generic limit results need no nonabelian structure. Their SU(2) instance
uses the previously proved, explicitly small-nome spatial form. This is not
a group-agnostic beta-uniform physical-gap argument. All continuum, full
observable/Hilbert/OS/QFT, physical-mass and all-group obligations listed
above remain open. No canonical frontier field or scorecard was weakened.

## Verification and review

Six new modules were checked through `scripts/safe_lean_build.py`, one worker,
20 GiB per worker, with process/swap checks before each run. All 78 public
printed gates use only `{propext, Quot.sound}`. Logs contain no errors,
warnings, `sorryAx`, or `Classical` dependency. The original relaxation
session handle disappeared across continuation; process inspection showed
no live compiler, and a fresh direct check finished with exit 0 and the same
log hash. This was not an overlapping restart.

| Module | Gates | Focused log under `/tmp/` | SHA-256 |
| --- | ---: | --- | --- |
| CRealSeminormCompletedApproximation | 10 | `ym-generic-completed-approximation-20260916.log` | `46557e8f9ae9ffbcc31e211e38305e88f4d347de625bf2e90b096f6bd3fc7bd1` |
| CRealSeminormCauchyRows | 16 | `ym-generic-cauchy-rows-20260916.log` | `15ab74683ad7701c9945ab4e845015d774e2d7d92f47804670b1d58c9c7d0940` |
| BF4ExactSlabThermodynamicGenericRowsPin | 12 | `ym-thermodynamic-generic-rows-pin-20260916.log` | `80efa932c1f6f51ac5b6a2c5c1af865a3fe9200c0856a3a5e08c2d9075172537` |
| BF4SpatialUnionCompletedDistance | 16 | `ym-union-completed-distance-20260916.log` | `fb02763883ba8b3af4378116f1e7aee079ab78694391cbd7f3cbb1301d42088e` |
| BF4SpatialUnionRelaxation | 11 | `ym-union-relaxation-confirmed-20260916.log` | `0baefc150a09d3236fe5bf920888343b1e29d4636b6969568a952cf6ef56ff53` |
| BF4SpatialUnionCauchyRows | 13 | `ym-union-cauchy-rows-20260916.log` | `9ca5299786f827b9daca1119da6d4087610805766203728010bb952718287eab` |

Independent source review covered all six modules: supplied representatives,
Type-valued rates, distance pins, limit uniqueness, same-object time/centering
and no hidden completeness/choice assumption. No old Lean proof changed;
only new modules and semantic-root imports were added. Root/full-tree/full
axiom audit and guards were not run. CI remains manual-only. No literature
scan occurred; the 12-hour cadence remains unchanged.
