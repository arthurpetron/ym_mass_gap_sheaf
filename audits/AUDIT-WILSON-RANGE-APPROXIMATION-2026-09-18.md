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
  `resolvent_add` (:270), `defect_smul` (:280), `resolvent_smul` (:297), and
  `resolvent_time` (:313) prove additive, rational-scalar, and physical-time
  commutation laws; `defect_selfAdjoint` (:324) and
  `resolvent_selfAdjoint` (:333) add the completed-pairing symmetry needed by
  an operator-side consumer. `defect_zero` (:362), `resolvent_zero` (:366),
  and `resolvent_ne_zero` (:371) give the corresponding fixed-spacing
  non-erasure certificate for nonzero centered vectors.
- `BF4WilsonSpatialUnionResolventBound.resolvent_norm_bound`
  (`lean/YMGap/Continuum/BF4WilsonSpatialUnionResolventBound.lean:133`) and
  `resolvent_distance_bound` (:139) give the explicit current-carrier norm and
  distance bounds.

Focused serialized checks passed with no `sorryAx`, `Classical.*`, or
`native_decide`; every printed gate in the four modules depends only on
`{propext, Quot.sound}`. Evidence logs and hashes:

| target | log | SHA-256 |
| --- | --- | --- |
| `BF4WilsonSpatialUnionResolventPartial.lean` | `/tmp/ym-wilson-resolvent-partial-current4.log` | `e6b8d3b731bfc94086f1cd16ef3dee718dbf8f45dc5354982301002614b586cf` |
| `BF4WilsonSpatialUnionResolvent.lean` | `/tmp/ym-wilson-resolvent-current11.log` | `471504afd78717318604a44b8fccdb273d35491b677aec9523fba50516fb2899` |
| `BF4WilsonSpatialUnionResolventBound.lean` | `/tmp/ym-wilson-resolvent-bound-current2.log` | `c86a1e5349d5595fb626f90e786a8e811c5ee8efe73e99b9e437a8b50f7ed9f8` |

This closes the fixed-spacing same-carrier represented resolvent branch. It
does not prove strict dense-observable range, a spacing-uniform rate, physical
time/mass calibration, a continuum limit, QFT reconstruction, or the Clay
theorem. The older legacy resolvent remains a separate carrier and was not
reused.

## Resolvent/excitation probe join, checked 2026-09-18

`BF4WilsonSpatialUnionResolventResponse.unitExcitation_center_fixed`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionResolventResponse.lean:121`) uses
the existing normalized Wilson excitation's actual orthogonality. The module
then derives `unitExcitation_ne_zero` (:125) from the existing fixed-spacing
same-object response theorem and feeds it to
`unitExcitation_resolvent_ne_zero` (:133), while
`unitExcitation_resolvent_centered` (:137) retains the vacuum-complement
property. This is the smallest checked probe certificate joining the
current-carrier resolvent to a concrete same-object excitation.

The same module now proves `unitExcitation_resolvent_norm_floor` (:140). Its
proof expands the squared-distance triangle for the resolvent defect, applies
the existing two-step contraction to the centered resolvent image, and
contracts the four-copy bound by the explicit rational factor `1/4`. Thus the
resolvent image has a quantitative nonzero squared-norm floor on this one
normalized probe, not merely a propositional non-erasure result. The estimate
is still fixed-spacing and small-nome SU(2); it is not a spacing-uniform
operator gap and does not cross the canonical `GNSData`/OS scalar bridge.

The focused check `/tmp/ym-wilson-resolvent-response-20260918c.log` passed
with SHA-256
`5a6f7e354791ccff0bd347a76760a805ff5b2d12ed33d99172d350c0ca182201`; all five
gates use only `{propext, Quot.sound}`. The result remains fixed-spacing,
small-nome SU(2) non-erasure, not a changing-spacing or continuum-survival
certificate.

## Conditional canonical OS/GNS handoff, checked 2026-09-18

`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean` now makes
the backward meet explicit. `CurrentCarrierBridge` (lines 65--82) requires a
map from the current `UnionCompletion` into a selected canonical
`WilsonTimeTranslationPin` completion, exact `RC`-form preservation and zero
preservation, two-step transfer intertwining, and vacuum orthogonality of the
transported resolvent probe. It has no inhabitant in the repository and does
not identify the carriers by definitional equality.

Given this named bridge, `CurrentCarrierBridge.canonical_resolvent_norm_floor`
(lines 109--117) rewrites the target canonical norm through the form-preserving
field and consumes the checked
`BF4WilsonSpatialUnionResolventResponse.unitExcitation_resolvent_norm_floor`.
`canonicalProbe` (lines 119--124) packages the vector, `1/4` floor,
orthogonality, and two-step relation. The focused serialized bridge check
passed with only `{propext, Quot.sound}`; this is a conditional carrier
handoff, not a completed OS/GNS realization, spacing-uniform gap, or continuum
theorem. The bridge check log is
`/tmp/ym-wilson-canonical-bridge-20260918c.log` (SHA-256
`7e6d12d68eaa8dd390067aebf26b372d47e32337b1f5f98346f117eeb3fc1c2c`).

## Concrete current physical sector, checked 2026-09-18

The forward fragment is now explicitly consumable as
`lean/YMGap/Continuum/BF4WilsonSpatialUnionCurrentSector.lean`.
`CompletedPhysicalSU2Sector.currentSector` selects the existing completed
Wilson carrier, `completedTime 1` as the physical discrete step,
`completedUnit` as the current vacuum (fixed by that step), and
`completedTime 2` as the selected two-step map. Its fields are discharged by
the existing same-carrier time-balance, positivity, contraction, semigroup,
vacuum-complement, and unit-norm declarations. The normalized Wilson
excitation supplies a nonzero probe, its vacuum orthogonality, and the already
checked same-object lower and upper two-step response bounds. The package also
exposes the existing uniform strict two-step form bound for every current
carrier vector orthogonal to the selected vacuum, with explicit rate
`twoStepRate nome hd`.
The package also retains the current-carrier resolvent probe's centeredness,
non-erasure, and explicit `1/4` squared-norm floor.

The public projection lemmas are
`CompletedPhysicalSU2Sector.current_twoStep_strict_form_bound`,
`CompletedPhysicalSU2Sector.current_time_decay`,
`CompletedPhysicalSU2Sector.current_same_object_correlator_pin`,
`CompletedPhysicalSU2Sector.current_connected_correlator_pin`,
`CompletedPhysicalSU2Sector.current_connected_correlator_sq_decay`,
`CompletedPhysicalSU2Sector.current_probe_connected_twoStep_lower`,
`CompletedPhysicalSU2Sector.current_probe_connected_twoStep_upper`,
`CompletedPhysicalSU2Sector.current_probe_twoStep_strict_lower`, and
`CompletedPhysicalSU2Sector.current_resolvent_probe_floor`. This closes a
forward landmark for the backward spectral/OS consumer while preserving the
carrier boundary: it is fixed-spacing, small-nome SU(2) data, not a canonical
OS/GNS identification, spacing-uniform gap, physical mass calibration,
continuum limit, or Clay theorem.

Focused serialized check:
`/tmp/ym-wilson-current-sector-20260918c.log`, SHA-256
`6339d52f59db13669b7a17b2ec5901c93396a89ddf0c41a1553bf1c64e070dfe`.
The printed gates use only `{propext, Quot.sound}`.

## Fixed-spacing logarithmic transfer mass, checked 2026-09-18

`lean/YMGap/Continuum/BF4WilsonSpatialUnionDiscreteLogGap.lean` consumes the
current strict rational rate `twoStepRate nome hd`. It constructs the genuine
binary range reduction (`currentRateBinExp`, `currentRateMantissa`), defines
`currentTransferMass` as the exact constructive `-log(currentRate)`, proves
`currentTransferMass_pos`, and pins it through
`currentTransferLogReduction` to `CReal.log`.

This is the logarithmic conversion of the fixed discrete transfer rate only.
No physical lattice spacing, canonical OS/GNS Hamiltonian, spacing-uniform
rate band, or continuum mass theorem is inferred. Focused log:
`/tmp/ym-wilson-discrete-log-gap-20260918a.log`; SHA-256
`1f56b616c701aa71c2454415c884a3ec65b288deb729e53de44f2d7669944126`.
All printed gates use only `{propext, Quot.sound}`.

## Fixed-spacing physical calibration, checked 2026-09-18

`lean/YMGap/Continuum/BF4WilsonSpatialUnionPhysicalCalibration.lean` adds an
explicit `CurrentSpacing` datum to the current fixed-spacing carrier. Its
`currentPhysicalRate` is the checked dimensionless
`currentTransferMass = -log(currentRate)` multiplied by the constructive
reciprocal of that positive spacing. `currentPhysicalRate_posEv` proves the
resulting dimensionful rate is eventually strictly positive, and
`currentPhysicalRate_log_pin` transports the exact logarithm pin through the
calibration.

This is a finite-spacing dimensional certificate only. It does not construct
the physical Yang--Mills spacing trajectory, a uniform `a → 0` floor, a
canonical OS/GNS bridge, or a continuum mass-gap theorem. Focused log:
`/tmp/ym-wilson-physical-calibration-20260918d.log`; SHA-256
`c0c18265f016c52434c0ccd51629777d0c1414063b3917c4d15c6199c502a412`.
All printed gates use only `{propext, Quot.sound}`.

## Same-mass spacing monotonicity, checked 2026-09-18

The physical-calibration module now also proves
`spacingReciprocal_antitone`: if `A.a ≤ B.a`, then the reciprocal of `B` is
below the reciprocal of `A`, by direct positive-denominator cross multiplication.
`currentTransferMass_nonnegative` converts the already proved strict current
mass into the eventual nonnegative order needed by constructive-real
multiplication.  The resulting
`currentPhysicalRate_mono_spacing` compares
`currentPhysicalRate B ≤ currentPhysicalRate A` on the SAME dimensionless
transfer mass.  This is the exact spacing-order edge needed by a later
trajectory compiler; it does not construct that trajectory, a uniform rational
floor, or a continuum limit.

Focused serialized check:
`/tmp/ym-wilson-physical-calibration-mono5.log`; SHA-256
`ab31ffac1263ad323e8de12434565453be845c5457b8a09fd35e480be1d5e5e2`.
The added declarations use only `{propext, Quot.sound}`.

## Explicit rational physical-rate floor, checked 2026-09-18

`FullLogMarginLower.rationalMargin_le_hamiltonianGapRealAll` now closes the
full-range arithmetic comparison: for any positive rational separator and its
constructive binary reduction, `1 - sep` is below the exact `-log(sep)`.
`BF4WilsonSpatialUnionPhysicalCalibration.currentTransferMass_margin_floor`
specializes this to the actual current Wilson rate.  Given a positive rational
spacing ceiling `c` and `A.a ≤ c`,
`currentPhysicalRate_floor_of_spacing_le` proves the rational floor
`(1-currentRate)/c` below the calibrated rate at `A`; its positivity is
`currentPhysicalRate_floor_pos`.

This is a genuine same-carrier uniform lower bound over an explicit spacing
class. The spacing trajectory, upper rate control, canonical OS/GNS passage,
and continuum construction remain unprovided.

Focused logs:
`/tmp/ym-full-log-margin-lower-floor2.log` (SHA-256
`01d124186e9362543764bb18e049d8b40f46a0a57e90eb177a13866c4e1e7e0c`), and
`/tmp/ym-wilson-physical-calibration-floor3.log` (SHA-256
`55412e321dfb1e84658047ad666c1f1921524a3b685536982726d70e5f9966f4`).

## Fixed-mass vanishing-spacing obstruction, checked 2026-09-18

`CurrentSpacingSchedule` packages only a positive spacing sequence and its
explicit modulus of convergence to zero.  The theorem
`currentRateFloor_cofinal` shows that the rational floors
`currentRateFloorAt S j` eventually exceed every prescribed nonnegative
rational threshold.  This is the exact constructive diagnosis for the current
fixed-rate branch: dividing a fixed positive `-log(currentRate)` by a spacing
that tends to zero cannot yield a finite continuum physical-rate band.

The result is not a no-go theorem for Yang--Mills. It says that the next
same-theory producer must couple the transfer separator to the changing
spacing (or supply an equivalent renormalization), while preserving the
original action, observable, and OS carrier.

`fixedMass_no_finite_physical_ceiling` strengthens this from a cofinality
diagnostic to a contradiction: for every positive proposed ceiling `C`, the
assumption `currentRateMargin ≤ C * S.a j` at every schedule index contradicts
`currentRateFloor_cofinal` at the threshold `1 + C`. Thus the fixed current
carrier cannot inhabit the two-sided physical-rate band required by a
continuum schedule.

Focused check:
`/tmp/ym-wilson-physical-calibration-noceiling4.log`; SHA-256
`85bcb5f7d6023daf6c8cf1c61e9c3cb64ad6f95084c83892eef38334194199f1`.
The added declarations, including
`fixedMass_no_finite_physical_ceiling`, use only `{propext, Quot.sound}`.

## Forward/backward carrier-join audit, checked 2026-09-18

The current forward package is `CompletedPhysicalSU2Sector.currentSector`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCurrentSector.lean:142`), whose
completion is the Wilson `UnionCompletion` of `Stage` (`BF4WilsonSpatialUnionSeminorm.lean:98,139`).
The backward physical-family consumer instead requires
`DynamicVacuumSectorCompletedFamily.completedGap`
(`BF4PhysicalDynamicVacuumSectorCompletedFamily.lean:53`), built from
`CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData` and the
separate cylinder presentation (`BF4PhysicalCutoffVacuumSectorCylinderCompletion.lean:51,93`).
These carriers are not definitionally equal.

The existing matched-AF route is conditional: its
`MatchedPhysicalRootCoercivityGapProducer.offRay` and `.ray`
(`BF4PhysicalMatchedAFRootCoercivityGapPath.lean:53`) require scale-indexed
rooted coercivity/capacity witnesses, and `toCompletedFamily` (:111) produces
the separate dynamic cylinder family. Its `FractionScaling` (:138) further
requires explicit two-sided comparisons with the changing spacing. The
`BF4QuarterPhysicalSeparatorProducer`
(`BF4PhysicalSeparatorProducer.lean:179`) additionally requires a local-gluing
certificate, a rational `CorrInterface`, and a same-object/rate-sharpness pin;
the current Wilson correlators are `RC`-valued
(`BF4WilsonSpatialUnionCurrentSector.lean:198,204`) and do not supply those
rational pins.

An unconditional same-current-carrier spacing-dependent producer was not found
after searching `BF4WilsonSpatialUnion*.lean`,
`BF4PhysicalSeparatorProducer.lean`,
`BF4PhysicalMatchedAFRootCoercivityGapPath.lean`,
`BF4PhysicalMatchedAFConditionalVarianceGapPath.lean`,
`BF4PhysicalMatchedAFDynamicFamilyCompiler.lean`,
`BF4PhysicalDynamicVacuumSectorCompletedFamily.lean`, and
`BF4PhysicalDynamicVacuumSectorObservablePath.lean`. The existing
`CurrentCarrierBridge` (`BF4WilsonSpatialUnionCanonicalGNSBridge.lean:65`)
is also conditional and targets a canonical `WilsonTimeTranslationPin`; it
does not repair this dynamic-family mismatch.
