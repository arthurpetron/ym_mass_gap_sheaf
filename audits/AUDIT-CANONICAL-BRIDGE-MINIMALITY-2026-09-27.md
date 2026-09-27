# Conditional carrier reductions and physical OS target audit

Date: 2026-09-27 UTC. Base commit: `7c2d23e`.

Status: source review and mathematical argument, with the completion/bridge
reduction now kernel-checked. `CRealSeminormCompletedApproximation`,
`GNSTransferMetric`, and `BF4WilsonSpatialUnionCanonicalGNSBridge` passed
serialized focused checks with only `{propext, Quot.sound}`. The independent
Product module also passed, with the same or fewer axioms. Section 9a adds the
subsequently checked contextual laws, actual quotient, and square-positivity
construction. Line references describe this
reviewed source revision. No canonical roadmap marker or Clay obligation closes.

**Physical-target warning:** the bridge's ordinary Wilson GNS destination is
not automatically the canonical reflected positive-time OS destination.
Section 5 records the missing identification and the resulting execution
correction. The checked dense-extension theorem is target-generic;
it does not construct a physical identification.

## 1. Probe orthogonality follows from static transport

`CurrentCarrierFormCertificate` preserves the pairing and vacuum
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:106`).
The current normalized resolvent probe is already centered by
`unitExcitation_resolvent_centered`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionResolventResponse.lean:137`).
`center_fixed_iff`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionVacuumProjection.lean:191`)
identifies centeredness with vacuum orthogonality. Consequently the argument is

```text
<F(Ru), Omega> = <F(Ru), F(U)> = B(Ru,U) = 0.
```

The checked `CurrentCarrierProbeCertificate.ofFormCertificate`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:923`)
implements those rewrites. It uses neither a transfer equation nor a choice
of Cauchy representative. The existing `CurrentCarrierProbeCertificate`
structure and its fields are preserved.

## 2. Dense dynamics determines dynamics on the completed image

The older exact stage interface also benefits from the target-generic
metric argument in section 4. The checked
`CurrentStageDenseTwoStepCertificate.toCauchyTwoStepCertificate`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:1077`)
specializes `CurrentCarrierFormCertificate.toTwoStepCertificateOfDense` to
the existing stage transport and then applies it to each supplied source
Cauchy class. Its `.toBridge` at `:1099` adds the derived probe pin.
The earlier duplicate pairing-limit draft has been replaced by this specialization.
The original structures and field types are preserved; the static stage
transport and dense equation remain inputs. No range section or extra
continuity hypothesis is used, and no stage producer is constructed here.

## 3. The exact rational stage interface needs an inhabitability check

`CurrentStageCauchyStagePairingCertificate.stagePairing`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:223`)
requires each source stage pairing to equal the embedded value of a rational
GNS pairing. Indeed `GNSData.B : V -> V -> Q'`
(`lean/YMGap/Continuum/GNSQuotient.lean:102`), whereas
`BF4WilsonSpatialUnion.pairing`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnion.lean:113`) takes values in
`CReal`. Likewise `WilsonGNSData.E` is rational-valued
(`lean/YMGap/Continuum/WilsonGNS.lean:131`).

Thus a producer through that exact stage interface must prove rational
representability of every mapped stage pairing. This review does **not** prove
that a particular physical pairing is irrational or that the certificate is
uninhabitable. It identifies a restriction requiring justification before
investing in a producer. The restriction also persists in
`CurrentStageCauchyFormCertificate` (bridge module `:403`): its termwise
transport sends constant source streams to constant GNS streams, and its
completed pairing equation applies to those constants. Therefore the new
dense-stage reduction inherits this restriction. The more general
`CurrentCarrierCauchyFormCertificate`
already allows a map of entire streams and asks for completed pairing
equality; no rationality claim for each source stage appears in its fields.
No field has been weakened to address the restriction.

## 4. Stronger reduction without exact rational stage representatives

The checked `CurrentCarrierFormCertificate.toBridgeOfDense`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:1064`)
instead takes the existing completed form certificate and a two-step equation
only on embedded source stages. Those images are arbitrary completed GNS
vectors, not necessarily constant rational GNS streams. The checked proof
proceeds as follows.

1. `CurrentCarrierFormCertificate.distance_preserving` (same module `:1023`)
   expands squared differences using `RCBilinearDifference.difference_diagonal`
   (`lean/YMGap/Continuum/RCBilinearDifference.lean:19`) and rewrites the four
   pairings. No linearity hypothesis on the map is added.
2. `GNSTransferMetric.transfer_sub`
   (`lean/YMGap/Continuum/GNSTransferMetric.lean:97`) derives difference
   preservation from self-adjointness and pairing nondegeneracy.
   `transfer_nonexpansive` (same module `:117`) then derives pairwise distance
   contraction from the transfer's supplied norm contraction.
3. For a supplied source representative `X` and positive tolerance `epsilon`,
   sample its own stage at `X.modulus (quarter epsilon)`.
   `CRealSeminormCompletedApproximation.constantApproximation_bound`
   (`lean/YMGap/Continuum/CRealSeminormCompletedApproximation.lean:84`), with
   `BF4WilsonSpatialUnionCompletedDistance.distanceData`
   (`lean/YMGap/Continuum/BF4WilsonSpatialUnionCompletedDistance.lean:162`),
   gives the stage's error bound. Source time contraction and target transfer
   contraction control the two resulting errors by `epsilon/4` each.
4. The supplied dense equation identifies the middle vectors.
   `GNSTransferMetric.distance_two_segment`
   (`lean/YMGap/Continuum/GNSTransferMetric.lean:51`) budgets the quadratic
   triangle as `2*(epsilon/4) + 2*(epsilon/4) = epsilon`.
   `eq_of_forall_small` (same module `:76`) yields the completed equation.

`CurrentCarrierFormCertificate.toTwoStepCertificateOfDense`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:1039`)
implements steps 1--4 via `GNSTransferMetric.maps_eq_of_dense`
(`lean/YMGap/Continuum/GNSTransferMetric.lean:128`). Its proof specializes
the general theorem `CRealSeminormCompletedApproximation.maps_eq_of_dense`
(`lean/YMGap/Continuum/CRealSeminormCompletedApproximation.lean:138`): the target
is any type with a squared distance, all-positive-tolerance separation and the
quarter-tolerance two-segment estimate. No rational GNS presentation or target
completeness is required. For a target with the existing constructive-real
`DistanceData`, these two laws are already supplied by
`CRealSeminormCauchyRows.completed_eq_of_small`
(`lean/YMGap/Continuum/CRealSeminormCauchyRows.lean:135`) and
`CRealSeminormCompletedApproximation.completedDist_two_segment`
(`lean/YMGap/Continuum/CRealSeminormCompletedApproximation.lean:110`).
No canonical frontier type is changed. Quotient induction
proves an equality; it does not
select quotient representatives as data. Independent Sol source review found
the approximation directions and certificate types consistent, with no added
range/density premise. Subsequent focused checks confirmed elaboration and
the permitted axiom set for all three completion/bridge modules.

Thus the stronger checked reduction leaves static completed form/vacuum
transport plus its dense dynamics equation as inputs. It avoids the exact
rational stage-map restriction; it does not alter the rational canonical root,
construct the continuum datum, or provide the all-vector range section.

## 5. Producer audit: ordinary Wilson GNS is not the physical OS root

No concrete producer for `CurrentCarrierFormCertificate` was found in the
bridge, `WilsonGNS`, `WilsonMinimalBoundedMassGapHandoff`,
`MeasureLinkedOSReconstruction`, `CanonicalOSRoot`, or
`BF4PhysicalDenseStageGraphNormCompiler` modules. The scoped source review
stops at two distinct missing identifications:

- `WilsonSelectedOSGNSData.expectationPinned`
  (`lean/YMGap/Continuum/WilsonMinimalBoundedMassGapHandoff.lean:39`) equates
  the supplied Wilson expectation with the supplied OS bundle's expectation.
  `MeasureLinkedOSGNSData`
  (`lean/YMGap/Continuum/MeasureLinkedOSReconstruction.lean:132`) relates that
  bundle to supplied stage-functional semantics. Neither declaration maps
  the current BF4 `Stage` syntax into the canonical algebra or identifies
  the current reflected pairing with the canonical expectation.
- `WilsonFunctionalRoot.ambientData`
  (`lean/YMGap/Continuum/CanonicalOSRoot.lean:63`) is ordinary `W.toGNSData`.
  In contrast, `PositiveTimeOSRoot`
  (`lean/YMGap/Continuum/CanonicalOSRoot.lean:268`) carries a separate
  `positive : GNSData` and its `reflectedForm` law. Its `physicalHilbert`
  (`:513`), `physicalVacuum` (`:518`), and `completedTransfer` (`:432`) live on
  that positive-time completion. The current bridge targets the ordinary
  completion, not this separate physical carrier. No identification between
  those two target forms was found in the scoped modules.

`BF4WilsonDenseStageMapData`
(`lean/YMGap/Continuum/BF4PhysicalDenseStageGraphNormCompiler.lean:101`) does
not fill either gap: it assumes a map from canonical observables toward
finite matched physical observables, plus intertwining. It is not a forward
map from the current spatial-union carrier.

There is also no uniform producer for arbitrary supplied time pins implied
by these definitions. A form/vacuum-preserving map would force the target
vacuum's norm to be one by `completedUnit_norm_one`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionPairingData.lean:150`).
`WilsonTimeTranslationPin`
(`lean/YMGap/Continuum/WilsonGNSTransferUnderdetermination.lean:131`) includes
no vacuum normalization; `qZeroPin` (`:179`) illustrates a zero-vacuum pin.
This is an interface-level example, not an H-specific impossibility theorem.

**Execution consequence:** retain the conditional bridge as conditional.
Do not seek an unqualified ordinary-GNS identification as the next physical
producer. The target must use the reflected positive-time form, with a
same-observable Gram identity and supported representative map. The new
generic dense-extension argument is reusable there; it constructs none of
those missing physical identifications. No canonical field is changed.

## 6. The current correlator already has original reflected-source provenance

No new analytic certificate is needed to interpret the existing current
completed dense correlator as a limit of original finite reflected Wilson
expectations. The source chain is:

1. `completedTime_correlator`
   (`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeForm.lean:137`) identifies
   `B(embedStage x, completedTime lag (embedStage y))` with the class of
   `pairing x (time lag y)`.
2. `pairing` (`lean/YMGap/Continuum/BF4WilsonSpatialUnion.lean:113`) computes
   the common base `N = max x.base y.base` and evaluates `intrinsicForm` on
   the two included expressions. `atBase_time` (same module `:66`) identifies
   the second expression with the original `advance lag` of `y`.
3. `intrinsicForm`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonIntrinsicForm.lean:99`)
   chooses the maximum radius `H` of those two expressions, then `form`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz.lean:158`)
   is exactly `spatialLimit` of their reflected product
   `.mul (mirror H (chart H X)) (chart H Y)`.
4. `spatialLimit`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:76`)
   is the Cauchy real of the literal `chartScalar ... n n n` diagonal.
   `spatialCauchy_modulus` (`:70`) gives its explicit Type-level rate via
   `SpatialPivotCauchy.diagonalModulus`
   (`lean/YMGap/Continuum/SpatialPivotCauchy.lean:43`).
   `spatial_approx` (`BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:100`)
   also controls independent spatial, heat, time and scalar-approximation
   indices: spatial pivot for `r`, that pivot's row modulus for `k,t`, and
   the diagonal Cauchy modulus for `i`.
5. `chartScalar`
   (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:120`)
   is the original normalized `finiteValue` on `chartIds` with the actual
   insertion polynomial. `chartScalar_original_pin` (`:127`) equates it to
   `originalWindowScalar` at the same cutoff and symmetric time depths,
   retaining the same partition normalization.

The source restriction remains fixed nome/physical spacing with the displayed
small-nome guards. This chain is not changing-spacing convergence and does not
identify the observable with the canonical continuum algebra. An independent
Sol source review found no single correlator-level wrapper, but confirmed this
existing chain and the supplied modulus. No duplicate wrapper is added.

## 7. Supported probe representation is separate from completed normalization

`PositiveTimeOSRoot.probeObservable` and `probeNormOne`
(`lean/YMGap/Continuum/CanonicalOSRoot.lean:318`, `:321`) require a supported
algebra observable whose state has exactly unit norm. The current physical
`unitExcitation`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean:101`)
is instead constructed by completed real-scalar multiplication using
`normalizer` (`:92`) and its explicit `normalizerCauchy` (`:96`). Its norm is
proved by `unitExcitation_norm` (`:107`). In contrast, `smulStage`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnion.lean:83`) takes a rational scalar.

These declarations alone do not exhibit a supported algebra representative
of the normalized completed vector. Such an identification remains an input
to a physical root producer; completed normalization must not be silently
treated as a raw-stage construction. This is a source/type distinction, not
a proof of irrationality or nonrepresentability. No frontier type is changed.

## 8. Supported products: checked construction, not an OS quotient algebra

`BF4WilsonSpatialUnionProduct.lean` passed its focused elaboration/axiom check.
`product` (`lean/YMGap/Continuum/BF4WilsonSpatialUnionProduct.lean:50`)
places both intrinsic expressions at their maximum radius; `productStage`
(`:98`) also uses their maximum spatial base. `chart_product` (`:55`) and
`atBase_product` (`:102`) retain the literal common-chart multiplication.

`embedStage_eq_of_common_source` (`:155`) composes the existing
`distSq_at_base` (`lean/YMGap/Continuum/BF4WilsonSpatialUnion.lean:151`),
`intrinsic_distSq_zero_of_padded_diagonal`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionObservableDescent.lean:140`), and
`chartInsertion_source_congr`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionSourceIdentity.lean:75`).
It requires one finite coefficient identity, not an additional analytic
estimate. This permits different source bases without choosing a common
support bound for an entire completed stream.

`product_comm` (`BF4WilsonSpatialUnionProduct.lean:169`), `product_assoc`
(`:183`), and `product_sum_right` (`:206`) then use the existing finite
polynomial laws to conclude equality of the corresponding `embedStage`
images. No arbitrary completed-state equality is used as a product
congruence hypothesis. These results alone do not define a product on the
OS null quotient. Their subsequent consumer is the distinct time-tested
observable quotient constructed in section 9a;
the canonical reflected Gram pin and supported normalized probe remain open.
Sol reviewed the mathematical argument independently. The subsequent focused
check uses only `{propext, Quot.sound}` or fewer axioms. No roadmap marker closes.

## 9. A multiplier-only equivalence need not be preserved by time

The following is an explicit rational **paper counterexample**, independently
recomputed by Sol. It has not been formalized or kernel-checked. It concerns
a proposed generic implication, not the Wilson model or the full OS axioms.

Let `A = Q^4` with coordinatewise multiplication and unit `(1,1,1,1)`, and
let `J : A -> Q^2` and the two time maps be

```text
J(a,b,c,d)   = (d,b-c)
tau(a,b,c,d) = (a,a,a,d)
T(u,v)      = (u,0).
```

The map `tau` is a unital rational algebra endomorphism. Direct substitution
gives `J(tau p) = T(J p)`. In the Euclidean form on `Q^2`, `T` is positive,
self-adjoint and contractive, and fixes `J(1) = (1,0)`.

Define multiplier-only equivalence by
`p ~ q` iff `J(p*z) = J(q*z)` for every `z : A`. For `x=(1,0,0,0)`, every
`x*z=(z_1,0,0,0)` maps to zero, so `x ~ 0`. However, with `z_0=(0,1,0,0)`,

```text
tau(x) = (1,1,1,0)
J(tau(x)*z_0) = (0,1) != (0,0).
```

Thus `tau(x)` is not equivalent to zero. Exact intertwining and even a
positive self-adjoint contraction do not make this stronger observable
equivalence time-stable. This does not contradict the existing physical
`completedTime` map: stability of the original OS null relation is a
different assertion. No assertion is made that this finite example satisfies
the Wilson provenance, the positive-response assumptions, or all OS axioms.

### Constructive algebraic correction and checked source implementation

For a unital commutative rational algebra `A`, a rational-linear map `J`, and
an algebra endomorphism `tau`, the time-stable version is

```text
p ~_time q  iff  for every n : Nat and z : A,
                 J((tau^n p)*z) = J((tau^n q)*z).
```

This is an equivalence by equality in the target. Addition and rational
scaling respect it by linearity. For products, use the first equivalence
with test `(tau^n b)*z`, then the second with test `(tau^n a')*z`, applying
associativity and commutativity in `A`. Time preservation uses the same
condition at `n+1`; no inverse or surjectivity of time is required. Taking
`n=0` and `z=1` gives equality of the original `J` images. All tests are
explicit universal quantifiers; no representatives or moduli are selected.

This argument identifies a constructive congruence, not a new assumed
analytic certificate. The checked module defines the concrete source
`TimeContextEq` (`lean/YMGap/Continuum/BF4WilsonSpatialUnionProduct.lean:265`).
`advance_product` (`:85`) and `time_product` (`:109`) give the exact raw-time
product identity; `product_smul_left` (`:233`) and `product_unit_right`
(`:249`) supply embedded scalar/unit laws. `timeContext_time` (`:279`),
`timeContext_embed` (`:285`), and `timeContext_product` (`:308`) implement
time stability, equality of original state images, and product congruence.
The last proof rotates entire products under the embedding before using a
contextual test; it does not multiply an equality of completed vectors.

All of these declarations passed the focused check. Independent Sol review
also checked the index shift, source guards and product rotations.
`timeContext_sum` (`:343`) and `timeContext_smul` (`:350`)
also derive addition/scalar congruence from the existing completed linear
operations and their embedded-stage pins. Section 9a records the subsequent
contextual product-law proofs and their quotient consumer. Laws only after
embedding must not be mistaken for laws after every contextual test. No
reflected canonical observable map, scalar-interface repair, or continuum
scaling control is constructed.

## 9a. Checked time-tested quotient and ordinary square positivity

`context_of_common_source`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionContextLaws.lean:49`) multiplies
each advanced common-chart identity by the arbitrary supported test polynomial
before invoking the checked source descent. Its specializations
`context_product_comm` (`:74`), `context_product_assoc` (`:88`),
`context_product_unit_right` (`:115`), `context_product_unit_left` (`:126`),
`context_time_unit` (`:132`), `context_product_sum_right` (`:138`), and
`context_product_smul_left` (`:170`) prove these laws in `TimeContextEq`.
The unit-time law does not assert equality of raw radius tags.

`Observable`, `observableAlg`, and `forwardHom`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionObservableQuotient.lean:50`,
`:152`, `:159`) construct the actual tested quotient and forward-time unital
product homomorphisms. Product commutativity, associativity and both unit
laws are proved separately (`mul_comm`, `mul_assoc`, `mul_one`, `one_mul`,
same module `:74`, `:79`, `:86`, `:91`); the minimal `ObsAlg` record alone
would not certify them. Descended sum and rational scalar operations also
exist, with product distributivity and scalar compatibility; a full rational
algebra law suite is not asserted by these declarations.

`state` (`:168`) maps this quotient to the existing physical completion.
`state_ofStage`, `state_one`, `state_forward`, `state_add`, and `state_smul`
(`:172`, `:176`, `:180`, `:187`, `:195`) pin the source observable, vacuum,
time, and linear operations to those exact existing objects. No injectivity,
all-vector range section, or multiplication on completed states is claimed.

`vacuumMean` (`:203`) is the pairing of that state with the original vacuum.
`vacuumMean_ofStage`, `vacuumMean_one`, `vacuumMean_add`, `vacuumMean_smul`,
and `vacuumMean_forward` (`:207`, `:212`, `:216`, `:222`, `:229`) prove its
original pairing pin, normalization, additivity, rational homogeneity and
stationarity. It is RC-valued: `WilsonProbFunctional.ProbFunctionalC.E`
(`lean/YMGap/Continuum/WilsonProbFunctional.lean:112`) instead asks for a
CReal-valued function. No representative-selection map is constructed here.
`ObservableMeasure.ProbFunctional.E`
(`lean/YMGap/Continuum/ObservableMeasure.lean:82`) remains rational-valued.

Ordinary square positivity is now supplied by
`product_square_vacuum_nonnegative`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionProductPositivity.lean:99`).
Its finite insertion is `(q*q)*1`, with `q` the original mirrored/recentered
supported source polynomial. `chartScalar_original_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:127`)
and `originalWindowScalar_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:122`)
retain the same original normalized action. The checked Haar-carrier unit
identity removes the final unit, and `windowRatio_square_nonnegative`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowFunctionalLaws.lean:154`)
supplies nonnegativity at every regulator. The explicit spatial Cauchy
approximants preserve it. `vacuumMean_square_nonnegative`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionObservableQuotient.lean:237`)
then proves it for every tested observable class. No identification of an
ordinary square mean with a reflected diagonal is used.

All three modules passed serialized focused checks within
`{propext, Quot.sound}`. This supplies concrete fixed-spacing source objects,
not a new assumed frontier certificate. The real-observable `star = id`
is explicitly not time reflection. Ambient reflection, the canonical
reflected Gram pin, scalar-interface reconciliation, supported normalized
probe, changing-spacing control, continuum QFT and every-group Clay theorem
remain unconstructed by these declarations. Canonical field types and
chart markers are unchanged.

## 10. Reuse the existing scaling obstruction; do not assume its endpoint

The conditional Wilson extinction estimate already exists:
`sampledAutocorrelation_small`
(`lean/YMGap/Continuum/BF4WilsonUniformLatticeRateScalingObstruction.lean:93`)
uses a supplied common `q < 1`, centered source vectors with one norm cap,
and `SpacingToZero`, and returns the bound at its computed
`physicalDecayModulus` (`:48`). `sampledLimit_zero` (`:162`) identifies any
supplied same-scalar limit as zero. The time argument is a positive **natural
number**, and spacing is explicitly the duration of two original lattice
steps. No duplicate extinction theorem is added.

Those common-rate and norm-cap hypotheses are not supplied for the identified
changing-nome channel by this module. `changingNomeDynamicFamily`
(`lean/YMGap/Continuum/BF4PhysicalChangingNomeDynamicFamily.lean:76`) instead
uses the cylinder completed family and its `cutoffUniformRate`; it is not a
declaration identifying that carrier with the spatial-union completion.
`changingNomeCarrierNormalizedSpacingToZero`
(`lean/YMGap/Continuum/BF4PhysicalChangingNomeExplicitMarginLaw.lean:514`)
supplies a spacing modulus, while the `Join` structure
(`lean/YMGap/Continuum/BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.lean:95`)
still takes the raw/normalization/rate variation inputs. These declarations
do not supply the required same-observable identification with the Wilson
union family or a uniform rate cap there.

Vanishing at positive integer times and a nonzero value at zero alone do
not contradict continuity. There is a sharper **paper argument**, separately
checked by Sol: for an actual same-carrier self-adjoint semigroup `S(t)`,
strongly continuous at zero, a zero autocorrelation at time one gives

```text
0 = <v,S(1)v> = <S(1/2)v,S(1/2)v>, hence S(1/2)v = 0.
```

Repeating the same square identity yields `S(2^(-k))v = 0` for all positive
`k`; strong continuity then gives `v = 0`. This uses a genuine semigroup at
dyadic times, norm separation, and the same vector throughout. No such
consumer was found in the scoped endpoint modules inspected here:

- `ContractionSemigroup`
  (`lean/YMGap/Continuum/OSReconstruction.lean:140`) contains only
  `semigroup_witness : Unit`, not time-indexed maps or continuity laws.
  `SemigroupGenerated` (`:178`) returns the supplied operator's abstract
  `generation_law` proposition and does not expose those laws.
- `BundleLinkedOSReconstructionData`
  (`lean/YMGap/Continuum/MeasureLinkedOSReconstruction.lean:72`) carries that
  abstract semigroup; its fields do not provide the dyadic operations.
- `GeneralTransferFormLaws`
  (`lean/YMGap/Continuum/CanonicalOSRoot.lean:560`) exposes a single actual
  transfer and its form laws, not a strongly continuous physical-time family.

Thus the dyadic argument cannot yet be applied through these declarations.
The pin from the scalar scaling limit to the continuum `S(1)` pairing is
also absent from `sampledLimit_zero`. No actual changing-nome contradiction,
QFT endpoint construction, or kernel-checked dyadic theorem is claimed.

## 11. Residue and verification boundary

The bridge still takes `H : ContinuumYMExistence mu`, a selected
`WilsonGNSData`, and a `WilsonTimeTranslationPin` as parameters
(`CurrentCarrierBridge`, bridge module `:953`). Building this conditional
transport cannot itself construct those parameters. The all-vector canonical
range section (`CanonicalRangeSectionCertificate`, same module `:1635`),
same-measure OS realization, scaling control, physical Hamiltonian,
nontrivial continuum theory, and every-group Clay theorem remain open.

The Lake process `46993` and its Lean child `60253`
(`BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows/Row64.lean`) were initially
treated as externally owned. The current thread's launch record at
2026-09-27 09:51:29 UTC instead identifies this assistant's accidental
`python3 scripts/safe_lean_build.py --jobs 1 -- --` invocation, which expanded
to the unintended full-library `lake build --`. Its process start time matched.
After revalidating the exact process group, SIGINT stopped both processes;
authoritative process inspection confirmed their exit before a narrow check
started at approximately 13:52 UTC. Completed artifacts were preserved, and
no lock was removed. The earlier termination claim based on sandbox-denied
process access was invalid; permission denial is not evidence of absence.

Verification completed: monitored one-worker, 20 GiB-capped focused checks of
`CRealSeminormCompletedApproximation.lean`, `GNSTransferMetric.lean`,
`BF4WilsonSpatialUnionCanonicalGNSBridge.lean`, and
`BF4WilsonSpatialUnionProduct.lean`, in that order. All printed declarations
use only `{propext, Quot.sound}` or fewer axioms, including the two unit-probe
consequences. Elaboration fixes addressed one GNS projection rewrite and
three product/chart elaboration errors; none changed mathematical statements.
The proof ledger records the checked reductions; canonical chart markers stay
unchanged. No full-library build or axiom audit is claimed.

The subsequent focused checks of `BF4WilsonSpatialUnionContextLaws.lean`,
`BF4WilsonSpatialUnionProductPositivity.lean`, and
`BF4WilsonSpatialUnionObservableQuotient.lean` also passed, with the same
single-worker 20 GiB limit and axiom gate. No canonical field was modified.

## 12. Full-window original reflection invariance supplied

The earlier source search found reflection symmetry for mixed products of
half-window expressions, not invariance for arbitrary full-window expressions.
The latter is now proved without altering the half-space positivity statements:

| Declaration | Source | Exact result |
|---|---|---|
| `mirror_involutive` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonFullReflection.lean:65` | `mirror H (mirror H e) = e` under `Within (2*H) e`. |
| `mirror_shift_full` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonFullReflection.lean:83` | Full-window reflection commutes with centered enlargement. |
| `loop_placed_reflection` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonFullReflection.lean:122` | Actual link reflection at every offset `j <= 2*H`. |
| `placed_reflection_full` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonFullReflection.lean:145` | Literal reflected polynomial for arbitrary signed full-window expressions. |
| `originalChain_finiteValue_reflection` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonFullReflection.lean:160` | Reflection preserves finite expectation with unchanged selected action, stage and reciprocal. |
| `chartScalar_mirror` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonFullReflection.lean:182` | Equality on every original spatial/heat/time chart. |
| `spatialLimit_mirror` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonFullReflection.lean:209` | Equivalent existing CReal expectations, with the same spatial small-nome guards. |

The finite proof combines `spatial_character_reflection`
(`lean/YMGap/Continuum/BF4ExactSlabSpatialWilsonReflection.lean:101`),
`originalChain_reflection`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReflectedSymmetry.lean:213`),
and `quaternionHaar_reflectCorrectedSlabPolynomial`
(`lean/YMGap/Continuum/BF4ExactSlabVacuumReflection.lean:263`). The limit proof
uses the existing `spatial_diagonal_converges`, not a new limit or selected
representative. Sol independently reviewed the full-window geometry and the
unchanged-action/partition pin.

The distinct fixed-center time-translation identity already exists as
`spatialLimit_shift_within`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonLimitStationarity.lean:168`).
The new reflection identity is not a claim that the positive-stage quotient
is reflection-closed. An ambient algebra congruence across centered/base
presentations, invertible ambient time, and the actual same-reflected-Gram
join remain to be constructed. Equality of expectations or of OS-null
states alone is not a supplied product congruence. Canonical scalar fields
remain unchanged; no canonical root or continuum obligation closes.

Verification: a focused monitored check passed with one worker capped at
20 GiB. All seven printed public declarations depend only on
`{propext, Quot.sound}`. An initial check found missing namespace opens;
those were corrected, with no statement change or new hypothesis. No
`sorry`, classical input, trusted computation or full-tree audit was added.

## 13. Signed-time source construction and original reflected-form join

The source construction now uses integer times relative to the reflection
plane, avoiding a premature quotient of radius-tagged expressions.
`Expression`, `Within`, `radius`, and `window` in
`lean/YMGap/Continuum/BF4WilsonSignedTimeExpression.lean:21` retain the
same ordered source loops, spins and signed rational operations. The
computed radius bounds every time on both sides. Every semantic window use
has this bound, excluding truncation by `Int.toNat`.

The syntax module's focused check passed with all 27 printed declarations
inside `{propext, Quot.sound}` or axiom-free. In particular:

- `backward_forward` and `forward_backward`
  (`lean/YMGap/Continuum/BF4WilsonSignedTimeExpression.lean:268`, `:285`)
  are literal inverse-time identities, not equalities of expectations alone.
- `reflect_reflect`, `reflect_forward`, and `reflect_backward`
  (same module `:252`, `:302`, `:323`) give actual reflection involution and
  conjugacy of the two time directions.
- `ofWindow_forward` (same module `:353`) retains the existing positive
  source's physical radius advance, including every time offset.

The expectation consumer's final focused check also passed. Its 18 printed
declarations are axiom-free or depend only on `{propext, Quot.sound}`:

| Declaration | Source | Claim |
|---|---|---|
| `mean`, `meanCauchy` | `lean/YMGap/Continuum/BF4WilsonSignedTimeExpectation.lean:58`, `:63` | The original CReal spatial expectation and its explicit rational Cauchy witness. |
| `mean_at` | same module `:69` | Centered-window independence under a witnessed support bound. |
| `mean_reflect` | same module `:82` | Invariance under actual time reflection. |
| `mean_forward`, `mean_backward` | same module `:92`, `:103` | Physical stationarity from unequal original padding, not from centered rechart alone. |
| `mean_one`, `mean_add`, `mean_smul` | same module `:112`, `:116`, `:128` | Normalization and rational linearity of that same CReal mean, up to CReal equivalence. |
| `mean_square_nonnegative` | same module `:150` | Ordinary square positivity from the original finite expectation, not the OS diagonal. |
| `mean_reflected_intrinsic` | same module `:185` | The reflected mean of the signed source pair is the existing intrinsic OS form. |
| `pairing_as_mean`, `completedInner_as_mean` | same module `:205`, `:217` | Every pair of stages in the all-finite-base union has exactly that reflected mean, including the current completed dense images. |
| `completedTime_correlator_as_mean` | same module `:229` | The current completed transfer acts on those dense correlators by the constructed signed forward time. |

Sol independently reviewed the expectation, positivity and same-carrier
pins. These are raw expression and source-state results: no literal
associative-algebra equality, ambient algebra quotient, canonical rational
functional, completed canonical range section, or continuum construction is
asserted. The common base in the pairing theorem is computed from its two
inputs; no common base is chosen for an arbitrary Cauchy stream.

Both checks were serialized through the monitored safe launcher, with one
worker capped at 20 GiB and the existing pressure/reserve safeguards. The
initial syntax draft exposed arithmetic guards insufficiently and allowed
bare `omega` on conjunction goals to introduce `Classical.choice`; explicit
conjunction introduction and guarded arithmetic removed that dependency.
The final axiom output contains no `Classical.choice` or `sorryAx`. The
expectation retry explicitly unfolded the spatial representative for its
positivity proof and closed a definitional equality in the transfer pin.
No mathematical statement was weakened. No full-library audit was run.

### Next mathematical join, not yet a proved declaration

An ambient contextual relation can test equality of `mean(a*z)` for every
signed-time expression `z`, using CReal equivalence rather than equality
of chosen CReal representatives. Unlike the earlier half-space relation,
inverse time is now available: a translated test can be pulled back with
`backward`, and reflection with `reflect`. Descending multiplication still
requires the actual mean-level polynomial laws. The supported quotient join
also needs a constructive supported representative for a sufficiently shifted
signed test and an explicit product-vacuum mean pin. Neither is inferred from
completed-state equality. Signed spatial-base inclusion and its mean
coherence must be supplied before this is an all-base ambient quotient.
This identifies the next proof obligation; it does not add a frontier bundle
or change a canonical field.
