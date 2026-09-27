# Conditional carrier reductions and physical OS target audit

Date: 2026-09-27 UTC. Base commit: `7c2d23e`.

Status: source review and mathematical argument; the accompanying Lean draft
has **not** passed elaboration or its axiom gates. Line references into the
bridge module below refer to the reviewed working-tree draft. Other references
are to unchanged source. This report closes no checked roadmap node.
The Lean drafts remain uncommitted pending verification; references to the
new generic module describe the local draft, not a verified file on `main`.

**Physical-target warning:** the bridge's ordinary Wilson GNS destination is
not automatically the canonical reflected positive-time OS destination.
Section 5 records the missing identification and the resulting execution
correction. The useful dense-extension draft has been made target-generic;
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

The draft `CurrentCarrierProbeCertificate.ofFormCertificate`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:923`)
implements those rewrites. It uses neither a transfer equation nor a choice
of Cauchy representative. The existing `CurrentCarrierProbeCertificate`
structure and its fields are preserved.

## 2. Dense dynamics determines dynamics on the completed image

The older exact stage interface also benefits from the target-generic
metric argument in section 4. The draft
`CurrentStageDenseTwoStepCertificate.toCauchyTwoStepCertificate`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:1077`)
specializes `CurrentCarrierFormCertificate.toTwoStepCertificateOfDense` to
the existing stage transport and then applies it to each supplied source
Cauchy class. Its draft `.toBridge` at `:1099` adds the derived probe pin.
The earlier duplicate pairing-limit proof has been removed from the draft.
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

The draft `CurrentCarrierFormCertificate.toBridgeOfDense`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:1064`)
instead takes the existing completed form certificate and a two-step equation
only on embedded source stages. Those images are arbitrary completed GNS
vectors, not necessarily constant rational GNS streams. The proof proceeds as
follows; all new declarations remain unverified.

1. `CurrentCarrierFormCertificate.distance_preserving` (same module `:1023`)
   expands squared differences using `RCBilinearDifference.difference_diagonal`
   (`lean/YMGap/Continuum/RCBilinearDifference.lean:19`) and rewrites the four
   pairings. No linearity hypothesis on the map is added.
2. `GNSTransferMetric.transfer_sub`
   (`lean/YMGap/Continuum/GNSTransferMetric.lean:97`) derives difference
   preservation from self-adjointness and pairing nondegeneracy.
   `transfer_nonexpansive` (same module `:113`) then derives pairwise distance
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
implements steps 1--4 via the new generic `GNSTransferMetric.maps_eq_of_dense`
(`lean/YMGap/Continuum/GNSTransferMetric.lean:124`). That lemma uses an arbitrary
GNS destination and a source `DistanceData`, so it is not tied to the ordinary
Wilson form or an assumed continuum-existence package. Quotient induction
proves an equality; it does not
select quotient representatives as data. Independent Sol source review found
the approximation directions and certificate types consistent, with no added
range/density premise. This is not an elaboration or axiom check.

Thus the stronger pending reduction leaves static completed form/vacuum
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

## 7. Residue and verification boundary

The bridge still takes `H : ContinuumYMExistence mu`, a selected
`WilsonGNSData`, and a `WilsonTimeTranslationPin` as parameters
(`CurrentCarrierBridge`, bridge module `:953`). Building this conditional
transport cannot itself construct those parameters. The all-vector canonical
range section (`CanonicalRangeSectionCertificate`, same module `:1635`),
same-measure OS realization, scaling control, physical Hamiltonian,
nontrivial continuum theory, and every-group Clay theorem remain open.

The existing external Lake process `46993` and its Lean child `60253`
(`BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows/Row64.lean`) were confirmed
live by process inspection during this review. No concurrent Lean check was
launched in this continuation. The previous claim that they had terminated
was invalid: sandbox-denied process access had been interpreted as process
absence. Future checks must distinguish those outcomes.

Next verification, only after the live build ends: a monitored one-worker
check/build of `GNSTransferMetric.lean`, then
`BF4WilsonSpatialUnionCanonicalGNSBridge.lean`, inspecting both modules'
printed axiom dependencies. The draft also contains the two earlier unverified
unit-probe consequences. No success or axiom-set claim is made for any of the
new declarations; the proof-status ledger and chart remain unchanged.
