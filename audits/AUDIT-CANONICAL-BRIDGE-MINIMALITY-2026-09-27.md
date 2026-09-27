# Canonical carrier bridge: two removable producer obligations

Date: 2026-09-27 UTC. Base commit: `7c2d23e`.

Status: source review and mathematical argument; the accompanying Lean draft
has **not** passed elaboration or its axiom gates. Line references into the
bridge module below refer to the reviewed working-tree draft. Other references
are to unchanged source. This report closes no checked roadmap node.

## 1. Probe orthogonality follows from static transport

`CurrentCarrierFormCertificate` preserves the pairing and vacuum
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:101`).
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
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:989`)
implements those rewrites. It uses neither a transfer equation nor a choice
of Cauchy representative. The existing `CurrentCarrierProbeCertificate`
structure and its fields are preserved.

## 2. Dense dynamics determines dynamics on the completed image

Let `F : CurrentStageCauchyFormCertificate P` and let
`C : CurrentStageDenseTwoStepCertificate P F`. For a supplied current Cauchy
stream `X`, its canonical image stream and its time-two image stream are
defined termwise by `F.transport.mapCauchy`. At every index the dense equation
says `y_n = P.op.T (P.op.T x_n)`.

For every fixed canonical test vector `z`, self-adjointness gives

```text
<z,y_n> = <T(T z),x_n>.
```

`GNSDenseCompletionLaws.fixed_input_converges`
(`lean/YMGap/Continuum/GNSDenseCompletionLaws.lean:80`) passes both pairings
to the limits of their supplied Cauchy streams. Transposing twice back gives
`<y,z> = <T(T x),z>`. Finally
`GNSDenseCompletionLaws.eq_of_pairings_equal`
(`lean/YMGap/Continuum/GNSDenseCompletionLaws.lean:38`) gives `y = T(T x)`.
Self-adjointness here is the field of the selected `TransferOperator`
(`lean/YMGap/Continuum/GNSDynamics.lean:143`); no additional continuity or
range hypothesis is inserted.

The draft `CurrentStageDenseTwoStepCertificate.toCauchyTwoStepCertificate`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:877`)
implements this argument. The draft `.toBridge` at `:1078` composes it with
the static probe argument to supply the existing `CurrentCarrierBridge`.
The original structures and field types are preserved. An independent Sol
source review checked the pairing directions and identified an elaboration
risk in implicit transposition arguments; the draft now supplies those
arguments explicitly. This review is not Lean verification.

The proposed remaining inputs are therefore the static stage form/vacuum
transport and the dense two-step equation, on a supplied canonical Wilson
datum and time-translation pin. Neither input is constructed here.

## 3. The exact rational stage interface needs an inhabitability check

`CurrentStageCauchyStagePairingCertificate.stagePairing`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean:218`)
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
`CurrentStageCauchyFormCertificate` (bridge module `:398`): its termwise
transport sends constant source streams to constant GNS streams, and its
completed pairing equation applies to those constants. Therefore the new
dense-stage reduction inherits this restriction. The more general
`CurrentCarrierCauchyFormCertificate`
already allows a map of entire streams and asks for completed pairing
equality; no rationality claim for each source stage appears in its fields.
No field has been weakened to address the restriction.

## 4. Residue and verification boundary

The bridge still takes `H : ContinuumYMExistence mu`, a selected
`WilsonGNSData`, and a `WilsonTimeTranslationPin` as parameters
(`CurrentCarrierBridge`, bridge module `:1019`). Building this conditional
transport cannot itself construct those parameters. The all-vector canonical
range section (`CanonicalRangeSectionCertificate`, same module `:1614`),
same-measure OS realization, scaling control, physical Hamiltonian,
nontrivial continuum theory, and every-group Clay theorem remain open.

The existing external Lake process `46993` and its Lean child `60253`
(`BF4PhysicalBoundaryCutoffTwoSectorRawKernelRows/Row64.lean`) were confirmed
live by process inspection during this review. No concurrent Lean check was
launched in this continuation. The previous claim that they had terminated
was invalid: sandbox-denied process access had been interpreted as process
absence. Future checks must distinguish those outcomes.

Next verification, only after the live build ends: the monitored one-worker
check of `BF4WilsonSpatialUnionCanonicalGNSBridge.lean`, followed by its
printed axiom dependencies. The draft also contains the two earlier unverified
unit-probe consequences. No success or axiom-set claim is made for any of the
new declarations; the proof-status ledger and chart remain unchanged.
