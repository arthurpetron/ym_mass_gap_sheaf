# Constructive Yang--Mills mass-gap formalization

> **Current frontier (2026-09-18 UTC):** the fixed-spacing SU(2) Wilson
> carrier now has a checked resolvent probe, strict two-step form gap, and a
> conditional canonical OS/GNS handoff.  The handoff's supplied range section
> constructively yields an exact carrier inverse and bijectivity, but neither
> the bridge nor its range section is inhabited yet.  Finite-stage Cauchy and
> form compilers now isolate the producer's metric-transport, finite-stage
> pairing, Gram, and zero/unit pin inputs.  Finite-stage pairing continuity
> now constructs the arbitrary-stream Gram field from stagewise `CReal.Equiv`
> data; a dense-stage two-step consumer transports the strict bound on
> finite-stage canonical images.
> Changing-spacing control,
> physical mass calibration, continuum QFT construction, and the all-group
> Clay endpoint remain open.

> **Research status (2026-09-18 UTC): this repository does not prove the Clay
> Yang--Mills existence and mass-gap theorem.** It contains kernel-checked
> finite-lattice and strong-coupling results, explicit proof compilers, and an
> honest ledger of the bridges that remain open.

This project is a Mathlib-free Lean 4 formalization of a constructive route
from four-dimensional lattice gauge theory to continuum quantum Yang--Mills.
The active concrete data are SU(2) BF4 lattice data. The positive
multiplicity-product conditional model and the signed exact-Haar model are
distinct; the former's gap is not a gap theorem for the latter. Existence
statements carry witnesses and explicit moduli; numerical exploration is not
part of the trusted proof.

The whole-project target remains the [Clay problem](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf):
a nontrivial continuum quantum Yang--Mills theory with the required QFT axioms
and a positive physical mass gap for each compact simple gauge group.
The [goal and execution instructions](work_plan.md#whole-project-goal-and-live-completion-map-updated-2026-09-16)
distinguish that target from the current SU(2) working case. Constructive
requirements are unchanged; classical mathematical review is encouraged as a
review aid, not as a replacement for explicit witnesses or the axiom gate.

**Latest result: the conditional canonical carrier handoff is now an exact
inverse, with a finite-stage transport compiler.**  In
[`BF4WilsonSpatialUnionCanonicalGNSBridge.lean`](lean/YMGap/Continuum/BF4WilsonSpatialUnionCanonicalGNSBridge.lean),
the supplied range-section equation yields constructive surjectivity,
preimage uniqueness, a quotient-defined inverse, both-sided inverse laws, and
an explicit bijectivity conjunction for the completed carrier.  The current
strict form gap and nonzero resolvent probe therefore transport to every
canonical vector *if* that bridge and range section are later inhabited.

This is a conditional consumer, not a fabricated OS/GNS identification:
`CurrentCarrierBridge` and `CanonicalRangeSectionCertificate` remain
uninhabited.  `CurrentStageCauchyTransportCertificate` constructs only the
canonical Cauchy stream/null descent from finite-stage metric data.  The new
`CurrentStageCauchyStagePairingCertificate.mapCauchy_pairing` theorem lifts a
finite-stage `CReal.Equiv` pairing law through the canonical and current
Cauchy limits, and `...toFormCertificate` leaves only the stage map/distance
law, stagewise pairing law, and zero/unit pins as producer data.
`CurrentStageCauchyFormCertificate` remains
available for callers that already have a completed Gram field.
`CurrentStageDenseTwoStepCertificate` handles exact
two-step transport only on finite-stage canonical images; arbitrary-limit
dynamics and probe pins remain open. The finite-stage reverse separation edge
is now constructed from explicit pairing continuity, while arbitrary-stream
range/dynamics remain open. Changing-spacing control,
physical mass calibration, continuum
QFT construction and every-group Yang--Mills remain open.  The focused check
used only `{propext, Quot.sound}` and produced no `sorryAx`; the detailed
execution record is in [`work_plan.md`](work_plan.md).

**Forward/backward physical meet, checked 2026-09-18:**
`CurrentStageMatchedPhysicalTransferJoin.stageTransfer_intertwines` composes
the existing physical dense-stage transfer law with an explicit one-step
current-to-canonical compatibility witness.  The companion
`stageTransfer_square_intertwines` composes two forward macro transfers using
a separately named two-step compatibility witness.  Thus the current
two-step gap node is not obtained by relabelling a one-step law.  Both
compatibility witnesses remain explicit, uninhabited inputs; no
current-to-canonical map or physical continuum bridge is inferred.  Focused
check: `/tmp/ym-forward-backward-corrected3.log`; the source hash is recorded
in `lean/SORRY_LEDGER.md`.  The declarations use only
`{propext, Quot.sound}`.

**Concrete physical endpoint, checked 2026-09-18:**
`BF4PhysicalConcreteCompletedEndpoint.ConcreteEndpoint.ofExisting` packages
the actual matched-stage SU(2) completed GNS carrier, macro transfer,
normalized vacuum, vacuum-complement preservation, dense inner product, and
same-object matrix coefficient.  This certificate is inhabited directly from
the finite physical constructions.  The remaining missing object is the
cross-model comparison map to the strong OS endpoint; no continuum or Clay
claim is added.  Focused check: `/tmp/ym-concrete-physical-endpoint2.log`;
source SHA-256 `3ffec48af04abe58e7541c3d114ac252dd5de6d83dfb5f2be5aa3e17aed0c5f8`.
Only `{propext, Quot.sound}` were reported.

**Finite cutoff-two non-vacuity witness, checked 2026-09-19:**
`BF4PhysicalConcreteCutoffTwoNontrivialEndpoint.cutoffTwoConcreteEndpoint`
specializes that completed endpoint to the explicit cutoff-two half-coupling
sector.  `NontrivialEndpoint.ofExisting` packages the centered closed-sector
indicator together with its checked stationary mean-zero law and strictly
positive weighted norm.  The imported
`BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction` identifies the
corresponding joint quadratic with this norm; this is a finite SU(2) witness,
not a cofinal rate, thermodynamic/continuum construction, or Clay result.
Focused check: `/tmp/ym-cutoff-two-nontrivial-final-check.log`; only
`{propext, Quot.sound}` were reported.

**Dense endpoint gap contraction, checked 2026-09-18:**
`DenseBF4MacroEndpointLiftData.toCompletedIntertwiner_physicalMacroVacuumNormGap`
contracts the explicit dense physical-to-strong lift certificate directly to
the existing uniform completed physical vacuum-complement norm gap.  The
finite map, exact distance/inner laws, macro radical law, and vacuum radical
law remain explicit inputs.  The Type-valued null modulus is constructed from
the physical representatives' two Cauchy moduli by
`GNSNullModulusRecovery.recoverNullModulus`; no dense analytic inhabitant,
continuum limit, or Clay result is inferred.  Focused check:
`/tmp/ym-dense-endpoint-recovered-modulus.log`; source SHA-256
`e8ba82112ad6a4f8f7533c755590d82efa13d9d1bdc06fc05d13bf4e87a2c697`.
Only `{propext, Quot.sound}` were reported.

**Type-modulated endpoint cross-check, verified 2026-09-18:**
`BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData`
has the same five dense laws on the Type-modulated physical completion, with
direct null-modulus transport and the same conditional strict endpoint gap.
Its focused check passed with only `{propext, Quot.sound}`; no five-law
inhabitant or continuum/Clay result is present.  Evidence:
`/tmp/ym-modulated-dense-endpoint-current.log`; source SHA-256
`323b00b49a0f0bdb4c93d011d1ac52fa8a09b87a9f8d56c195b512e70a926138`.

**Forward/backward spacing branch, checked 2026-09-18:**
`BF4PhysicalMatchedAFDynamicSpacingTailCompiler.MatchedPhysicalDynamicScalarTrajectory.physicalSpacingInverseSquareOfAFTrajectory`
transports the existing AF inverse-square spacing estimate to the exact
matched dynamic trajectory.  The target is the trajectory's literal spacing,
so this discharges the spacing-tail input consumed by the exact-log compiler
without changing the coupling, envelope, or completed family.  The
same-family physical-gap variation, local matched producer, observable pin,
and rate band remain open.  Focused check:
`/tmp/ym-spacing-tail-compiler.log`; source SHA-256
`55cac7b3f1e8ef7f578a3873a9c6bd84f7ca012f49c99e167bce7b8b9326495e`.
Only `{propext, Quot.sound}` were reported.

**Forward/backward two-sided scalar margin compiler, checked 2026-09-18:**
`BF4MatchedPhysicalAFTwoSidedMarginCompiler.MatchedPhysicalDynamicScalarTrajectory.toBlockedMarginBand`
contracts the matched cubic bounds with an explicit Type-valued lower
quadratic spacing envelope.  It produces an explicit positive floor and
ceiling for the literal matched `blockedMargin` in units of the same spacing
chart.  This is a scalar calibration of the matched blocked observable only:
it does not identify that margin with the separately completed transfer's
`physicalGap`, and it does not construct the missing gap-variation certificate,
observable pin, OS/continuum handoff, or Clay endpoint.  Focused check:
`/tmp/ym-two-sided-margin-final.log`; source SHA-256
`cf72592bc487f808b7a80a9d1f010894d83394c4138e9607a43659b2530f2e54`.
Only `{propext, Quot.sound}` were reported.

**Parallel exact-ray product audit, checked 2026-09-18:** finite-kernel
positivity, routing, and cutoff-dependent margin payment still do not produce
the exact `ExplicitTransitionProductExtension`.  Its smallest missing field is
the cofinal capacity comparison
`MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer.capacityCheck`;
the restricted-capacity product cannot be lifted to the exact compiled ray
capacity, and the global-edge-floor shortcut is ruled out.  This is the next
product-side estimate, not a completed transition-product witness.

**Forward/backward input audit, checked 2026-09-18:**
The exact-log backward node
`DynamicVacuumSectorObservablePin.exactLogRateCauchy` has two independent
inputs.  The spacing input is now supplied conditionally by the matched-AF
spacing-tail compiler above.  A repository-wide search found no inhabited
producer for `SummableRationalStepVariation family.physicalGap`; the existing
ratio/reciprocal algebra requires a positive floor on the denominator, while
the physical spacing is precisely the quantity tending to zero.  Thus the
next center frontier is a same-completed-family variation estimate for
`latticeMargin / transferSpacing`, not a relabeling of the AF rate or a bare
heat-kernel proxy.  The observable pin, rate band, projective/OS handoff,
continuum measure, full QFT structure, and all-compact-simple-group route also
remain explicit uninhabited inputs.

**Forward/backward regular-scaling meet, checked 2026-09-18:**
`DynamicVacuumSectorObservablePin.toRegScalingBand` now compiles the same
observable-connected completed-transfer rate band through the named physical
separator into `RegScalingBand`.  Its checked consequences
`toRegScalingBand_physGapMin_pos`, `toRegScalingBand_gap_survives`, and
`toRegScalingBand_gap_le_ceiling` preserve the same separator and expose the
uniform regular-real lower/upper bounds at every spacing index.  This is a
conditional bridge: the observable pin and two-sided physical rate band are
still explicit uninhabited inputs, so no thermodynamic/continuum witness or
Clay conclusion is claimed.  The compiler does not substitute the bare
heat-kernel separator.  Focused check:
`/tmp/ym-forward-backward-regband5.log`; source SHA-256
`89af408c6ad2c8210d700e962cae41edec41112ec60100e1ad3f8c2fec5b5c6b`.
Only `{propext, Quot.sound}` were reported.

The reverse finite-stage edge is now named explicitly as
`CurrentStagePairingSeparationCertificate`.  Its checked consumer,
`CurrentStagePairingSeparationCertificate.stageClass_eq_iff_current_eq`,
proves the exact two-way compatibility for transported stage classes when
that separation datum is supplied.  The constructor
`CurrentStagePairingSeparationCertificate.ofExistingPairingContinuity` now
builds that datum from the generic Cauchy-stream pairing-continuity theorem;
the remaining uninhabited inputs are the finite-stage transport/form pins and
the arbitrary-stream canonical range/dynamics bridge.

With that constructed certificate and the finite-stage dynamic pin, the checked consumer
`CurrentStageDenseTwoStepCertificate.twoStep_fixed_stage_eq_zero` now excludes
canonical two-step fixed points among transported finite stages, assuming the
same explicit current vacuum-orthogonality premise.  The convenience theorem
`twoStep_fixed_stage_eq_zero_of_existing_pairing_continuity` supplies the
constructed separation automatically.  This remains conditional and
finite-stage; arbitrary canonical Cauchy vectors still require the dynamic
density/range bridge.

The finite-window operator realization below is now a historical checkpoint.

The entries below are historical checkpoints. Their next steps and open
items describe the status then; use the latest result above for current status.

**Previous result: bounded Wilson observables recover the SAME vacuum correlations.**
Time-zero multiplication is now proved symmetric and linear on the existing
completion, including real scalars supplied with explicit moduli. Applying
it to the existing vacuum gives the original loop state. Consequently
`<U, M_L T_n M_K U>` is exactly the original Wilson time correlation;
subtracting its vacuum means gives the existing connected scalar and decay
bound. The action, state space, time operator and vacuum are unchanged.

This remains fixed-spacing, small-nome SU(2). General multi-time observable
realization, full coverage, canonical Hilbert/OS/QFT, changing-spacing control,
physical mass calibration and every-group continuum construction remain open.
Four focused checks passed all 24 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree audit ran. See the
[proof and remaining boundary](audits/AUDIT-WILSON-SPATIAL-UNION.md#symmetric-linear-observables-and-the-same-vacuum-correlations).

**Previous result: time-zero Wilson multiplication acts on the SAME OS completion.**
For every supplied finite spatial loop and spin, multiplication now has a
proved bound in the original reflected form, retaining the full heat action.
It descends to the existing spatial-union completion, including streams with
unbounded support, with explicit tolerance `epsilon/(characterBound spin+1)`.
The squared-distance cap depends only on spin (four for the fundamental
character). No ordinary Haar norm is substituted for the OS norm.

This is fixed-spacing, small-nome SU(2), alongside the already proved
two-step strict bound and nonzero excitation on this carrier. Full observable
representation laws, canonical Hilbert/OS/QFT realization, changing-spacing
control, finite physical mass and every-group continuum construction remain
open. Five focused checks passed all 35 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree audit ran. See the
[proof and remaining boundary](audits/AUDIT-WILSON-SPATIAL-UNION.md#bounded-time-zero-wilson-multiplication-on-the-same-completion).

**Previous result: genuine quaternion Haar identities identify the SAME Wilson states.**
A finite source identity tested against supported Haar insertions now
transports to the actual centered charts and descends to equality in the
existing completion. The proof retains the full interacting action and
partition. As a concrete sphere-dependent application, following a physical
link and immediately returning along it gives the same state as constant two.

This extends the preceding coefficient-polynomial result; it does not
identify ordinary Haar L2 with the reflected OS space or define products
on arbitrary OS-null states. Full observable coverage, canonical Hilbert/
OS/QFT realization, changing-spacing control, finite physical mass and
every-group continuum construction remain open. Four focused checks passed
all 23 public axiom gates within `{propext, Quot.sound}`; no root/full-tree
audit ran. See the [proof and remaining boundary](audits/AUDIT-WILSON-SPATIAL-UNION.md#source-haar-identities-and-an-actual-backtracking-loop).

**Previous result: one finite source identity identifies states on the SAME Wilson carrier.**
An exact coefficient-polynomial identity on the finite chronological source
now transports through the actual placements to every centered chart.
The previously proved observable descent then gives literal equality of
the existing embedded states. Both source support guards are retained;
no separate equality at every regulator is assumed.

This removes the source-identity transport obligation, not all identities
valid only on the unit-quaternion sphere. Arbitrary OS-null multiplication,
canonical observable/state coverage, full Hilbert/OS/QFT realization,
changing-spacing control, finite physical mass and every-group continuum
construction remain open. Two focused checks passed all 8 public axiom
gates within `{propext, Quot.sound}`; no root/full-tree audit ran. See the
[proof and remaining boundary](audits/AUDIT-WILSON-SPATIAL-UNION.md#one-finite-source-identity-reaches-the-same-completed-states).

**Previous results: normalized positive response and observable identities on the SAME Wilson carrier.**
An explicitly constructed inverse square root of the actual norm now
normalizes the existing vector. Its two-step response has a proved rational
lower bound above zero and upper bound below one. The certificate returns
the vector, orthogonality, norm one, the original time-operator equality,
both bounds and the scalar Cauchy modulus as data.

Exact original-polynomial equality on the regulator diagonal also now
implies literal equality of the embedded states. The proof retains the
same reflected test, full action and partition. As a concrete application,
the two orders of a polynomial product give the same state; this does not
define multiplication on arbitrary OS-null classes.

This is **fixed-spacing SU(2) at nome 1/1024**, not a continuum mass gap.
Canonical observable/state identification, full Hilbert/OS/QFT realization,
changing-spacing control, finite physical mass and every-group continuum
construction remain open. The two focused checks passed 25 normalization
and 6 observable-descent axiom gates within `{propext, Quot.sound}`;
no root/full-tree audit ran. See the
[proof and next interface](audits/AUDIT-WILSON-SPATIAL-UNION.md#original-polynomial-identities-descend-to-the-same-states).

**Previous result: positive nonzero-time response of the EXISTING Wilson excitation.**
Exact comparison of the two separated plaquette probes identifies their
connected scalars under the same original action and partition, then through
their unchanged regulator limits. The existing Wilson vector therefore
inherits the positive lag-three response floor. Original time contraction
gives the same floor at lag two, without assuming one-step positivity.
The certificate returns this vector and the explicit floor
`(1/16)*(1/1024)^36` as data.

This is **fixed-spacing SU(2) at nome 1/1024**, not a continuum mass gap.
Normalized positive-response data on this carrier, full Hilbert/canonical
OS/QFT realization, changing-spacing control, finite physical mass and
every-group continuum construction remain open. Two focused checks passed
all 12 public axiom gates within `{propext, Quot.sound}`; no root/full-tree
audit ran. See the
[proof and remaining joins](audits/AUDIT-WILSON-SPATIAL-UNION.md#positive-response-of-the-existing-wilson-excitation).

**Previous result: actual vacuum projection and all-vector relaxation on the SAME Wilson carrier.**
Real scalar multiplication with supplied explicit moduli now constructs the
unit projection and orthogonal centering. Each supplied vector representative
gives a computed rate for its original time orbit to converge to its projection;
the two-step fixed space is exactly the image of that projection. Connected
scalar moments are exactly
the time pairings of these same centered vectors, with geometric squared
correlation decay and the original dense Wilson-moment pin.

These are **fixed-spacing, small-nome SU(2)** results. No representatives or
moduli are selected from arbitrary quotient reals. Full Hilbert and canonical
OS/QFT realization, positive nonzero-time response on this Wilson carrier,
changing-spacing control, finite physical mass and every-group continuum
construction remain open. Six focused checks passed the constructive axiom
gate; no root/full-tree audit ran. See the
[proof and remaining joins](audits/AUDIT-WILSON-SPATIAL-UNION.md#real-action-vacuum-projection-and-all-vector-relaxation).

**Previous result: rational linear geometry and represented limits on the SAME Wilson carrier.**
Addition and signed rational scaling now act on the actual Wilson union
completion, with computed moduli. Its completed form is bilinear and
separates vectors; the original time maps are rational-linear. The squared
norm of the actual difference is proved to be the limit of the original
distances, supplying constructive limits for Cauchy rows whose representatives
and moduli are given. Time commutes with those limits, and the unit-orthogonal
time orbit converges to the existing zero vector at a computed geometric rate.

This is **fixed-spacing, small-nome SU(2)** infrastructure. It does not choose
representatives for arbitrary quotient-valued sequences or establish full
real Hilbert/OS/QFT structure. Real scalar action, canonical observable/state
identification, changing-spacing control, finite physical mass and every-group
continuum construction remain open. Five focused checks passed the
constructive axiom gate; no root/full-tree audit ran. See the
[proof and next joins](audits/AUDIT-WILSON-SPATIAL-UNION.md#rational-linear-geometry-and-represented-limits-follow-up).

**Previous result: quantitative time decay on the SAME Wilson spatial union.**
Original time balance now passes through the actual union pairing limits,
so time preserves the unit complement. The existing two-step form bound
becomes a one-step squared-norm bound and iterates:
`B(T_n x,T_n x) <= q(w)^n B(x,x)` whenever `B(x,U)=0`.
Sharp Cauchy--Schwarz also gives squared mixed-correlator decay. A supplied
Cauchy representative computes an explicit tolerance threshold, with no
choice of quotient representative and no whole-stream support bound.

These are **fixed-spacing, small-nome SU(2)** results, not a continuum
Hamiltonian gap or a one-step positivity theorem. The rate depends on nome;
full linear/Hilbert structure, canonical OS/QFT realization, changing-spacing
control, physical mass calibration and every-group construction remain open.
Both focused checks passed the constructive axiom gate; no root/full-tree
check ran. See the [proof and remaining joins](audits/AUDIT-WILSON-SPATIAL-UNION.md#time-balance-and-quantitative-decay-follow-up).

**Previous result: one coherent Wilson spatial-union completion with a nonvacuous strict bound.**
Enlarging a source box now provably preserves the original limiting Wilson
form and distance. This constructs one completion of the existing finite-base
Wilson windows, allowing Cauchy streams with unbounded support bases and time
radii. Its actual time maps retain the supplied moduli, and the strict bound
`B(x,T_2 x) <= q(w) B(x,x)` holds throughout its unit complement.

The original positive-norm excitation maps into this SAME carrier. Its form
is positive definite, and a unit-orthogonal vector fixed by two time steps
must be zero. These are **fixed-spacing, small-nome SU(2)** results, not a
continuum Hamiltonian gap. Full linear/Hilbert structure, full gauge-observable
coverage, canonical OS/QFT realization, changing-spacing control, finite
physical mass calibration and every-group construction remain open.
Eleven focused serialized checks passed all 152 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[spatial-union proof and remaining joins](audits/AUDIT-WILSON-SPATIAL-UNION.md).

**Previous result: a strict two-step form bound on the SAME Wilson completion.**
Original time-separated Wilson correlations now have a geometric bound with
one shared action and partition. Fixed-size probe supports keep the amplitude
independent of time separation and lattice regulators. The actual centered
moment inequalities remove that amplitude before passage to arbitrary
Cauchy streams, proving `B(x,T_2 x) <= q(w) B(x,x)` for EVERY vector
orthogonal to the embedded unit, with `0 < q(w) < 1` under the stated guards.

The rate depends on nome but not the vector or positive source base. A concrete
certificate at nome `1/1024`, base one, joins this bound to the existing
nonzero centered excitation and its positive norm floor. This is a
**fixed-spacing, small-nome SU(2) strict form bound**, not a continuum
Hamiltonian mass gap. Base-union coherence, full Hilbert/OS/QFT realization,
changing-scale control, physical mass calibration and every-group construction
remain open. Seven focused serialized checks passed all 61 public gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[same-carrier proof and remaining causal joins](audits/AUDIT-WILSON-COMPLETED-STRICT-BOUND.md).

**Previous result: original discrete time on the SAME Wilson completion.**
Exact window stationarity, reflected positivity and a lag-independent scalar
cap now prove nonexpansiveness of the actual Wilson time advance. It descends
to the existing completion, retaining every supplied Cauchy modulus. The
completed maps obey the time-addition law, fix the embedded original unit,
preserve its orthogonal sector, and retain the original dense correlators.
Even-time quadratic forms are nonnegative and bounded by the original squared norm.

This is **fixed-spacing, small-nome SU(2)**, not a strict gap or continuum
theory. One-step positivity is not asserted. The next strict-gap task is a
decay estimate for this carrier's own time-separated connected Wilson
correlations; the older plaquette-only gap is not silently transferred.
Full Hilbert/OS/QFT realization, changing-scale control, physical mass and
every-group continuum construction remain open. Seven focused serialized
checks passed all 70 public gates within `{propext, Quot.sound}`; no root/
full-tree check ran. See the [proof, five-front parallel map and next join](audits/AUDIT-WILSON-ORIGINAL-COMPLETED-TIME.md).

**Previous result: an actual nonzero centered vector on the Wilson completion.**
Rational approximations of the original mean now construct a vector in the
SAME enlarged Wilson completion, with an explicit Cauchy modulus. Its pairing
with the embedded unit is zero; its mixed pairings are exactly the connected
original reflected form. The plaquette vector's squared norm inherits the
positive local-star floor. A concrete certificate discharges all guards at
nome `1/1024` and source base one, returning a nonzero unit-orthogonal vector.

The completed pairing also separates zero: zero squared norm is equivalent
to equality with the actual completed zero. This is **fixed-spacing SU(2)**,
not a continuum excitation or a physical-vacuum identification. Full completed
linear/Hilbert structure, original time and the strict bound on this enlarged
carrier, changing scale, physical mass, full OS/QFT and every-group continuum
construction remain open. Six focused serialized checks passed all 59 public
gates within `{propext, Quot.sound}`; no root/full-tree check ran. See the
[same-carrier excitation proof and next obstruction](audits/AUDIT-WILSON-CENTERED-EXCITATION.md).

**Previous result: the same Wilson completion pairing and a positive plaquette variance.**
The original limiting reflected form now supplies an actual squared seminorm,
with a proved triangle estimate and null replacement. Explicit common-window
embeddings give its intrinsic carrier. Quantitative pairing continuity then
constructs the pairing on its represented Cauchy completion, preserving the
original form on embedded expressions, symmetry, nonnegativity, the unit norm
and Cauchy--Schwarz.

In parallel, the original ordered plaquette is identified with a Wilson loop
at every spin. Exact first/second moment pins transfer its existing positive,
nome-dependent variance floor to the SAME Wilson scalar limit. This is not
yet a centered vector on the enlarged completion or a transfer of the old gap.

These are **fixed-spacing, small-nome SU(2)** results. Full completed linear/
Hilbert structure, original time and the strict bound on this enlarged carrier,
full OS/QFT realization, changing scale, physical mass and every-group
continuum construction remain open. Seven focused serialized checks passed
all 86 public gates within `{propext, Quot.sound}`; no root/full-tree check ran.
See the [proof and five-front parallel joins](audits/AUDIT-WILSON-COMPLETION-AND-PLAQUETTE-VARIANCE.md).

**Previous result: a consistent limiting reflected form for original Wilson windows.**
The SAME three-regulator Wilson limit is now normalized and rational-linear.
Its mixed reflected form is symmetric, positive on the diagonal and satisfies
sharp Cauchy--Schwarz. Null differences can be replaced in either argument.
Exact centered-window compatibility survives both the joint time/cutoff and
spatial limits: both observable offsets move with the reflection plane.

Parallel finite algebra, reflection, positivity and window-padding proofs
thus join into laws of one actual limiting form. This is **fixed-spacing,
small-nome SU(2)**, not the enlarged carrier's completion or strict bound.
Full observable coverage, canonical OS/QFT realization, physical scaling,
continuum nontriviality and the every-group theorem remain open. Six focused
serialized checks passed all 38 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[proof, next joins and five-front parallel map](audits/AUDIT-WILSON-LIMITING-REFLECTED-FORM.md).

**Previous result: original Wilson expectations after joint lattice-regulator removal.**
Signed multi-time Wilson expressions now have an explicit CReal limit as
spatial margin, heat cutoff and external time depth recede. Exact translation,
a placement-independent ordered-word cap and literal fixed-box locality give
the original-action spatial comparison. A computed pivot combines it with
the time/cutoff modulus; no mixing estimate uniform across widths is assumed.
The previous joint expectations converge to this SAME limit, and complete
signed reflected products remain nonnegative.

This is **fixed-spacing, small-nome SU(2)**. The enlarged reflected form's
algebra, quotient/completion and strict bound, full OS/QFT identification,
physical scaling and the every-group continuum theorem remain open. Seven
focused serialized checks passed all 65 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[three-regulator proof and next mathematical join](audits/AUDIT-WILSON-THREE-REGULATOR-LIMIT.md).

**Previous result: reflected positivity for original multi-time Wilson expressions.**
Finite signed sums and products of closed spatial loop characters now have
an exact common-window realization in the original action. Literal reflection
and one-sided support connect the complete reflected product to the existing
finite-chain positivity theorem. The SAME fixed-width, fixed-cutoff time limit
inherits that positivity, with an explicit time modulus independent of the
cutoff stage but dependent on nome, width and observable.

This supplies a larger reflected observable domain, **not** an extension of
the old completed-carrier strict bound. Joint time/cutoff removal and the
concrete spatial placement/locality/cap proofs are the next separable tasks;
full OS/QFT identification, changing-scale control, physical mass and the
every-group continuum theorem remain open. Five focused checks passed all
35 public axiom gates within `{propext, Quot.sound}`. Checks were serialized
under the safe-build procedure; no root/full-tree check ran. See the
[proof and parallel-front map](audits/AUDIT-WILSON-WINDOW-REFLECTED-POSITIVITY.md).

**Previous result: original spatial Wilson loops, with exact action and time-limit realization.**
Arbitrary closed ordered spatial Wilson words now pass through the same
temporal gauge sweep as the complete original action. Signed products of
such loop characters retain every shared link and action factor. A concrete
six-link rectangle is pinned to the existing plaquette-only nonrecoding
example; this is a pointwise obstruction, not a claim about OS-norm density.

Literal source placement and cancellation of the same partition identify
original loop expectations with the existing fixed-width polynomial time
state, with an explicit Cauchy modulus. That modulus is uniform in the late
heat stage, **not** in nome, spatial width or observable. The existing dense
plaquette presentations also have an explicit product preserving their source
polynomials, placement, time and base inclusion.

This is not an extension of the strict bound to the larger Wilson carrier.
The reflected carrier/limit join, full Hilbert/OS/QFT identification, changing
scale, physical mass and every-group continuum construction remain open.
Eight focused checks passed all 78 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[original-Wilson proof and five-front parallel map](audits/AUDIT-ORIGINAL-SPATIAL-WILSON-REALIZATION.md).

**Previous result: an actual unit-norm excitation with a positive strict response interval.**
Real scaling by a supplied constructive real and its explicit Cauchy modulus
now acts on the same spatial union carrier. Scalar/vector representative
independence, the scalar algebra laws, and compatibility with original time,
centering, unit projection and reduced inverse are proved.

Applying a computed inverse square root to the actual excitation norm gives
a vacuum-orthogonal vector `v` with `B(v,v)=1` and explicit rational bounds
`0 < lower <= B(v,T_2 v) <= upper < 1`. The construction returns the vector,
bounds, response real and response modulus. No eigenvector is assumed.

This is **fixed-spacing SU(2) at nome 1/1024**, not physical mass calibration.
Full Hilbert/OS/QFT identification, original observable coverage, full spatial
symmetry, changing-scale control, continuum survival and every-group physical
construction remain open. No modulus for an arbitrary legacy quotient real
is selected. Six focused checks passed all 56 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[normalized-excitation checkpoint](audits/AUDIT-SPATIAL-UNION-NORMALIZED-EXCITATION.md).

**Previous result: a positive nonzero-time response on the same completed carrier.**
The original centered plaquette now has an explicit positive connected-response
floor at physical lattice lag three and at lag two. The proof embeds the older
full finite action into the current selected-chain action, bounds their signed
covariance difference, and makes that error vanish on the existing unchanged
diagonal. It retains the actual excitation, pairing, time and cutoff; it does
not identify different completed carriers or assume the desired response.

The floor is `(1/16)*(1/1024)^36`, with a computed comparison modulus. This
closes the fixed-spacing response transport highlighted by the parallel review.
Full real/Hilbert/OS/QFT structure, signed/axiswise spatial translations,
changing-scale control, physical mass calibration, continuum survival and
actual constructions for every compact simple group remain open.

Seven focused checks passed all 81 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[positive-response proof and five-front parallel map](audits/AUDIT-SPATIAL-UNION-POSITIVE-RESPONSE.md).
This is **fixed-spacing SU(2) at nome 1/1024**, not a continuum mass-gap theorem.

**Previous result: a constructive reduced inverse and spatial symmetry on the same completed carrier.**
The actual two-step transfer now has a bounded inverse for `I-T_2` on the
unit complement. Its geometric-series construction returns an approximation
modulus; its squared-norm bound is explicitly `(1-q(w))^(-2)`. Rational
linearity, self-adjointness and commutation with actual discrete time are
proved. No stronger coupling guard or alternative carrier is used.

Parallel work proves positive diagonal spatial translations preserve the
actual pairing and commute with time. This is not yet the full spatial
translation group. An odd/even comparison also transfers a supplied lag-three
response floor to lag two; the required original-action comparison supplying
that floor remains open. The old response has lag three, not lag two.

This remains **fixed-spacing, small-nome SU(2)**. Full real/Hilbert/OS/QFT
structure, changing-scale control, physical mass calibration and actual
constructions for every compact simple group remain open. Six focused checks
passed 92 public axiom gates within `{propext, Quot.sound}`; no root/full-tree
check ran. See the [proof checkpoint and parallel-work map](audits/AUDIT-SPATIAL-UNION-RESOLVENT.md).

**Previous result: computed row limits and quantitative relaxation on the same spatial union carrier.**
Supplied Cauchy representatives now have a computed diagonal limit with an
explicit outer modulus. Original physical time and centering commute with
these limits; the existing unit complement is closed under them. The actual
time orbit converges to its unit projection with squared-distance rate
`q(w)^n` and a computed tolerance threshold. This does not select representatives
for arbitrary quotient-valued sequences or assert full Hilbert completeness.

The strict completed bound and a nonzero excitation were already proved.
A parallel review separates the remaining work: full Hilbert/OS/QFT structure,
original-action spatial/spacing comparison, physical time/mass calibration,
and actual constructions for other compact simple groups. The positive norm
floor is not yet a positive nonzero-time response or continuum nontriviality.
The existing AF guard obstruction remains. This is **fixed-spacing,
small-nome SU(2)**, not a continuum mass-gap theorem.

Six focused module checks passed all 78 public axiom gates within
`{propext, Quot.sound}`; no root/full-tree check ran. See the
[proof checkpoint and parallel dependency map](audits/AUDIT-PARALLEL-FRONTIERS-2026-09-16.md).

**Previous result: exact centering and stationary-sector characterization on the same spatial union carrier.**
Actual addition and rational scaling now descend with explicit moduli and
bilinear laws. A computed unit projection splits every vector into its
unit component and its orthogonal part. Centered time pairings equal the
existing connected moments. The checked strict bound then proves
`T_1 x = x` and `T_2 x = x` each equivalent to `unitProjection x = x`;
the unit coefficient uniquely determines a stationary vector.

This remains **fixed-spacing, small-nome SU(2)**. No quotient scalar
representative is selected, and no unrestricted real-module or metric
completeness theorem is asserted. Full gauge observable coverage, spatial
translation/OS/QFT identification, physical scaling, continuum control and
the all-group target remain open. The AF small-nome-guard obstruction is
unchanged. Six focused checks passed all 114 public axiom gates; no
root/full-tree check ran. See the
[union centering and stationary-sector audit](audits/AUDIT-SPATIAL-UNION-STATIONARY.md).

**Previous result: one spatial union carrier with a strict completed-sector bound and a concrete nonzero excitation.**
The existing finite-base plaquette-character presentations now share one
Cauchy carrier, allowing streams with growing support bases. Its actual
spatial-limit pairing is positive definite and satisfies Cauchy--Schwarz.
Original physical time preserves the unit complement, where
`B(v,T_2 v) <= rho(w)^2 B(v,v)` and the corresponding one-step squared-norm
bound hold for every completed vector. Fixed-base maps preserve pairings
and time; the original centered plaquette remains nonzero with the same
connected correlators. A closed instance at `w = 1/1024` supplies every
coupling guard and an actual nonzero vector in this sector.

This is **fixed-spacing, small-nome SU(2)**, not the continuum theorem.
General completed linear/centering laws, metric completeness, full gauge
observable coverage, spatial-translation/OS/QFT identification, continuum
control and the all-group target remain open. The old small-nome guard is
already proved incompatible with the supplied AF chart; that analytic
obstruction is not removed here. Fifteen focused checks passed all 180
public axiom gates; no root/full-tree check ran. See the
[spatial union-sector audit](audits/AUDIT-SPATIAL-UNION-SECTOR.md).

**Previous result: the strict bound holds on the completed spatial-limit unit complement, with a nonzero excitation.**
The actual spatial-limit pairing now extends to its own Cauchy quotient,
with explicit moduli, positive definiteness and Cauchy--Schwarz. For every
completed vector orthogonal to its normalized unit,
`B(v,T_2 v) <= rho(w)^2 B(v,v)`. Physical time preserves this sector;
its one-step squared norm has the same strict bound. Rational approximations
to the original plaquette mean construct an actual centered vector with
squared norm at least `starRatio(w)>0`. Its time correlations equal the original
connected spatial limits. No nonzero stationary vector exists in this sector.

This is **fixed-spacing, small-nome SU(2) progress**, with a common rate
and excitation floor across positive base sizes. The separate fixed-base
completions are not yet one union carrier. General completed linear/centering
laws, metric completeness, full Hilbert/OS/QFT reconstruction, physical
spacing control, continuum nontriviality and the all-group goal remain open.
Twelve focused checks passed all 110 printed public axiom gates, including
one existing module whose scalar helper was exported. No root/full-tree
check ran. See the
[completed spatial-sector audit](audits/AUDIT-SPATIAL-COMPLETED-SECTOR.md).

**Previous result: a strict, base-independent two-step bound on the dense spatial-limit unit complement.**
Separate fixed-size boxes around the actual two probes give connected
decay with a coupling-dependent rate and a prefactor independent of time
separation and all three regulators. This estimate passes to the original
spatial-limit reflected form. Its even-moment inequalities eliminate the
observable-dependent prefactor, proving `B(x,T_2 x) <= rho(w)^2 B(x,x)`
for dense presentations orthogonal to the unit, with `0 < rho(w)^2 < 1`.
Enlarging the base box around unchanged words now preserves that form.
The limiting seminorm also has its own explicit-Cauchy quotient and
physical-time action, with a nonzero fixed unit.

This is **fixed-spacing SU(2) progress under explicit small-nome guards**.
The bound has not yet been extended to every vector of this new completed
carrier; a nonzero centered completed excitation and a single union carrier
remain to be constructed. Full Hilbert/OS/QFT reconstruction, physical
spacing control, continuum nontriviality and the all-group target remain
open. Twelve focused checks passed all 139 public axiom gates; no root or
full-tree check ran. See the
[spatial dense-gap and coherence audit](audits/AUDIT-SPATIAL-DENSE-GAP-AND-COHERENCE.md).

**Previous result: actual reflected correlators have explicit spatial limits, with a positive plaquette variance.**
For fixed signed physical presentations, the original reflected product now
has a geometric cross-box comparison bound, uniform in heat cutoff and time
buffer. A computed spatial pivot combines this bound with the existing
cutoff/time modulus at just one box. This constructs a `CReal` limit of the
literal three-regulator diagonal, with explicit Cauchy data. Removing
cutoff/time first gives the same scalar; the observation chart does not
change it. The original plaquette variance retains its strictly positive,
coupling-dependent local floor after this spatial passage.

This is **small-nome SU(2) scalar-limit progress**, not a continuum theory or
an infinite-volume gap. Compatibility between different base presentations,
the limiting form's own quotient/completion, width-independent connected
decay, physical spacing control and the all-group target remain open.
Seven focused checks passed all 59 public axiom gates; no root/full-tree
check ran. See the [spatial-limit audit](audits/AUDIT-REFLECTED-SPATIAL-LIMIT.md).

**Previous result: original plaquette means in different spatial boxes have a geometric comparison bound.**
Translate the smaller action into the larger Haar carrier, keeping its exact
partition. A spatial shift by `d` and time shift by `2*d` align both time
boundaries. Every omitted factor is then spatially distant, including
temporal plaquettes outside the smaller spatial box. The signed boundary
estimate gives an error `A(w,spin) * rho(w)^(r+1)`, uniform in heat cutoff,
time buffer, base size and further outer padding. The same bound survives
heat-cutoff removal. Its small-nome conditions are explicit and proved at
the existing `w=1/1024` pilot.

This is a **one-plaquette cross-width estimate**, not general reflected
correlation decay or a continuum gap. Next: extend comparison to the actual
reflected probe products and combine it with the fixed-width joint limits.
Unrestricted-nome spatial control, a width-independent decay rate, spacing
control, full Hilbert/OS/QFT reconstruction and the all-group target remain
open. Seven focused checks passed the constructive axiom gates; no root or
full-tree check ran. See the
[aligned-box comparison audit](audits/AUDIT-ALIGNED-SPATIAL-PLAQUETTE-COMPARISON.md).

**Previous result: recentered plaquette excitations retain a positive variance floor independent of box size.**
The proof compares only the at-most-six heat factors touching one actual
link, retaining every other action factor and the original partition.
Exact SU(2) character cancellation then bounds the interacting variance
below by the explicit positive `starRatio(w)`. This same bound survives
joint heat-cutoff/time-boundary removal and is the squared-norm floor of
an actual centered vector in each original completed carrier. Computed
spatial translations put every probe endpoint arbitrarily far from the
spatial boundaries without changing its time distance.

The constant depends on coupling. **This is a volume-independent
nontriviality estimate, not a volume-independent spectral gap.** Comparing
the states in different boxes, a width-independent decay rate, spacing
control, full Hilbert/OS/QFT reconstruction and the continuum/all-group
target remain open. Four focused module checks passed all 39 public gates;
no root/full-tree check ran. See the
[local-variance audit](audits/AUDIT-RECENTERED-LOCAL-VARIANCE.md).

**Previous result: the actual completed unit complement has a strict form bound and a nonzero excitation.**
Rational approximations to the original plaquette mean construct an actual
orthogonal vector with an explicit positive norm floor. Its physical-time
pairings are exactly the original connected correlators. The prefactor-free
two-step inequality now holds for **every completed vector orthogonal to the
same unit**; actual physical time preserves that sector. The rate is below
one at fixed coupling and spatial width, not uniformly over those parameters.

This remains **fixed-spatial-width SU(2) progress**, not a complete Hilbert/OS
theory or a continuum mass gap. Next: recenter local probes for genuine bulk
exhaustion and prove spatial-boundary comparison and width-independent decay.
General completed linear/centering and Hilbert structure, spacing control,
physical mass calibration and the continuum/all-group target remain open.
Six focused module checks passed 58 public axiom gates; no root/full-tree check
ran. See the [completed-sector audit](audits/AUDIT-JOINT-COMPLETED-CENTERED-GAP.md).

**Previous result: reflected correlators survive heat-cutoff removal, preserving the strict scalar bound.**
At fixed spatial width and nome, the original reflected correlators now
have a constructed joint heat-cutoff/time-boundary limit. Both orders of
limits give the same scalar, with explicit moduli. The centered physical
moment retains its geometric envelope and the prefactor-free inequality
`M(2,x,x) <= q^2 * M(0,x,x)`. It is also identified with the limit of literal
finite connected expectations sharing **one action and partition**.

This is a cutoff-removed scalar result, not an identification of the
cutoff-dependent completed spaces. Next: construct the limiting reflected
seminorm and its own physical-time carrier. Spatial/spacing control,
nonconstant excitations, full QFT reconstruction and the Clay theorem remain
open. Four focused checks passed all 37 public axiom gates; no root/full-tree
check was run. See the [reflected joint-limit audit](audits/AUDIT-FIXED-SPATIAL-REFLECTED-JOINT-LIMIT.md).

**Previous result: strict contraction on the actual completed unit complement at fixed cutoff.**
For fixed nome, spatial width and retained cutoff, the SAME physical-time
map now satisfies `B(v,T_2 v) <= q^2 * B(v,v)` and
`B(T_1 v,T_1 v) <= q^2 * B(v,v)` on the original unit-orthogonal carrier,
with the computed `0 <= q < 1`. Reflected probes are pinned to the original
separated-window covariance; actual even-time moment inequalities remove
its presentation-dependent prefactor. The resulting norm-relative estimate
passes to supplied Cauchy streams and their quotient without representative
choice or a uniform coefficient cap.

The rate is independent of retained heat stage but depends on nome and
spatial width. **This is not a continuum mass-gap theorem.** Nonconstant
excitations, full Hilbert/OS reconstruction, joint cutoff/time passage,
spatial/spacing control and physical mass calibration remain open. Next is
the reflected common-chart cutoff/time limit, keeping the original action
and partition. Five focused checks passed all 35 public axiom gates; no
root/full-tree check was run. See the
[centered strict-bound audit](audits/AUDIT-FIXED-SPATIAL-CENTERED-STRICT-BOUND.md).

**Previous result: connected correlation decay between separated finite windows.**
For the original fixed-spatial SU(2) transfer, the connected expectation of
two signed polynomial windows is bounded by `4 * cap(P) * cap(Q) * q^g`,
where `g` counts the transitions between their endpoints. Joint and marginal
expectations retain the **same full action and partition**. Exact contraction
of the first window, transfer-bracket decay, and signed residual cancellation
prove the bound without dividing by an observed or residual mass.

The rate depends on nome and spatial width; the estimate is uniform in
external boundary lengths and late heat cutoff for fixed probes. At that
checkpoint it was not a strict reflected-norm or physical mass-gap theorem.
The next step was to identify the reflected physical-time probes with these
separated windows and pass the bound to their existing connected limit.
Five focused checks passed all 15
public axiom gates; no root/full-tree check was run. See the
[separated-covariance audit](audits/AUDIT-FIXED-SPATIAL-SEPARATED-COVARIANCE.md).

**Previous result: actual unit projection, centered physical time and same-partition connected correlators.**
Real scaling with explicit Cauchy data now constructs projection onto the
original fixed unit. Subtracting that projection gives its orthogonal
complement and an exact norm decomposition. The SAME physical-time map
preserves this complement and commutes with centering. Its centered pairing
equals the constructed limit of a **finite connected expectation with one
shared action and partition** for the joint moment and both marginals.

This is **fixed-nome, fixed-width, fixed-cutoff SU(2) progress**, not a
strict-gap theorem. The latest finite estimate controls separated windows;
its reflected physical-time placement and limit consumers remain open.
Metric completeness, full Hilbert/OS reconstruction, nonconstant excitations,
vacuum isolation, the reflected-norm strict bound, joint limits and continuum
Clay closure remain open. Seven focused checks passed all 97 public axiom
gates; no root/full-tree check was run. See the
[centering and connected-correlator audit](audits/AUDIT-FIXED-SPATIAL-CENTERED-CORRELATORS.md).

**Previous result: rational linear structure and actual squared-distance geometry on the original completed carrier.**
Addition and rational scaling now act on the SAME physical Cauchy carrier,
with explicit moduli and proved algebraic laws. Its original pairing is
bilinear, positive definite and satisfies sharp Cauchy--Schwarz. The
completed squared distance recovers the original dense distance and is
zero exactly at equal states. The SAME physical-time map is rational-linear
and contracts that distance with constant **one**.

This remains **fixed-nome, fixed-width, fixed-cutoff SU(2) progress**.
The latest result supplies real scaling with Cauchy data, projection onto
the fixed unit and actual centered correlations. Metric completeness,
full Hilbert/OS reconstruction, nonconstant excitations, vacuum isolation,
a strict gap, joint limits and continuum Clay closure remain open. Five
modules passed focused checks with all 77 public gates inside the
constructive axiom gate; no root/full-tree check was run. See the
[completed-linear audit](audits/AUDIT-FIXED-SPATIAL-COMPLETED-LINEAR.md).

**Previous result: a positive-definite completed pairing with original physical-time correlators.**
The original reflected pairing now extends to the SAME Cauchy carrier as
the physical-time maps. Its limit and representative-independence proofs
carry explicit moduli; zero diagonal means exactly the zero element.
Time balance, constant-one contraction and even-time positivity hold on
this carrier. On embedded probes, the completed time correlator equals
the constructed limit of the **original finite expectations**, retaining
the selected action and partition.

This remains **fixed-nome, fixed-width, fixed-cutoff SU(2) progress**.
The latest result adds rational linear laws and bilinearity; scalar
extension and metric completeness remain open. This is not yet a full
Hilbert/OS construction. Nonconstant excitations,
vacuum isolation, a strict gap, joint limits and continuum Clay closure
remain open. Seven modules passed focused checks with all 61 public gates
inside the constructive axiom gate; no root/full-tree check was run.
See the [completed-pairing audit](audits/AUDIT-FIXED-SPATIAL-COMPLETED-PAIRING.md).

**Previous result: genuine physical time is contractive in the original reflected seminorm.**
Incrementing each observable's distance from the reflection plane defines
the actual time shift. Its same-object time-balance identity, reflection
positivity and a lag-independent coefficient bound prove contraction with
constant **one**, without assuming a spectral gap. The shift preserves null
presentations and acts on the explicit-modulus Cauchy carrier, retaining
each supplied modulus exactly. The original unit gives a fixed element
distinct from embedded zero.

This is a **fixed-nome, fixed-width, fixed-cutoff SU(2) construction** for
the selected original action. The latest result adds a positive-definite
completed pairing and its original correlator pin; Hilbert-space laws
remain open, and a fixed unit is not an isolated vacuum. Strict contraction
on the vacuum complement, joint limit control, continuum QFT and the Clay
mass gap remain open. Seven focused checks passed all 101 public axiom
gates; no root/full-tree check was run. See the
[physical-time audit](audits/AUDIT-FIXED-SPATIAL-PHYSICAL-TIME.md).

**Previous result: a window-independent reflected pairing with sharp Cauchy--Schwarz.**
The [intrinsic reflected pairing](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIntrinsicReflectedForm.lean)
records observables by their distances from the reflection plane and computes
a common enclosing window. Changing that window provably leaves the SAME
constructed limit unchanged. The pairing is signed-rational bilinear and
symmetric, has nonnegative diagonal, and satisfies sharp Cauchy--Schwarz.
A zero-norm presentation pairs to zero with every physical probe span.

The proof retains the original selected action and partition. It neither
assumes finite stationarity nor synchronizes different CReal approximation
indices. This is a **fixed-nome, fixed-width, fixed-cutoff SU(2) intrinsic
scalar form**, not yet a completed physical OS theory. The latest result
adds genuine time-shift balance, contraction and its Cauchy-carrier descent.
The completed Hilbert structure, joint limits, continuum QFT and the physical
mass gap remain open. Six focused checks at this earlier checkpoint passed 73 public
axiom gates; no root/full-tree check was run. See the
[intrinsic-form audit](audits/AUDIT-FIXED-SPATIAL-INTRINSIC-REFLECTED-FORM.md).

**Previous result: the constructed time limit is reflection-positive on signed spatial-probe sums.**
The [reflected-window theorem](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowReflectionPositive.lean)
proves nonnegativity of the reflected form for every finite rational sum of
scheduled spatial face-character products, including all signed cross terms.
The proof factors the SAME selected original action into lower, central and
reflected-lower weights. It keeps the central weight once and uses its actual
positive certificate, without assuming the insertion or lower factor positive.

A symmetric ambient placement makes reflection send offset `j` to `2*h-j`.
The compact observable and heat cutoff therefore stay fixed while both time
boundaries recede. Positivity passes to the **existing explicit-modulus window
limit**, with no replacement state or new convergence assumption. Separately,
reflection positivity survives cutoff removal on each fixed selected chain;
these two limits have not been interchanged.

This remains a **fixed-nome, fixed-width, fixed-cutoff SU(2) time-limit result
on the spatial-probe span**. Later results supply the intrinsic scalar
pairing and contractive physical shifts on its Cauchy carrier. The completed
Hilbert structure, isolated vacuum, joint cutoff/volume/spacing control,
and the continuum Clay target remain open. Six focused checks passed
63 public axiom gates; no root/full-tree check was run. See the
[reflection audit](audits/AUDIT-FIXED-SPATIAL-WINDOW-REFLECTION.md).

**Previous result: original multi-time spatial probes reach the same constructed window limit.**
The [original-window identity](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalWindow.lean)
identifies scheduled products of signed spatial face characters with the
existing original lattice expectation, retaining the SAME selected action,
cutoff and partition. The whole-window coordinate embedding preserves all
slice and fringe coordinates; probe placement preserves coefficients, spins,
repeated times and list order.

The original expectation stream inherits the explicit two-boundary Cauchy
modulus and converges to the already constructed positive window family.
Its rectangular bound allows the two boundaries to recede independently.
This concerns the **selected fixed-width chain action**, not the full
growing-box action or its interacting marginal. Arbitrary coordinate
polynomials are not declared original gauge observables.

The latest result supplies reflected positivity on the scheduled spatial-probe
span. Physical OS transfer/vacuum, joint limit control, width/spacing control,
continuum QFT and the Clay target remain open. Three focused checks at this
earlier checkpoint passed all 17 public axiom gates; no root/full-tree
check was run. See the [original-window audit](audits/AUDIT-FIXED-SPATIAL-ORIGINAL-WINDOW.md).

**Previous result: the window limits form a normalized positive linear family with translation consistency.**
The [window-state laws](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowState.lean)
prove normalization, addition, signed rational homogeneity and nonnegativity
on supported squares for the already constructed CReal limits. They retain
the original Haar-carrier relations and agree with the earlier slice
functional when the window has zero transitions.

Exact finite identities redistribute a single unobserved slice between the
window and a boundary, keeping the SAME action, insertion and partition.
The rectangular estimate then proves that right padding or a one-slice
translation leaves the limiting expectation unchanged. No stationary law
for a finite boundary-conditioned chain is assumed.

This is a **fixed-nome, fixed-width, fixed-cutoff polynomial window family**,
not yet a physical OS theory. Later results identify scheduled spatial probes
with original observables and prove their span reflection-positive;
gauge-observable completeness and the physical OS construction remain open.
Joint limit and width/spacing control, continuum QFT and the Clay target remain
open. Three focused checks at this checkpoint passed all 25 public axiom gates;
no root/full-tree check was run. See the
[window-state audit](audits/AUDIT-FIXED-SPATIAL-WINDOW-STATE.md).

**Previous result: complete observed windows have a constructive two-boundary time limit.**
The [two-boundary estimate](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowTwoBoundary.lean)
compares the SAME observed window with independently receding left and right
boundaries. The error is `2*C*(kappa+1)*q^s` once all four distances are at
least `s+1`, where `C=polynomialCap(P)` and `kappa=(kineticCap/kineticFloor)^2`.
Positive-message comparison and exact residual cancellation supply the new
left estimate without dividing by a possibly zero residual mass.

The [returned CReal](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowTimeLimit.lean)
has an explicit Cauchy modulus and a bound for arbitrary late rectangles,
not only the diagonal. The modulus is independent of late heat cutoff;
nome and spatial width still enter both `q` and `kappa`.
At that checkpoint this was a fixed-window scalar limit. The latest result
adds positive linear laws, unit-padding/shift consistency and original
placement for scheduled spatial probes. Interior cutoff removal, physical OS
identification and width/spacing control remain open, as do continuum QFT
and the Clay target. Six focused checks
passed all 54 public axiom gates; no root/full-tree check was run. See the
[window-time audit](audits/AUDIT-FIXED-SPATIAL-WINDOW-TIME-LIMIT.md).

**Previous result: complete observed windows have quantitative right-boundary control.**
The [window-contraction identity](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowPairing.lean)
retains any supported polynomial across several consecutive time slices,
with the SAME chronological action and partition. Its intermediate action
omits the final spatial weight; the terminal pairing supplies that weight
exactly once. Constructed certificates bound the observed message relative
to the original unobserved transfer iterate.

The [window estimate](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowBracket.lean)
then bounds two right-boundary distances beyond `s` by `2*polynomialCap*q^s`.
The error is independent of the fixed left-boundary distance and late heat
cutoff, but still depends on nome, spatial width and the observable.
The latest result above adds left-boundary comparison and the two-sided
time limit. Whole-window ambient-lattice placement and stationary cylinder
consistency were still open at that checkpoint; the latest result supplies
the unit-padding/shift laws, not a physical OS state or mass gap.
Five focused checks passed all 29 public axiom gates;
no root/full-tree check was run. See the
[observed-window audit](audits/AUDIT-FIXED-SPATIAL-OBSERVED-WINDOW.md).

**Previous result: a constructed positive linear expectation on supported slice polynomials.**
The [polynomial-bound construction](lean/YMGap/Continuum/QuaternionHaarSupportedPolynomialInterval.lean)
returns an explicit interval certificate for every supported rational
polynomial, including signed coefficients and shared variables. The existing
two-boundary argument therefore constructs a [CReal expectation](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPolynomialState.lean)
on an addition-closed algebra, not only separate probe-list scalars.
It is normalized, rational-linear and nonnegative on squares, respects
the original Haar-carrier relations, and agrees with the previous probe limit.
All laws retain the SAME finite partition before passing to the limit.

This is a **fixed-nome, fixed-width, fixed-cutoff slice functional**, not yet
a stationary multi-time cylinder state or physical OS theory. The latest
results supply whole-window contraction, both-boundary convergence and
consistency under unit insertion and one-slice time translation.
Cutoff removal, uniform volume/spacing control, continuum QFT and the Clay
target remain open. Four focused checks passed all 30 public axiom gates;
no root/full-tree check was run. See the
[polynomial-state audit](audits/AUDIT-FIXED-SPATIAL-POLYNOMIAL-STATE.md).

**Previous result: an original interior observable has a two-sided time limit.**
The [two-boundary estimate](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddleBracket.lean)
compares any two pairs of boundary distances beyond `s` with error
`4*probeCap*q^s`. It first changes one boundary, then the other; the
original partition is retained throughout. The rate is independent of late
heat cutoff, but still depends on nome and spatial width.

The [middle-slice pin](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalMiddle.lean)
identifies that ratio with the existing original lattice expectation, with
its physical face and geometry guards. Its [constructed time limit](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalMiddleTime.lean)
has an explicit modulus and controls independently receding boundaries,
not just a chosen diagonal. Nome, width and heat cutoff remain fixed.

At that checkpoint this was an **interior scalar limit**, not yet a positive
linear functional. The latest result above supplies the slice-algebra laws;
a positive linear cylinder state, stationary vacuum, physical OS theory,
cutoff removal, multi-insertion consistency and uniform volume/spacing
control remain open. The continuum
QFT and Clay target remain open. Five focused checks passed all 30 public
axiom gates; no root/full-tree check was run. See the
[two-sided-limit audit](audits/AUDIT-FIXED-SPATIAL-TWO-SIDED-TIME-LIMIT.md).

**Previous result: the actual transfer gives an exact interior-message pairing.**
The [weighted-symmetry proof](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean)
exchanges the two complete slices of the original kinetic polynomial and
retains both spatial weights. The [middle-insertion contraction](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean)
then identifies a chronological chain's interior numerator as
`ell((T^m 1) * p * (T^n 1))`, where `ell(h) = H[V*h]`.
Its denominator is proved equal to the SAME finite-chain partition and
strictly positive at every pair of lengths, including zero.

This was an **exact finite identity**, not yet two-sided convergence or a
stationary vacuum. The latest result above supplies the original middle-slice
placement and two-sided scalar boundary-forgetting bound. A separately checked
endpoint-probe ratio is explicitly distinguished from this interior ratio.
The rate still depends on nome and spatial width; physical OS identification,
uniform volume/spacing passage, continuum QFT and the Clay target remain open.
Six focused checks passed all 34 public axiom gates; no root/full-tree check
was run. See the [middle-pairing audit](audits/AUDIT-FIXED-SPATIAL-MIDDLE-PAIRING.md).

**Previous result: heat cutoff and boundary time have the same joint limit.**
The [original-scalar rectangle estimate](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalJointCauchy.lean)
constructs a common limit as both indices recede, with explicit independent
cutoff and time thresholds. It compares long chains through one computed
intermediate length; no cutoff estimate uniform in all chain lengths is assumed.
The [two iterated-limit theorems](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalJointLimits.lean)
prove that removing the heat cutoff first or the opposite time boundary first
reaches that SAME limit of the original selected-chain expectation.

This remains a **one-sided boundary scalar at fixed nome and spatial width**,
not a stationary vacuum, a bulk state or a physical OS theory. At that
checkpoint two-sided transfer pairing and an exact interior-probe identity
were the next steps; the latest result above supplies their finite algebra.
Width/spacing-uniform control, continuum QFT and the Clay target remain open.
Two focused checks passed all 15 public axiom gates; no root/full-tree check
was run. See the [joint-limit audit](audits/AUDIT-FIXED-SPATIAL-JOINT-BOUNDARY-LIMIT.md).

**Previous result: an original chain observable has an explicit boundary-time limit.**
The [nested comparison intervals](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferBracketNesting.lean)
now contain every later normalized ratio. Their geometric widths give a
constructed [CReal boundary limit](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoundaryTimeLimit.lean),
with an executable time-Cauchy modulus independent of late heat cutoff K.
The [original-action pin](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalTimeLimit.lean)
transfers this limit to the existing selected-chain expectation on admissible
growing boxes, keeping the same partition and terminal spatial weight.

This is a **one-sided, fixed-width, fixed-cutoff boundary scalar**, not a
stationary vacuum or physical OS state. The rate still depends on nome and
width. Joint cutoff/time passage is the next step; bulk/stationary and
connected-correlation construction, physical OS identification, uniform
volume/spacing estimates, continuum QFT and the Clay target remain open.
Three focused checks passed all 19 public axiom gates; no root/full-tree
check was run. See the [boundary-limit audit](audits/AUDIT-FIXED-SPATIAL-BOUNDARY-TIME-LIMIT.md).

**Previous result: geometric comparison bounds reach an original chain observable.**
The [actual transfer comparison](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferBracketDecay.lean)
constructs polynomial certificates bracketing `T_K^n f` relative to
`T_K^n 1`. For each original signed source probe, the interval width is
exactly `2*probeCap*q^n`, where `q = 1 - kineticFloor/kineticCap` and
`0 <= q < 1`. Positive normalization masses are proved at every step.
The rate is independent of late heat cutoff K, **not** of nome or width.

The [same-original scalar pin](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.lean)
places the existing normalized finite-chain expectation inside that interval,
with its actual geometry guards, terminal spatial weight and whole-chain
partition. The interval centre may change with time and cutoff: this is not
yet a stationary limit, connected-correlation bound or physical OS gap.
Uniform volume/spacing passage and the Clay target remain open. Six focused
checks passed all 40 public axiom gates; no root/full-tree check was run.
See the [proof audit](audits/AUDIT-FIXED-SPATIAL-PROJECTIVE-BRACKETS.md).

**Previous result: the actual transfer has a constructed cutoff limit.**
The [limit operator](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCompletedTransferLimit.lean)
acts on the SAME ordinary-Haar completion, without rescaling T or selecting
quotient representatives. Its explicit Cauchy family yields the original norm
cap and `||(T_limit-T_K)x||^2 <= epsilon^2 ||x||^2` at the existing computed
cutoff, uniformly in x at fixed nome and width. Addition and rational scaling
are proved for this actual limit map.

In parallel, [rank-one bounds](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean)
certify `a*H[V_K*f] <= T_K f <= b*H[V_K*f]` in the polynomial certificate
cone. Here a and b depend on nome and width, not the late heat cutoff;
the displayed weighted mass still depends on K. No spatial factor is dropped.
These bounds do not yet prove a contraction, stationary vacuum or physical
OS identification. Uniform volume/spacing passage and the Clay target remain
open. Four focused checks passed all 35 public axiom gates; no root/full-tree
check was run. See the [proof audit](audits/AUDIT-FIXED-SPATIAL-TRANSFER-LIMIT.md).

**Previous result: the original transfer preserves certified polynomial order.**
The [actual transfer-order theorem](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferOrder.lean)
now composes the proved Haar-integration rule with a support-guarded
certificate enlargement. It retains the original K*V weight and constructs
certificates for T f and every finite iterate from a supported certified f.
Certified comparisons between two supported messages are preserved as well.

The support guard matters: enlarging a carrier without it can expose terms
that were previously invisible to Haar integration. The proof handles
arbitrary transported certificate intermediates through an explicit supported
representative. This is positive-cone preservation, **not** operator positive
semidefiniteness, contraction or a physical gap. Two focused checks passed
all 11 public gates; no root/full-tree check was run. See the
[follow-up audit](audits/AUDIT-FIXED-SPATIAL-HAAR-CUTOFF.md#support-guarded-extension-and-actual-transfer-order-follow-up).

**Previous result: explicit cutoff-Cauchy control of the actual completed operator.**
The [completed difference estimate](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCompletedCutoffControl.lean)
proves `||(T_J-T_K)x||^2 <= epsilon^2 ||x||^2` for every point of the
same ordinary-Haar completion once both cutoffs exceed a computed threshold.
The threshold depends on nome, spatial width and epsilon, not on x.
The proof retains the original K*V weight and handles its signed difference;
it does not assume that difference is positive.

In parallel, [actual partial-Haar integration](lean/YMGap/Continuum/SU2QuaternionHaarCertificateIntegration.lean)
now preserves constructive square certificates on all remaining variables.
The square case uses two parity sectors and coefficientwise sphere-radius
homogenization. This supplies an order-preservation ingredient; quantitative
forgetting is still open. At that checkpoint a limiting operator had not yet
been constructed from the Cauchy estimate; the latest result above supplies it.
Stationary/physical OS, volume/spacing and continuum
mass-gap obligations remain open. Five focused checks passed all 29 public
gates; no root/full-tree verification was run. See the
[proof audit](audits/AUDIT-FIXED-SPATIAL-HAAR-CUTOFF.md).

**Previous result: completed powers recover the original finite-chain moments.**
The [completed-iteration theorem](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCompletedIteration.lean)
identifies every finite power of the actual completed map with its original
polynomial iterate. Pairing with `V*g` recovers the original selected-chain
numerator, including signed endpoint probes. The terminal spatial weight
occurs once, including at zero steps. This joins the completed operator to
the existing finite-chain scalar theory; it is not an operator cutoff limit
or a stationary OS construction.

A parallel [Gaussian square certificate](lean/YMGap/Continuum/SU2QuaternionHeadGaussianSquareCertificate.lean)
expresses integration of four head coordinates of a polynomial square as
an explicit nonnegative sum of tail-polynomial squares. This supplies a
constructive algebraic ingredient for partial-integration positivity;
the actual partial-Haar certificate producer remains open at this checkpoint.
Both focused checks passed, with all 13 public gates in the allowed axiom
set. Root/full-tree verification was not run. See the
[follow-up audit](audits/AUDIT-FIXED-SPATIAL-HAAR-TRANSFER.md#completed-original-moments-and-gaussian-square-follow-up).

**Previous result: the actual weighted step has a bounded ordinary-Haar completion.**
The [original transfer bound](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferBound.lean)
proves `||T f||^2 <= C(w,width)^2 ||f||^2` for the actual
`T f(y) = integral K(x,y)V(x)f(x) dH(x)`. The explicit cap is independent
of heat cutoff after the existing positivity threshold, but depends on
nome and spatial width. No action factor is removed or separately normalized.

The [completed map](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCompletedHaarTransfer.lean)
retains that bound, exact dense pairing, rational linearity, and explicit
Cauchy moduli on the existing ordinary product-Haar GNS completion.
**This is not the physical reflected OS Hilbert space or a gap estimate.**
Cutoff-operator convergence, stationary vacuum construction, quantitative
forgetting and the volume/spacing/continuum passage remain open.
Six focused serialized checks passed all 57 public gates; root/full-tree
verification was not run. See the [proof audit](audits/AUDIT-FIXED-SPATIAL-HAAR-TRANSFER.md).

**Previous result: cutoff removal for the actual normalized finite-chain iterate.**
The [scalar-limit theorem](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIterationLimit.lean)
identifies both the iterated numerator and its partition with the same
original selected action. One original reciprocal normalizes the whole
chain. At every rational `0<w<1`, the resulting scalar stream converges to
the existing original expectation with its explicit cutoff modulus.

This uses the exact original-action identity below, so no convergence of
cutoff-dependent intermediate messages is assumed. Width, chain length and
probes are fixed: stationary time limits, OS realization, quantitative
contraction and volume/spacing/continuum control remain open. All 13 public
gates passed a focused serialized check; root/full-tree verification was
not run. See the [follow-up audit](audits/AUDIT-FIXED-SPATIAL-ORIGINAL-ITERATION.md#original-scalar-cutoff-limit-follow-up).

**Previous result: original finite-chain moments equal weighted-step iterates.**
The [original-action identity](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalIteration.lean)
now connects the entire selected time chain to repeated application of
the same original kinetic/spatial step on one fixed spatial carrier.
Signed spatial-face probes on both endpoints are retained. There are n
kinetic factors and n+1 spatial weights; the zero-step case has one weight.

The chronological carrier and endpoint-probe pins were developed in parallel;
the parent composed and checked them. All 27 public gates passed three
focused serialized checks. This closes the previously missing finite-chain
identification, not a normalization, stationary OS operator or gap estimate.
The next consumer is the existing fixed-insertion cutoff limit, applied to
the whole scalar pairing. Quantitative control and the continuum/all-group
target remain open. Root/full-tree verification was not run. See the
[proof audit](audits/AUDIT-FIXED-SPATIAL-ORIGINAL-ITERATION.md).

**Previous result: an exact original weighted step and finite-chain identities.**
The [computed step](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferStep.lean)
integrates the original kinetic factor and one lower spatial weight on a
fixed slice carrier. Its pairing equals the original swept `V0*K01*V1`
pairing, for arbitrary supported source polynomials. The upper weight
stays explicit; neither endpoint weight is counted twice.

Parallel proofs establish exact iteration on an ordered polynomial chain
and duplicate-free original face geometry for any finite number of layers.
A single common sweep also factors that original chain into its actual
spatial and kinetic factors. **Connecting the entire arbitrary-length
original carrier to the ordered iteration still needs proof.** Stationary
OS identification, quantitative contraction and the continuum gap remain open.
All 45 public gates passed six focused serialized checks; root/full-tree
verification was not run. See the [proof audit](audits/AUDIT-FIXED-SPATIAL-TRANSFER-STEP.md).

**Previous result: one original spatial weight on a fixed slice carrier.**
The [spatial-weight identity](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean)
constructs one polynomial depending only on spatial width, rational nome
and heat cutoff. At every contained time and ambient extent, its explicit
coordinate placement gives the original spatial heat product. Ordered
plaquette multiplication, every finite spin term and spatial fringe links
are retained. Weighted Haar pairings agree for all supported source insertions.

Parallel work also supplied the exact face-list placements and an ordered
pair of consecutive slice carriers. Six focused serialized checks passed;
all 73 reported public gates are within {propext, Quot.sound}. This is an
exact finite identity, not a contraction estimate. The kinetic-factor pin,
repeated weighted composition, stationary OS identification and continuum
mass gap remain open. Root/full-tree verification was not run. See the
[proof audit](audits/AUDIT-FIXED-SPATIAL-SLICE-WEIGHT.md).

**Previous result: exact fixed-width boundary realization.**
The [computed two-layer kernel](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBoundaryCarrier.lean)
now lives on an explicit two-endpoint carrier whose size depends only on
spatial width, not ambient extent, start time or heat cutoff. Its embedding
reconstructs the original polynomial and preserves the Haar integral.
Spatial plaquette-edge fringe variables are retained.

Parallel work supplied the exact compression proof and an independent
consumer review. All 30 new public axiom gates passed focused serialized
checks. The kernel's coefficients still depend on the original parameters;
repeated single-slice composition, stationary normalization and quantitative
control remain open. No continuum or gap claim follows from this recoding.
See the [proof audit](audits/AUDIT-FIXED-SPATIAL-BOUNDARY-CARRIER.md).
The parallel [new-paper review](audits/RESEARCH-MATH-PH-2026-09-16.md)
identified useful normalization and hierarchical-RG ideas, but no directly
applicable Yang--Mills estimate. Root/full-tree verification was not run.

**Previous result: original two-layer gluing at fixed spatial width.**
The [new finite identity](lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean)
glues two adjacent temporal layers of the original selected-window action.
The shared middle spatial heat occurs exactly once; both endpoint spatial
weights remain outside the middle-link Haar integral. Signed endpoint
insertions and every finite character term are retained.

Parallel geometry, locality and operator-interface work supplied the inputs.
All 30 new public axiom gates passed focused serialized checks. This is an
exact finite pairing identity, **not a stationary transfer or gap theorem**.
Repeated composition on one physical carrier, the applicable quantitative
Haar estimate and continuum-scale control remain open. The root/full tree
was not checked. See the [proof and future-path audit](audits/AUDIT-FIXED-SPATIAL-TWO-LAYER-GLUING.md).

**Previous result: distance exclusion and exact insertion activity.**
The [original response](lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean)
now has a proved geometric floor: for two connected probe carriers and
a fresh inserted face, a retained core needs at least the largest pairwise
root distance minus the two carrier sizes in old faces. The proof adds
only the actual inserted face, not an artificial connecting corridor.

Independently, the actual SU(2) heat insertion contributes an exact `w^3`
factor to the signed response and every old-face finite-difference
coefficient. The combined finite identity retains the third-moment term,
quadratic correction and every detached partition factor. It works at
arbitrary rational `w`, including zero, without division by `w`.

This is one insertion factor, **not decay per core face**. A useful bound
on the remaining signed cofactor is still missing; the coarse all-coupling
normalization cost does not supply one. All 22 public gates passed four
focused serialized checks; root/full-tree checks were not run. See the
[proof and route audit](audits/AUDIT-RESPONSE-DISTANCE-ACTIVITY.md).
The continuum physical mass-gap goal remains open.

**Previous result: exact spectator resummation and local response normalization.**
The [new identity](lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean)
regroups the original signed covariance response by its computed rooted
cores. Detached selections sum exactly to their original partition fourth
power, before any absolute bound is taken. The inserted face and both
probes are included in the roots; the existing three-mark tests remove
only proved-zero coefficients.

An [explicit normalization bound](lean/YMGap/Continuum/BF4ExactSlabResponseCollarNormalization.lean)
then charges only for the local collar, retaining both original endpoint
partitions. Its cost depends on the coupling and marked/core sizes, not
the number of detached faces. This removes a whole-volume normalization
penalty, but supplies no smallness, summability or spatial decay. The
physical/continuum gap remains open. All 22 public gates passed focused
serialized constructive checks; root/full-tree checks were not run.
The [audit](audits/AUDIT-RESPONSE-SPECTATOR-RESUMMATION.md) records the
parallel proofs, exact cost and remaining analytic input.

**Previous result: exact three-mark cancellation for the original response.**
The [new expansion](lean/YMGap/Continuum/BF4ExactSlabThreeMarkResponseExpansion.lean)
removes terms whenever a literal link cut separates either probe from the
other probe and inserted face, or separates the inserted face from both
probes. In the last case the probes may remain correlated: both spectator
partition factors cancel exactly. A disconnected insertion also leaves
the actual cutoff-removed covariance unchanged for every rational `0<w<1`.

The surviving response is one signed, computed finite sum. Its spatially
decaying bound remains open; detached spectator factors cannot simply be
dropped, and absence of these cuts does not mean every face is connected.
All 11 public gates passed focused serialized constructive checks;
root/full-tree checks were not run. The [audit](audits/AUDIT-THREE-MARK-RESPONSE.md)
records the exact consumer and the remaining physical/continuum obligations.

**Previous result: one shared face, and a ruled-out coarse-window inference.**
Two distinct literal links share
[at most one physical plaquette](lean/YMGap/Continuum/BF4ExactSlabSharedFaceUniqueness.lean).
But even this improvement does not make the existing absolute heat window
narrow: `32*headFloor(w) <= prefixCap(w)` for every rational `0<w<1`.
An [explicit four-weight law](lean/YMGap/Continuum/RationalTwoStateWindowWitness.lean)
inside that numerical window has centered unit-norm signs and computed
conditional squared norm at least `961/1089 > 7/8`. Thus that window alone
cannot imply a squared-norm contraction factor of `1/2`.

This witness is **not Yang--Mills** and does not lower-bound its actual
influence or refute sharper small-nome estimates. It rules out a proposed
generic inference before investing in further operator scaffolding.
The next missing input is a spatially decaying, action-specific signed
response or boundary-determinant estimate with useful physical-scale
dependence. Four focused serialized checks passed; all 31 public gates
are within the constructive axiom gate. Root/full-tree checks were not run.
See the [proof and route audit](audits/AUDIT-SHARED-WINDOW-INFLUENCE.md).

**Previous result: non-neighbor conditional updates commute for the original action.**
The [new theorem](lean/YMGap/Continuum/BF4ExactSlabStarNonneighborCommutation.lean)
proves that updates at two physical links sharing no plaquette commute on the
entire original full-action L2 completion. Their joint update is self-adjoint
and idempotent, with fixed space exactly the intersection of the two fixed
spaces. This holds for every rational `0<w<1` and `K>=headCutoff(w)`, retaining
all interactions and the already constructed Cauchy representatives.

This removes non-neighbor commutators, not correlations between distant
observables. A quantitative neighboring-influence bound, spatial decay and
an OS/physical-gap bridge remain open. Nineteen public gates passed focused
serialized constructive checks; root/full-tree checks were not run.
See the [proof and scope audit](audits/AUDIT-NONNEIGHBOR-COMMUTATION.md).

**Previous result: cutoff stability relative to the actual centered variance.**
The [new comparison](lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean)
proves that changing one face from cutoff `K` to `K+L` changes ordinary
original-action variance by at most a multiplicative factor `(1+eta)^2`,
in either direction, once `K>=relativeCutoff(w,eta)`. Each law uses its
own computed mean. The bound works for every supported polynomial,
without a supplied observable cap or `eta<1`; both partitions and every
positive spectator interaction remain. The two centered null spaces agree.

This is norm-relative regulator stability, not spatial decay or an OS-norm
comparison. The cutoff depends on the coupling, and only one face changes.
Twenty public gates passed focused serialized checks; root/full-tree checks
were not run. The [audit](audits/AUDIT-ONE-FACE-VARIANCE-COMPARISON.md)
also records why heat cap/floor bounds alone do not supply the missing
all-nome physical transfer identification. The Clay target remains open.

**Previous result: an exact connected response, and a test of pairwise closure.**
The [original-action identity](lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean)
expresses the change of covariance under one full heat-face insertion using
a third connected moment and a subtracted product of two pairwise moments,
with their exact partition factors.
Both different partition functions and the pre-existing covariance remain.
The cutoff-limit consumer preserves this signed combination; it still
requires a quantitative bound as input and does not produce spatial decay.
Its full-slab covariance is proved equal to the existing original observable.

An independent [finite witness](lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean)
uses the actual positive cutoff-one heat factor at `w=1/8`: both
probe–insertion covariances vanish, yet the covariance changes by `1/256`.
Thus pairwise responses alone do not determine this change. The probes
occupy the same plaquette; this is not a separated-probe, all-late-cutoff,
cutoff-removed or full-slab counterexample. The next missing estimate must
control this signed response with usable spatial and coupling
dependence. See the [audit](audits/AUDIT-CONNECTED-FACE-RESPONSE.md) for exact
scope and verification. The continuum and physical mass-gap target remains open.

**Previous result: one-face cutoff stability without a volume penalty.**
The [new estimate](lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean)
bounds the change of an original normalized expectation by `2*c*eta` when
one face's heat cutoff is increased beyond the explicit `relativeCutoff(w,eta)`.
Here `c` is the supplied observable cap; every other interaction and shared
link remains in the same positive background. Both different partition
functions are retained until division. No `eta<1` assumption or inverse-floor
loss is needed, but the cutoff still depends on the coupling.

An independent [retained-head witness](lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean)
has original connected numerator exactly `w^36>0` on the twelve-face tube
sub-action. Thus small high-spin tails do not make the interacting head's
correlation vanish. The missing step is spatial control of that head and
its response to perturbations, not another normalization wrapper. Nineteen
public gates passed focused serialized checks; root/full-tree checks were
not run. The [audit](audits/AUDIT-RETAINED-HEAD-CUTOFF-STABILITY.md) records
the parallel work and the precise remaining boundary. No continuum or
physical mass-gap claim follows.

**Previous result: bounded original OS dual tests at all positive subunit nomes.**
The [new estimate](lean/YMGap/Continuum/BF4ExactSlabAllNomeDressedDualTest.lean)
removes the old small-nome restriction on bounded auxiliary polynomial tests.
After cutoff removal, their squared amplitude is bounded by their supplied
cap product times the SAME original reflected norm. Both original partitions
cancel exactly. The concrete bulk scalar test has norm at most one and
descends to the existing finite-volume OS quotient; it is not assumed to be
an original state or a separating test. The unit test evaluates to one on
the original unit.

In parallel, [site-reflection positivity](lean/YMGap/Continuum/BF4ExactSlabAllNomeSiteReflection.lean)
now holds for the original cutoff-removed even-slab law at every rational
`0<w<1`. These results do not supply centered decay or continuum control.
Fifteen public gates passed focused serialized checks; no full-tree check
was run. The [route audit](audits/AUDIT-ALL-NOME-OS-TESTS.md) identifies the
next analytic estimate and explains why extra boundary gluing is not its
prerequisite.

**Previous result: the original signed slab form is reduced to its actual boundary.**
The [boundary-marginal identity](lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean)
integrates the interior links of both complete heat-dressed observables,
retaining the literal crossing-link coordinates and every action factor.
Their pairing against the original relative heat interface equals the SAME
signed slab bilinear, at every finite cutoff and odd extent for `w>=0`.
The schedules and residual polynomials are explicit; no coordinate recoding
or assumed conditional independence is needed.

An independent [background estimate](lean/YMGap/Continuum/BF4ExactSlabAllNomeBulkProbeBackground.lean)
now works for every rational `0<w<1` at `K>=headCutoff(w)`. It does not
remove the separate smallness condition on collar perturbations.
Thirty public gates passed focused serialized checks; root/full-tree checks
were not run. The [boundary audit](audits/AUDIT-ORIGINAL-BOUNDARY-MARGINAL.md)
separates this finite identity from the still-missing adjacent-region gluing,
original OS-observable realization, physical time identification, and usable
centered decay. None of these results closes the continuum/Clay target.

**Previous result: positive certificates for the actual crossing interface at all nomes.**
The [new original-interface construction](lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean)
certifies its spatial heat factors and complete spectator products for every
rational `0<w<1`, once the existing explicit `headCutoff(w)` is reached.
The proof uses the literal lower/reflected-upper link word and retains all
shared variables. Weighted lower/upper comparisons use the existing
`headFloor(w)` and `prefixCap(w)`; they are not coupling- or volume-uniform
gap bounds. The older small-nome statements are unchanged.

This removes a finite positivity restriction, not the missing centered
spatial/OS estimate. Twenty new public gates passed focused serialized
checks; root/full-tree verification was not run. See the
[operator-path audit](audits/AUDIT-HEAT-WINDOW-OPERATOR-PATH.md) for the exact
original-action pins and remaining boundary/operator and continuum obligations.

**Previous result: an explicit budget for the original six-face conditional law.**
The [new comparison](lean/YMGap/Continuum/BF4ExactSlabRoundedStarBudget.lean)
uses the actual heat windows to prove `1 <= 4^(6*bits(w))*starRatio(w)`.
Its normalized original-action consequence retains every complementary
interaction and both partition functions. The exponent counts six incident
faces, not the volume, and has AF-scaled cost at most `1080` under the existing
envelope. The coupling dependence remains explicit: this is not a uniform
mixing margin or an OS spectral gap.

Parallel [operator-path review](audits/AUDIT-HEAT-WINDOW-OPERATOR-PATH.md)
also located the already-proved original temporal-gauge identity at arbitrary
cutoff and extent. It should be reused; the old 23-factor comparison is not
an identification with the original physical transfer. All five new gates
passed focused serialized checks; root/full-tree verification was not run.

**Previous result: actual positive SU(2) heat windows with a proved AF budget.**
The [new construction](lean/YMGap/Continuum/BF4RoundedPositiveAFWindows.lean)
now supplies local windows, their ratio bound, and their growth witness;
these are no longer assumed inputs. For the rounded cutoff `N(w)`, it
uses the explicit budget `bits=5*N+5` and proves `bits*t/4 <= 180`
under the existing AF envelope. Finite Euler-product bounds and the
actual SU(2) Casimir decay control both window endpoints, including all
rational class coordinates in `[-1,1]`. No Gaussian image identity or
exact dyadic schedule is assumed.

The bounds feed a comparison for products of 23 actual completed heat
factors. They do **not** identify that product with the original interacting
transfer or prove its centered contraction rate. The matched specialization
still assumes the cubic law and physical spacing envelope. See the
[declaration-level audit](audits/AUDIT-ROUNDED-HEAT-WINDOWS.md) for this
boundary. All 37 public gates passed focused serialized checks; root/full-tree
verification was not run. Continuum Yang--Mills and the all-group Clay target
remain open.

**Previous result: direct cutoff growth without the impossible dyadic schedule.**
The [rounded actual-nome cutoff](lean/YMGap/Continuum/HeatRoundedCutoff.lean)
computes `N=floor(8/(1-w))+1`, proves `8 <= N*(1-w) <= 9` and
`w^N <= 1/8`, and gives the same integer for equivalent rational nomes.
The [AF growth proof](lean/YMGap/Continuum/BF4RoundedNomeAFGrowth.lean)
uses the existing margin `t/8 <= 1-w` to prove `N*(t/4) <= 18`.
It supplies the existing growth and generic window interfaces at the actual
nome; the matched specialization still assumes the cubic law and spacing
envelope. No exact dyadic or Pade identity is required.

At that checkpoint, the actual local windows and their `upper <= 4^N*lower`
estimate were explicit inputs. The new result above constructs windows
with the sufficient larger bit budget `5*N+5`; the sharper `4^N` cap is
not asserted. All 13 public gates passed in two focused, serialized checks; no
full-tree build was run. Physical scale/transfer calibration, changing-action
spatial estimates, continuum construction and the all-group target remain open.

**Previous result: a bridge specification was refuted, not a physics theorem proved.**
The [exact matched dyadic bridge](lean/YMGap/Continuum/BF4MatchedDyadicHeatObstruction.lean)
requires a rational coupling with square `1/2`. Lean now proves that it
has no inhabitant. The matched pointwise-window interface also contains
that impossible bridge. Its conditional theorems therefore cannot supply
physical instances. The [audit](audits/AUDIT-AF-DYADIC-BRIDGE.md) traces
the affected consumers and distinguishes the separate RG-calibration issue.

The old statements are preserved and explicitly labelled; no frontier field
was weakened. Five new and seven existing public axiom checks passed in
three focused, serialized runs. The direct quantitative growth above now
bypasses this schedule through an unchanged generic interface;
the required local-window and spatial estimates remain open. The independent
original-action results below are not refuted. No full-tree build was run.

**Previous result:** [original intermediate face-set expectations](lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean)
are now constructed for every rational nome `0<w<1`, with explicit cutoff
and Cauchy moduli. The [partition reciprocal](lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetReciprocal.lean)
uses the original positive cutoff tail, and the resulting expectations are
proved equal to the existing original-action laws where both are defined.
[Comparison bounds](lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean)
cancel both actual partitions before taking limits, preserving exactly the
supplied determinant coefficient. This removes the old small-nome
normalization guard; it does **not** supply a spatially decaying coefficient,
a nome/volume-uniform modulus, or a comparison between different nomes.

Parallel proof work and independent source review were integrated with
serialized checks under the safe-build policy. All 32 public gates in the
four changed proof modules passed; no full-tree build was run. The next
obstacle is an original-action spatial estimate with usable coupling and
scale dependence. The continuum and all-group Clay target remain open.

**Previous result:** two parallel proof branches supplied
[exact shared-face factorization](lean/YMGap/Continuum/BF4ExactSlabSharedFaceGeometry.lean)
and [one-face change-of-action identities](lean/YMGap/Continuum/BF4ExactSlabFaceInsertionDeterminant.lean).
Only faces touching both selected links are separated; every other action
factor remains, and the shared list has at most six faces. The change-of-action
numerator from adding a face is exactly a covariance numerator under the
preceding action, retaining both different partition functions. These are algebraic identities, not
conditional independence or spatial decay.

An independent [route review](audits/AUDIT-T2-TEST-COMPARISON.md)
prevented a redundant branch: the proposed small-nome path targets
fixed-coupling consequences already proved here. The next argument
must address the changing original action and physical scale, not merely
produce another fixed-nome gap. All 33 new public declarations passed focused,
serialized constructive checks; no full-tree build was run. The continuum
and all-group Clay target remain open.

**Previous result:** [fixed support for the actual conditional projection's approximants](lean/YMGap/Continuum/BF4ExactSlabStarConditionalLocality.lean).
For an input supported on `S`, every approximation is supported on `S` plus
the selected link's incident faces, with that link removed. The neighborhood
does not grow with iteration count. An explicit Cauchy representative with
this support and the existing modulus is proved to represent the original
completed conditional projection.

This closes the local support step, not cross-link commutation or spatial
mixing. The next quantitative target must remove the common exterior
observables of two links and control their remaining interaction in the
original action. The boundary-law and physical-scale bridges remain open.

[A checked arithmetic obstruction](lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean)
also shows that the present coarse directional factor is at least `63/64`:
it cannot serve as a small per-neighbor weight, even for `2*q<1`.
This is a limitation of that bound, not a non-mixing or nonexistence theorem.
All 11 new declarations passed focused constructive checks; root/full-tree
verification was not run.

**Previous result:** [a strict local estimate for explicitly free-centered inputs](lean/YMGap/Continuum/BF4ExactSlabStarLocalInfluence.lean).
For every original polynomial `p`, compute its free-link residual `r` by
subtracting its Haar average over the selected link. The **actual**
conditional projection satisfies `||Q_link r||² <= (1-L(w)/U(w))*||r||²`
in the original full-action norm. The factor is below one for each allowed
`w`, independent of volume and cutoff above the stated guard. Sixteen new
public declarations passed focused constructive checks; no full-tree build
was run.

This is a **directional one-link estimate**, not a gap on the whole vacuum
complement. Next are cross-link propagation and quantitative influence,
followed by a proved connection to the two-law boundary response. A later
link update need not preserve this centering condition. No coupling-uniform
physical margin, continuum QFT or all-group Clay closure is claimed.

**Previous result:** [the actual one-link conditional projection is constructed on the entire original weighted completion](lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean).
It is self-adjoint, idempotent and nonexpansive, agrees with the lifted
`N_p/D` on dense inputs, and fixes every completed exterior probe. The
construction retains the original full action and the exterior marginal
`D*B`, with explicit Cauchy and null-compatibility moduli. Two parallel
proof branches and a downstream-interface review were integrated; all 35
new public gates pass focused, serialized constructive checks.

**Next:** quantitative influence between links or regions, sufficient for
the original boundary-numerator spatial-decay estimate. The proved norm
bound is **1, not a strict rate below 1**. This ordinary weighted L2
projection is not an OS transfer or Hamiltonian gap. Physical scaling,
continuum QFT and the all-group Clay target remain open. Root/full-tree
verification was not run.

The entries below record earlier checkpoints; their then-open local
obligations are superseded where explicitly closed above.

**Previous result:** [the actual one-link normalizer now has constructed completed preimages](lean/YMGap/Continuum/BF4ExactSlabStarCompletedInverse.lean).
The polynomial approximants are Cauchy in the original complementary-action
weighted space, with an explicit modulus. Multiplication by `D` extends to
that same completion and is injective. For every supported polynomial `r`,
the constructed state satisfies the exact equation `D * inverseState(r) = r`.
This constructs `N_p/D` for the actual conditional numerator, not a replacement law.
All 31 public gates in the three checked proof modules pass the constructive
axiom gate. Verification was focused and serialized, not a full-tree build.

The original full-action lift and conditional projection, open at that
checkpoint, are now supplied by the latest result above.

**Previous result:** [explicit polynomial approximate division by the actual one-link normalizer](lean/YMGap/Continuum/BF4ExactSlabStarInverseApproximation.lean).
In the actual complementary-action weighted norm, the iteration
`a <- a + (r-D*a)/U` has squared residual bounded by
`(1-L/U)^(2*n)` times the input norm, with a computed tolerance cutoff.
[The actual inserted numerator is controlled by the original full-action norm](lean/YMGap/Continuum/BF4ExactSlabStarInsertedNumerator.lean),
so these approximants apply to the original conditional ratio `N_p/D`.
The constants depend on `w`, not volume or cutoff above `headCutoff(w)`.

Two parallel proof branches and a completion-interface review were integrated;
all 30 public gates passed serialized focused checks. **An approximate preimage is not yet
a completed inverse or conditional projection.** Their Cauchy/limit identities,
spatial decay, physical scaling and the Clay target remain open.

**Previous result:** [the actual one-link normalizer has strict weighted form bounds](lean/YMGap/Continuum/BF4ExactSlabStarNormalizer.lean#L196).
The original exterior marginal retains the boundary-dependent normalizer
`D` and complementary action `B`: its weight is `D*B`, not `B`.
Exact test-function identities preserve the original action and observables.
For every supported exterior polynomial, the proof bounds this marginal
form above and below by explicit `w`-dependent multiples of the `B` form,
and bounds multiplication by `D` in that weighted norm. Constants do not
grow with volume or sufficiently late representation cutoff.

All 28 public gates across three focused modules pass; checks were serialized.
The constructive inverse and original-law conditional update remain next,
followed by the still-open spatial estimate. This is not an OS or physical gap.

**Previous result:** [an explicit volume-independent comparison for the actual one-link star](lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean#L120).
For every rational `0<w<1` and sufficiently late cutoff, deleting only
the link's at-most-six incident heat factors costs explicit positive
constants depending on `w`, not volume or cutoff. All complementary
factors and shared links remain. The normalized comparison retains both
partition functions by cross multiplication.

[Parallel geometry work](lean/YMGap/Continuum/BF4ExactSlabLinkStarGeometry.lean)
proves the actual incidence bound and exact complement Fubini identity.
All 49 public gates across three focused modules pass the constructive
axiom gate; compiler checks were serialized. This is **not yet an original
conditional kernel or spatial contraction**: its boundary-dependent
normalizer and influence estimate remain to be constructed and controlled.

**Previous result:** [increasing the cutoff cannot rescue the unit-background spatial expansion](lean/YMGap/Continuum/BF4ExactSlabHeatHaarGuardObstruction.lean#L285).
For the actual plaquette and `r=1+chi_1`, the exact Haar moments are
`H(r^2)=2` and `H(r^2*(H_K-1))=4*w^3+3*w^8` for every `K>=2`.
Thus at `w>=7/8`, the full interaction cannot have an original Haar
interval cap at most one—even eventually, with a cutoff-dependent cap.
This rules out a repair of the old spatial argument, **not Yang–Mills
existence**. The small omitted tail proved below is a different object.

The parallel source review also identifies the retained-head obstacle:
the zero-tail term is still the head's boundary response, not zero.
Its spatial estimate remains open. Five new and 14 existing declarations
passed focused constructive axiom checks; no full-tree build was run.

**Previous result:** [late original heat prefixes have a strict Haar-order floor and a relative tail bound](lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean).
For every rational `0<w<1`, the proof retains the full interacting head
and controls its omitted tail against the **same** positive background.
The computed cutoff depends on `w` and the relative tolerance, not the
slab, face placement, background size or tail length. Original shared-link
heat-product backgrounds receive actual positivity certificates.

Three parallel tasks also delivered a reusable constant-term certificate,
[late-cutoff normalization transport](lean/YMGap/Continuum/BF4ExactSlabBoundaryLimitNormalization.lean),
and [a trivial centered zero-image kernel for the original real generator graph](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDerivativeClosedGraph.lean).
All 55 public declarations in the five changed modules passed focused
constructive axiom checks; compiler checks were serialized.

**The remaining issue is spatial decay of the retained interaction.**
A small truncation tail is not a small full interaction. The next target
is the original denominator-cleared inter-slab estimate, with a bound
that tends to zero with separation. The thermodynamic action is still
fixed at nome `1/1024`; physical scaling, continuum QFT and all required
groups remain open. CI remains manual-only.

**Previous result:** [arbitrary-nome heat insertions converge in the original reflected OS norm](lean/YMGap/Continuum/BF4ExactSlabLocalHeatCutoffNorm.lean).
For every rational inserted `0<w<1`, a computed cutoff controls the
existing heat-dressed observable, uniformly over bulk padding and allowed
lag, under any independent finite-volume action nome `0<v<1`.
[The same samples now construct a state in the existing thermodynamic completion](lean/YMGap/Continuum/BF4ExactSlabThermodynamicLocalHeatState.lean),
with an explicit approximation modulus and equality to the legacy state
where its old guard holds. No new carrier or replacement observable.

The thermodynamic action is **still fixed at nome `1/1024`**. This removes
an inserted-cutoff restriction, not the changing-action or physical-scale
obstruction. The background-relative retained-head/tail comparison is now supplied above;
low-spin decay, a compatible scaling family, continuum QFT and all required
groups remain open. Seventeen new public gates and all 22 existing gates
in the two edited modules passed within the constructive axiom gate in
two focused safe checks; no full-tree run or raised limits.

**Previous result:** [arbitrary-nome local heat tails now have original-Haar certificates](lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean).
The low-spin head is retained exactly. For every rational `0<w<1`,
a computed cutoff makes the omitted tail small in original Haar order.
[The actual product remainder and prefix difference are controlled too](lean/YMGap/Continuum/BF4ExactSlabAllNomeProductTail.lean):
one cutoff depending on `w`, retained face count and tolerance works
in every slab, with all shared links retained. Its normalized square
expectation is at most `epsilon^2` under the original interacting law;
the action's nome `v` is an independent, explicit parameter.

This is local representation-cutoff control, not thermodynamic decay
or a mass-gap theorem. The cutoff is not uniform in `w` or region size.
The reflected OS-norm consumer is now supplied above.
Physical scaling, continuum QFT and all required groups remain open.
All 25 public axiom checks passed within the constructive gate in
focused safe checks; no full-tree run or raised limits.

**Previous result:** [an exact original-Haar test rules out sharpening the all-cutoff guard](lean/YMGap/Continuum/BF4ExactSlabHeatHaarGuardObstruction.lean).
On any physical slab plaquette, the explicit square `(1+chi_1)^2` has
Haar integral two. Against the cutoff-one heat remainder its integral
is `4*w^3`. Thus, for `w >= 7/8`, no existing Haar interval certificate
for that remainder can have cap at most one. This concerns the actual
polynomial, not a loose upper bound. A computed point on any supplied
AF chart puts both its fine and matched blocked nomes in this range.

The obstruction is to the **all-cutoff** near-unit interface, already
at cutoff one. Later-cutoff estimates and different reference actions
are not excluded. The next task retains the low-spin head and controls
only its omitted tail in original Haar order. Physical scaling,
continuum QFT and all required groups remain open. All 14 public axiom
checks passed within the constructive gate in focused safe checks;
no full-tree run or raised limits.

**Previous result:** [the existing small-nome guard cannot cover the AF chart](lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean).
The guard requires a returned remainder cap below one. That cap is
`128*w^3`, already at least two for `w >= 1/4`. Any supplied existing
AF margin law puts both the fine nome and the one-step matched blocked
nome above this threshold when `0 < g <= min(g1,1/2)`.
The proof returns that explicit coupling witness.

This rules out direct reuse of the old guard, not the AF law or
Yang--Mills existence. It is a bound on the returned cap, not a lower
bound on the actual heat remainder. The next task is to test whether
a sharper original-face estimate suffices before designing a replacement
scale/volume estimate. Physical scaling, continuum QFT and all required
groups remain open. All 15 public checks passed within the constructive
gate in one focused safe check; no full-tree run or raised limits.

**Previous analytic result:** [the original time action preserves its derivative graph](lean/YMGap/Continuum/BF4ExactSlabThermodynamicGraphTimeTransport.lean).
If `J u = T2 v`, then `(A_t u, A_t v)` belongs to the same graph.
Commutation of the actual difference quotients and contraction preserve
the derivative rate. The original output representatives are constructed,
and the same Taylor radius works uniformly along the entire positive-time
orbit. The centered form gap is preserved there as well.

This completes another same-operator link, not the physical-scale limit.
The underlying thermodynamic functional is still fixed at SU(2) nome
`1/1024`; its smallness guards have not been proved along an AF trajectory.
Physical calibration, spectral/QFT interfaces, continuum existence and all
required groups remain open. All 15 new public axiom checks passed within
the constructive gate in focused safe checks; no full-tree run or raised limits.

**Previous analytic result:** [the original time action differentiates on the whole closed graph](lean/YMGap/Continuum/BF4ExactSlabThermodynamicGraphRealDerivative.lean).
For supplied original state/image representatives with `J u = T2 v`, a
computed positive radius gives `||u - A_t u - t v||^2 <= epsilon*t^2`
for every supplied positive real time below it. The proof uses the old
core Taylor estimate and the new image-norm control; no preimage limit
or division by a small time is needed.

[The dyadic derivative domain is also identified exactly](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDerivativeDomain.lean):
the graph computes a convergence rate for `2^n(u-S_n u) -> v`, and any
such modulus-bearing derivative forces `J u = T2 v`. The short converse
applies the bounded original `T2` and compares two constructed limits.

This is still SU(2), nome `1/1024`, fixed spacing, the original real
completion and T2-time units. Physical Hamiltonian/spectral identification,
physical scaling, continuum QFT and all required gauge groups remain
open. All 33 new public axiom checks passed within the constructive gate
in three focused safe checks; no full-tree run or raised limits.

**Previous analytic result:** [time increments are controlled by the derivative image on the whole original graph](lean/YMGap/Continuum/BF4ExactSlabThermodynamicGraphTimeBound.lean).
For every graph point `J u = T2 v` and every supplied positive real time,
`||u - A_t u||^2 <= t^2 ||v||^2`. The constant is one, with no small-time
restriction. Positive original mixed moments show that the squared dyadic
quotient norms increase to `||J y||^2`. Finite averages and the existing
two-coordinate graph approximants then pass this image-norm estimate to
the whole graph and the actual real-time action. No convergence of
preimages is assumed.

This supplies the missing uniform increment control for extending the
Taylor derivative to the whole graph; that differentiation is now proved
above. The scope is still the original real completion, SU(2), nome
`1/1024`, fixed spacing and T2-time units. Physical Hamiltonian/spectral
identification, scaling, continuum QFT and every required group remain
open. All 17 new public axiom checks passed within the constructive gate
in focused safe checks; no full-tree run or raised limits.

**Previous analytic result:** [the original derivative graph equals its real-pairing adjoint](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDerivativeClosedGraph.lean).
The equation `J u = T2 v` now defines a single-valued graph extending
`H0(T2 y) = J y`. One computed finite-sum degree approximates both `u`
and `v` by points of the old differentiated domain. These approximants
prove symmetry and positivity; the graph is closed under supplied Cauchy
rows and equals its adjoint graph for the original real pairing. The
centered form bound `B(v,u) >= (1/2)*B(u,u)` extends to the whole graph.

Generation/differentiation of the existing time action on this entire
domain still needs proof. The canonical physical Hamiltonian interface,
spectral interpretation, physical scaling, continuum QFT and all required
groups remain open. Scope: the original real completion, SU(2), nome
`1/1024`, fixed spacing and T2-time units. This is not a physical or Clay
mass-gap theorem. All 39 new public axiom checks passed within the
constructive gate in focused safe checks; no full-tree run or raised limits.

**Previous analytic result:** [the actual derivative has a centered form gap on its original dense domain](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDifferentiatedCore.lean).
The existing real-time derivative defines `H0(T2 y) = J y`. This rule is
well-defined, positive, symmetric, linear, and zero on the original vacuum.
For centered domain states it satisfies `B(H0 v,v) >= (1/2)*B(v,v)`.
The key argument is short: each dyadic refinement adds a nonnegative
square to the derivative form, so the existing transfer-gap bound passes
to the actual derivative. Supplied Cauchy graph rows also prove closability.

This is a **dense-domain form gap in T2-time units**, not yet a
self-adjoint spectral or physical mass-gap theorem. The graph extension
is now proved above; same-semigroup generation on it, physical scaling, continuum QFT
and every required gauge group remain open. The scope is SU(2), nome
`1/1024`, fixed spacing. The separate logarithmic candidate has not been
silently substituted or identified. All 33 new public axiom checks passed
within the constructive gate; no full-tree run or raised limits.

**Previous analytic result:** [the derivative estimate holds for positive real times](lean/YMGap/Continuum/BF4ExactSlabThermodynamicRealDerivative.lean).
For every supplied original state representative and `epsilon > 0`, a
computed positive radius controls the existing real-time action:
`||T2 y - A_t(T2 y) - t J y||^2 <= epsilon*t^2`.
The derivative vector `J y`, scalar multiplication, time action and norm
are all the original ones. Explicit Cauchy rows and their limit identities
pass the previous dyadic estimate to every represented positive real time
below the radius; no inverse-time or quotient-representative choice is used.

This is real-time differentiation on the original transfer range, in
**T2-time units**. Equality with the logarithmic candidate, self-adjoint
generation and physical scaling remain open. The scope is still SU(2),
nome `1/1024`, fixed spacing; continuum QFT and the all-group Clay target
are not proved. All 17 new public axiom checks passed within the
constructive gate in focused safe checks; no full-tree run or raised limits.

**Previous analytic result:** [one derivative estimate controls every dyadic time mesh](lean/YMGap/Continuum/BF4ExactSlabThermodynamicMeshDerivative.lean).
The actual multi-step quotient is a finite average of translated one-step
quotients. A length-independent norm bound and the original time-zero
continuity give a computed radius such that
`||T2 y - A_t(T2 y) - t J y||^2 <= epsilon*t^2`
for **every dyadic time** below that radius, including coarse mesh
presentations. `J y` is the previous constructed derivative limit, not a
supplied generator. All vectors and norms are the original ones.

The real-time extension is now proved above. Self-adjoint generation,
logarithmic identification and physical scaling remain open.
This is still SU(2), nome `1/1024`, fixed spacing and T2-time units;
continuum QFT and the all-group Clay target are not proved.
All 39 new public axiom checks passed in focused safe builds; no full-tree run.

**Previous analytic result:** [actual dyadic difference quotients converge on the original transfer range](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicDerivative.lean).
For the existing dyadic time operators `S_k`, the vectors
`Q_k y = 2^k (T2 y - S_k T2 y)` have a constructed limit in the
original completion, with explicit output representatives and an error
modulus. The key estimate is
`||Q_(k+1)y - Q_k y||^2 <= 4^(-k) ||y||^2`.
It follows from positive mixed moments and repeated finite telescoping,
without assuming a logarithm or a generator.

That milestone proved convergence along `h = 2^(-k)` in **T2-time units**;
the arbitrary-positive-real-increment estimate is now proved above.
Identification with the logarithmic candidate below, self-adjointness,
physical scaling, continuum QFT and the all-group Clay target remain open.
Scope remains SU(2), nome `1/1024`, fixed spacing. All 41 new public axiom
checks passed within the constructive gate; no full-tree run or raised limits.

**Previous analytic result:** [a constructed logarithmic generator candidate on an original dense domain](lean/YMGap/Continuum/BF4ExactSlabThermodynamicLogarithmicCore.lean).
The explicit polynomials `p_N(t) = sum_{k=1}^N t*(1-t)^k/k` have
a proved uniform tail bound `1/(N+1)`, including at zero. Their limit
constructs a bounded positive symmetric operator `L` on the original
completion. On the original dense range of `T2`, the rule
`H0(T2 y) = L y` is well-defined, rational-linear, symmetric, positive,
and annihilates the original vacuum. Domain approximants and operator
convergence moduli are computed.

This is a **generator candidate**, not yet the physical Hamiltonian.
Equality with the existing semigroup's time derivative and self-adjoint
closure remain open. No inverse bound or logarithm oracle is assumed.
The scope is still SU(2), nome `1/1024`, fixed spacing; physical scaling,
continuum QFT and the all-group Clay target remain open. All 45 new
constructive axiom checks passed in focused checks; no full-tree run.

**Previous analytic result:** [computed range density and time-zero continuity on the original completed space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicFullSpaceZeroContinuity.lean).
Every supplied original Cauchy state and positive squared-error tolerance
now compute a finite approximate preimage under the actual two-step
transfer. The residual is bounded at every degree above the computed
threshold. The existing positive-real-time action consequently tends to
the identity on the whole original space, with a computed radius. The
original two-step transfer is also proved injective.

The proof uses two rational tolerances, the transfer-relative test bound,
Cauchy--Schwarz, and finite telescoping. Dense samples and defect
contraction extend it to arbitrary original state data. No inverse is
assumed and no range-closure space replaces the original completion.

This remains SU(2), nome `1/1024`, fixed spacing. Moduli use supplied
Cauchy representatives; no representative is selected from a quotient.
There is no uniform inverse bound or new physical mass-gap claim.
The dense-domain candidate is now built above; its generator and
physical identification, spacing/coupling control, continuum QFT and the
all-group Clay target remain open. All 20 new constructive axiom checks
passed in focused checks; no full-tree run or raised resource limits.

**Previous analytic result:** [the transfer-relative test bound holds on the original completed space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTransferTestBound.lean).
For every original completed state `x` and fixed original test `f`,
`B(f,x)^2 <= bound(f) * B(T1 x,x)`. Here `B` is the original OS pairing,
`T1` is the actual geometric one-step transfer, and `bound(f)` is the
test's existing computed square cap. No heat-inverse premise or replacement
carrier is used.

The short argument combines adjacent-site reflection, weighted
Cauchy--Schwarz and the inward test. Every original action factor and the
same partition are retained. The test cap survives rebasing, so the existing
pairing limits extend the bound to all original completed `x`.

This is SU(2), nome `1/1024`, fixed spacing. The cap depends on the test;
the estimate is **not** a uniform lower spectral bound or a physical mass
gap. The residual modulus and full-space time-zero consequence are now
proved above. Physical Hamiltonian, continuum QFT and the all-group Clay
target remain open. All 19 constructive axiom checks for this earlier
increment passed; no full-tree run or raised resource limits.

**Previous analytic result:** [a bounded inward test is pinned to the original reflected pairing](lean/YMGap/Continuum/BF4ExactSlabSiteInwardTestNorm.lean).
Moving the reflection plane to the adjacent time slice permits an arbitrary
original plaquette expression to move one step inward, including its
boundary-touching terms. Its site-reflected mixed product is exactly the
original zero-lag product. Its site squared norm is bounded by the original
expression's computed square cap, with the full action and its partition
unchanged. The mixed identity reaches the existing thermodynamic form with
an explicit volume modulus.

This supplied the concrete test for the transfer-relative Cauchy--Schwarz
argument completed above. This earlier increment alone did not prove range
density or full-space time zero. The finite bound has explicit small-nome guards, while the
thermodynamic pin uses SU(2), nome `1/1024`, fixed spacing. It is a size bound,
not a mass-gap estimate. All 22 focused constructive axiom checks passed;
no full-tree run or raised resource limits. The physical Hamiltonian,
continuum QFT and all-group Clay target remain open.

**Previous analytic result:** [the original collar corrections now have a joint cutoff/order limit](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCorrectedState.lean).
The actual existing corrections `e * G_K(H_K-1)` converge in the **existing
OS completion**, with an explicit source-dependent, volume-independent
modulus. Both the heat cutoff and correction order increase together.
Multiplying those same finite samples by their same heat collar gives a
second convergent sequence whose completed state is **exactly the original e**.

The key estimate comes from one finite cancellation identity. It bounds the
difference of two corrections by their heat-factor difference and residuals,
without paying for growing polynomial degrees. The original full action and
partition normalization remain unchanged throughout the bulk and volume limits.

This result concerns the existing canonical source collar (at most 24 faces),
at SU(2) nome `1/1024` and fixed spacing. It does **not** define multiplication
on arbitrary OS classes or identify the corrected state with a time-transfer
preimage. Identifying that corrected state with a transfer preimage remains
open; the direct test estimate and time-zero proof above use another argument.
Physical Hamiltonian and the continuum/all-group Clay target remain open.
Twenty-nine focused constructive axiom checks passed; no full-tree run or
raised resource limits.

**Previous analytic result:** [local heat cutoffs converge in the original OS completion](lean/YMGap/Continuum/BF4ExactSlabThermodynamicLocalHeatState.lean).
For a fixed original source expression `e` and finite lower face region `R`,
the actual states `e * H_K(R)` now have a computed Cauchy modulus. Their
cutoff difference has squared OS norm at most
`bound(e) * (S(w, |R|) * 2^(-K))^2`, independently of volume, padding and
cutoff increment. The common heat prefix is cancelled before bounding the
signed remainder; the full original action keeps its own normalization.

This constructs a state in the **existing** thermodynamic completion and
certifies every sufficiently large cutoff's completed-distance error. The
actual at-most-five other faces touching a selected crossing link provide
a concrete instance. The test nome `w` has an explicit smallness guard;
the thermodynamic action remains SU(2), nome `1/1024`, fixed spacing.

This controls changing **heat-dressed states**, not changing actions,
inverse corrections or a bounded multiplication operator on all completed
states. The actual transfer preimage is still missing. Twenty-seven focused
constructive axiom checks passed; no full-tree run or raised resource limits.
Range/injectivity, full-space time zero, physical Hamiltonian, continuum
and the all-group Clay target remain open.

**Previous finite result:** [a positive local comparison on the full reflected action](lean/YMGap/Continuum/BF4ExactSlabReflectedLocalCutoff.lean).
The lower heat profile now determines its actual reflected upper profile.
The complete original action is identified with the same-channel Gram form,
so positivity and cutoff selection apply to **the same object**.

For one selected crossing face, a computed degree `D` gives
`w^(D*(D+2)) * reference <= original <= reference`, with positive factor
when `0 < w <= 1`. This holds for **every distant cutoff profile** and
every selected cutoff at least `D`. Only the touching lower collar is held
at cutoff `B`, with its upper partners reflected. The reference changes the
selected face's nome to one; every other heat factor remains unchanged.

`D` still depends on `B`, the insertion, nomes and extent. This is an
unnormalized finite comparison, **not** a completed OS-norm or mass-gap theorem.
The source-state heat-cutoff estimate above supplies part of the next
original-norm control, not a changed-action or range comparison. Forty-six
focused constructive axiom checks passed;
no full-tree run or raised resource limits. Range, full-space time zero,
physical Hamiltonian and continuum/Clay closure remain open.

**Previous finite result:** [local cutoff selection inside the full physical action](lean/YMGap/Continuum/BF4ExactSlabLocalBulkCutoff.lean).
After separating one selected face, at most **five** other faces touch its
exposed link. Holding their cutoff `B` fixed, the selected heat cutoff
stabilizes exactly at a computed threshold, for **every individual cutoff
choice on all detached faces**. Those interactions remain in the integral.
Equal cutoffs recover the pre-existing full-action numerator exactly.

The threshold still depends on the touching cutoff `B` and the insertion.
This is finite mixed-cutoff Haar selection, not a normalized OS-norm estimate;
arbitrary cutoff profiles are not asserted to preserve reflection positivity.
The reflection-compatible connection is now supplied above; controlling
the touching-cutoff error in the original thermodynamic norm remains open.
Twenty-five focused constructive axiom checks passed; no full-tree run or raised
resource limits. Transfer range, full-space time zero and the Clay target remain open.

**Previous finite result:** [only changed crossing faces pay the comparison factor](lean/YMGap/Continuum/BF4ExactSlabLocalInterfaceCoercivity.lean).
For `0 <= w <= 1`, the same reflected form, with all overlapping channels
retained, now has lower factor `w^(sum of K_f*(K_f+2) over changed faces)`.
If only those cutoffs are bounded by `N`, the factor `w^(N*(N+2)*S)` works
for every choice of untouched cutoffs; `S` counts the changed physical faces.
At common cutoff this is pinned to the **original full-action numerator**,
with the same bulk dressing. Untouched faces contribute exactly one.

This is an **unnormalized finite comparison**, not a completed OS-norm or
range estimate. The factor still depends on the changed cutoffs and coupling;
its reference retains finite nome-one packets only on the selected faces.
The next task is an observable-dependent comparison with controlled local
degrees and errors through the original bulk and volume limits.
Thirty focused constructive axiom checks passed; no full-tree run or raised
resource limits. The physical Hamiltonian and continuum/Clay target remain open.

**Previous geometric-time result:** [the constructed positive root equals actual one-step translation](lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricRootIdentification.lean).
On every state of the **existing** thermodynamic completion, `rootAction = T1`.
The constructive proof uses commuting polynomial approximations, the newly
proved geometric positivity, and the already constructed next root to reduce
the difference to zero squared norm. No spectral theorem or inverse is assumed.

The [existing positive-real-time action now recovers all original lattice steps](lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricTimePins.lean):
`A(n/2) = T_n`, including odd steps, independently of the supplied time
presentation. These are the **existing dimensionless units**: one semigroup
time unit is two lattice steps, not a proved physical-spacing calibration.

The next obstruction is a controlled range approximation for arbitrary
unshifted observables. **Injectivity, full-space time-zero continuity, the
physical Hamiltonian and continuum/Clay closure remain open.** SU(2) nome
`1/1024` and spacing stay fixed. Fourteen focused constructive axiom checks
passed; no full-tree run or raised resource limits.

**Previous positivity result:** [positivity of the actual completed one-step translation](lean/YMGap/Continuum/BF4ExactSlabThermodynamicOneStepPositivity.lean).
For every state in the **existing** thermodynamic completion,
`<T1 x, x> >= 0`. The proof identifies the literal geometric one-step insertion
with an even-slab reflected square, retaining the full original heat action.
An explicit odd/even volume comparison converges to the **existing**
thermodynamic pairing; its existing Cauchy limits then extend positivity to
the completion. Symmetry and composition give positivity at every integer lag.
No positive-root operator is substituted for geometric time translation.

This is at the existing SU(2) nome `1/1024` and fixed spacing. **Positivity is
not injectivity.** Identification of `T1` with the constructed positive square
root is now supplied above; arbitrary-state range control, full-space time zero, physical
Hamiltonian and continuum/Clay closure remain open. Twenty-three focused
constructive axiom checks passed; no full-tree run or raised resource limits.

**Previous geometry result:** [original-action comparison across odd/even slabs](lean/YMGap/Continuum/BF4ExactSlabCoordinateBoundaryComparison.lean).
The smaller slab is included without moving coordinates. Its original heat
factors and observable move through the same injective link-index map, and
its normalized expectation is recovered exactly from the kept target faces.
The added exterior action remains explicit. Proved geometric clearance and
the existing signed boundary estimate now bound the full even-slab expectation
against the **existing odd-slab expectation**, under explicit small-nome guards.

The literal one-step observable/reflection identity, receding-volume application
and completed positivity that were open at this checkpoint are now supplied
above. Full-space time zero and the Clay target remain open. Focused
constructive checks passed; no full-tree run or raised resource limits.

**Previous cutoff-limit result:** [normalized site reflection positivity](lean/YMGap/Continuum/BF4ExactSlabSiteExpectation.lean).
The heat cutoff is now removed at every fixed even volume, keeping the full
original action and its own partition normalization. Explicit moduli control
the normalized cutoff values and their constructive-real limit. The new
[face-list expectation](lean/YMGap/Continuum/BF4ExactSlabFaceSetExpectation.lean)
is proved equal to the existing expectation on every full odd slab.

The existing [boundary estimate now also passes through this normalization](lean/YMGap/Continuum/BF4ExactSlabFaceSetBoundaryComparison.lean)
for any physical face mask, with both partition factors cancelled exactly.
The inclusion, separation, one-step reflected insertion and its volume-limit
application that were open at this checkpoint are now supplied above.
Twenty-three focused constructive axiom checks passed at this earlier checkpoint;
no full-tree run or raised resource limits.

**Previous finite result:** [site reflection positivity with the full original heat action](lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean).
At every finite cutoff and even-slab size, the original reflected quadratic
equals a computed boundary square integrated against the original fixed-slice
heat weight. All lower, upper and shared-slice interactions are retained.
The identity holds for arbitrary rational nome; nonnegativity uses explicit
small-nome guards, discharged in particular at the existing nome `1/1024`.

This closed the finite heat-action step; identification with the existing
thermodynamic pairing and completed one-step positivity are now supplied above.
The distinct transfer-range approximation needed for full-space time zero
remains open. Twenty focused constructive axiom checks passed;
no full-tree run. The preceding [unweighted conditional square](lean/YMGap/Continuum/BF4ExactSlabSiteConditionalSquare.lean)
supplies the computed monomial decomposition used here.

**Previous completed-space result:** [the completed scalar test is exactly an original plaquette pairing](lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean).
On the **existing** thermodynamic OS completion,
`completedTest(x) = <x, (1/128) * original plaquette state>`.
The representing state is explicitly constructed; no representation theorem,
new state algebra or choice of representatives is assumed.

The proof retains the full original interacting action, removes the heat cutoff
using the same partition normalization, then compares the existing volume and
completion limits. The finite identity holds at every cutoff and rational
coupling; cutoff removal assumes `0 < w < 1`. The thermodynamic/completed result
uses the existing SU(2) nome `1/1024` at fixed spacing. **This is an identity,
not a coupling-uniform spectral estimate or a continuum mass gap.** Forty-five
focused constructive axiom checks passed; no full-tree run or raised limits.

This settles what the test measures: it adds no separating information beyond
the existing plaquette pairing. The next obstruction is an actual-transfer
approximation/range estimate for unshifted boundary states, not more wrappers
around this scalar test. Full-space time zero and continuum/Clay closure remain open.

**Supporting gauge calculation:** [the global scalar-probe image](lean/YMGap/Continuum/BF4ExactSlabBulkScalarVertexImage.lean)
and [full original-action invariance](lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean).
One common vertex assignment changes all original links, preserves the whole
supported product-Haar functional and every spin character, and retains
neighboring action factors even when they share probe links.

**Previous local calculation:** [what the scalar test measures under local gauge averaging](lean/YMGap/Continuum/BF4ExactSlabBulkScalarGaugeAverage.lean).
Three exact SU(2) Schur contractions turn its vertex-gauged four-link product
into the **original plaquette character divided by 128**. This holds on the
actual translated slab links, retaining arbitrary dependence on all original
links. Only the three auxiliary gauge variables are integrated. The full-action
identity and completed identification above now consume this local calculation.
Neither the local calculation nor the completed identity supplies a transfer
preimage or mass gap. Focused constructive checks passed; no full-tree run.

**Previous completed-space result:** [the scalar test on the original completed OS carrier](lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean).
Common-volume comparison and null descent make the test independent of the
original observable presentation. An explicit continuity modulus extends it to
the **existing** thermodynamic completion, with
`|L(x)-L(y)|^2 <= original squared distance(x,y)`. Its values agree with the
previous concrete test; no representatives are chosen and no state algebra is
enlarged. Two focused modules passed 49 constructive axiom checks; no full-tree
run. A useful comparison with actual time translation, separation by a rich
test family, and transfer range density remain open. This is not a mass gap.

**Previous volume result:** [a scalar dual test through the thermodynamic limit](lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean).
Translating the original state and scalar-link test together gives a constructed
volume limit with an explicit geometric error bound at the existing small nome.
Its value satisfies `L(e)^2 <= formLimit(e,e)`: the norm is the **original
thermodynamic OS norm**, with the full action retained. Twenty-five focused
constructive axiom checks passed; no full-tree run. Its quotient compatibility
and completed extension are now supplied above. A useful actual-transfer
identity remains open; one bounded test does not prove separation or range density.

**Previous cutoff result:** [full-channel auxiliary tests through cutoff removal](lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean).
The temporal gauge change fixes the concrete lower-link test. Its fully dressed
amplitude is therefore an existing **original-action numerator**, with every
crossing channel retained. This supplies its cutoff limit and explicit modulus;
the coefficient-one bound survives in the original normalized OS norm. The
test descends to the existing cutoff-removed finite-volume quotient.
Twenty focused constructive axiom checks passed; no full-tree run.
The volume limit for the concrete scalar test is now supplied above;
the actual time-transfer comparison remains open.
This is not a spectral gap or a continuum result.

**Previous finite estimate:** [normalized auxiliary tests on the original finite OS quotient](lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean).
Keeping the full lower action gives `test energy <= test cap * original Z`;
exact normalization cancels the partition. The resulting dual-test bound uses
the **original reflected norm**, without requiring the auxiliary polynomial to
be a plaquette expression. A concrete spatial-coordinate product has coefficient
one at every slab and cutoff under explicit small-nome guards. Tests descend
to the existing finite-cutoff null quotient, and the unit test has value one.
Twenty-three focused constructive axiom checks passed; no full-tree run.
That finite estimate alone supplied neither test limits nor time-transfer comparison.
This is a size bound, **not** a coupling-uniform spectral gap or a continuum result.

**Previous local result:** [exact quadratic heat transmission and its polynomial inverse](lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean).
For the original relative one-link heat kernel, trace-free quadratic modes
transmit by `w^8` at every cutoff `K >= 2`, with arbitrary retained polynomial
insertions. The inverse is explicit and coupling-dependent. A checked example
shows that multiplying two degree-one images gives the wrong answer; cutoff
one also annihilates a quadratic mode with nonzero ordinary Haar norm.
Nineteen focused constructive axiom checks passed; no full-tree run.
These are local kernel identities, **not** preimages for the interacting OS
transfer. The full-action boundary-state comparison remains open.

**Established route correction:** [a checked obstruction to exact plaquette-only recoding](lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean).
Two explicit unit-quaternion configurations agree on every observable in the
existing plaquette-generated algebra, but an outer-rectangle character has
values `-2` and `0` on them. The proof uses the **original slab coordinates and
evaluator**. Thus exact pointwise/coefficient recoding of this rectangle—or its
half-normalization—into that algebra is impossible. This rules out one proposed
boundary compiler, **not** OS-norm approximation or the Yang--Mills goal.
Nineteen focused constructive axiom checks passed; no full-tree run. The next
comparison must concern the unchanged original state and its actual OS norm,
with the full action retained.

**Previous local calculation:** [adjacent-plaquette shared-link integration](lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteGluing.lean).
Integrating the shared link of two selected fundamental plaquettes gives
exactly half the outer-rectangle character, with all six outer links retained.
A symbolic Schur proof avoids expanding those paths; arbitrary spectator
polynomials independent of the shared link are preserved. The selected heat
factor is explicitly `2*w^6`, not a coupling-uniform gap. Two focused modules
passed the constructive axiom gate; no full-tree run. Representing the resulting
boundary observable in the original state algebra, retaining the full action,
and proving an actual transfer-range comparison remain open.

**Established interior result:** [literal time preimages for original interior observables](lean/YMGap/Continuum/BF4ExactSlabThermodynamicInteriorTimePreimage.lean).
A decidable support condition identifies plaquette expressions strictly inside
the reflection boundary. A computed inward shift is their exact geometric
one-step preimage: translating it back gives the **same polynomial on the same
link variables**, before taking any measure or quotient. The preceding range
estimate then supplies approximate two-step preimages and a time-zero modulus.
Eighteen focused axiom checks passed within `{propext, Quot.sound}`; no full-tree
run. Ordinary box enlargement preserves the condition, so it cannot remove a
boundary contact. The test is sufficient, not a characterization of the range.
Boundary-touching observables, range density, full-space time zero, the physical
Hamiltonian and continuum/Clay closure remain open.

**Established range estimate:** [time-zero continuity on the actual geometric one-step range](lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricRangeContinuity.lean).
A finite telescoping argument proves
`n * ||(I-T2)^n T1 x||^2 <= ||x||^2` for the **original** geometric operators.
It computes approximate two-step preimages of one-step states, then uses
the existing time-zero modulus and contraction to prove continuity there.
No exact inverse or identification of geometric T1 with the positive square
root is assumed. Sixteen focused axiom checks passed within
`{propext, Quot.sound}`; no full-tree run. Approximating arbitrary unshifted
states by this range remains open, as do full-space time zero, the physical
Hamiltonian, continuum control and the Clay target.

**Latest route review:** [the missing actual-transfer comparison](audits/AUDIT-T2-TEST-COMPARISON.md).
The instructions now distinguish an **original observable or transfer preimage**
from an **auxiliary dual test**. Existing finite-cutoff bounds permit arbitrary
polynomial dual tests; exact plaquette-only recoding is not required for that
use. The estimates above supply original-partition control and, for the concrete
full-channel test, cutoff removal and original finite-volume null descent.
The concrete scalar test now also has a volume limit, original quotient descent
and a bounded completed extension. Actual-transfer comparison and a sufficiently
rich test family remain open; the audit separates these from the checked limits.

An earlier Lean-checked counterexample shows why finite strict positivity and a
common excited-sector upper bound do not alone exclude a limit kernel.
It is not a Yang--Mills model or a physical closure. The next target is
constructive approximate range for the **actual** thermodynamic transfer;
candidate preimages already exist, but their residuals need a computable
smallness estimate on a dense original family. Exact test preimages need not
be demanded. Classical review helped distinguish these obligations without
changing the constructive proof substrate. The counterexample passed 21
focused axiom checks; no full-tree audit was run.

**Established separation:** [collar tests separate the original thermodynamic completed states](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCollarTestDensity.lean).
The same source collar and correction now retain their geometric OS error
under actual bulk enlargement, and the bound passes through the existing
thermodynamic form limit. Explicit approximants prove separation by the family
of source-collar-dressed tests, ranging over source bases. This is the original
fixed-spacing completion, not a new carrier or a continuum limit.
Two modules passed 14 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. The remaining transfer question is whether an actual
two-step-transfer zero mode vanishes against these tests. That implication,
transfer range density, physical time zero, and the continuum/Clay target
remain open; test-family density alone does not supply them.

**Established finite-slab result:** [collar-dressed tests distinguish the same original completed states](lean/YMGap/Continuum/BF4ExactSlabCollarDressedTestDensity.lean).
At each finite slab, the actual OS squared error of `H * (e * G_n) - e`
is at most `bound(e) * 2^(-2n)`. A computed correction order and the
existing Cauchy modulus therefore produce collar-dressed approximants to
every supplied completed-state representative. Two states agreeing on all
these tests are equal. No OS multiplication operator or quotient
representative selection is assumed.
Two modules passed 23 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. The collar uses nome `1/1024`; these size/density results
hold in every existing finite-slab action with `0 < w < 1`, not as a
coupling-uniform spectral gap. Growing-volume transport is now supplied above;
identification of tests as actual time-transfer images remains open.

**Established realization:** [collar corrections are admissible original observables](lean/YMGap/Continuum/BF4ExactSlabOriginalCollarCorrector.lean).
Finite heat products and their geometric corrections now live in the existing
plaquette-expression algebra, with their lower and reflected upper evaluations
proved equal to the actual heat/correction polynomials. Both correction
evaluations have certified cap 2. Multiplying an original expression by this
correction gives an **existing original OS test amplitude** exactly equal to
the previously bounded corrected integral. The computed order therefore gives
error at most `epsilon * Zsp` against the existing reference amplitude.
Two modules passed 24 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. This closes finite representability, not state separation:
the observable is changed and depends on the heat cutoff. Cutoff-compatible
limits and a comparison that detects the **unchanged thermodynamic state**
remain open, as do transfer injectivity and the continuum/Clay target.

**Established estimate:** [finite collar corrections with spectator-relative error control](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCollarCorrection.lean).
An exact geometric identity now approximately cancels the actual local
heat collar. Its correction polynomial is bounded by 2 at every order;
its ordinary squared test norm costs at most a factor 4 against the same
positive background. For every original plaquette expression, a computed
order gives error at most `epsilon * Zsp`, where `Zsp` is the **original
full spectator partition**. That order is unchanged by actual bulk/time
embedding and does not use a partition reciprocal or the action cutoff.
Three modules passed 46 focused axiom checks, three axiom-free and the
rest within `{propext, Quot.sound}`; no full-tree run.
The application fixes the nome at `1/1024` and the existing translated
24-face collar. The correction changes the insertion and depends on the
heat cutoff. Admissible finite original realizations are now proved above;
their cutoff limits and separation of the same thermodynamic states remain
open. The ordinary weighted square bound is **not** an OS operator-norm
bound, and no transfer inverse or continuum/Clay result is claimed.

**Established integral bridge:** [all-spin spectator integrals reach the original normalized packets](lean/YMGap/Continuum/BF4ExactSlabAllSpinSpectatorIntegralLimit.lean).
For arbitrary selected spins and crossing faces, the actual retained
integrand is now identified with its selected positive weight, reflected
channel square, and **complete spectator heat product**. All factors keep
their original shared link variables. With both observables dressed by the
original bulk action, its mixed pairing obeys a constant-one original-form
bound. Its diagonal converges to the existing retained packet with an
explicit cutoff; the same original partition reciprocal gives a computed
normalized sample and error guarantee.
Three modules passed 39 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. The normalization threshold explicitly depends on the
finite-volume reciprocal ceiling. This does **not** establish a surviving
general packet floor, thermodynamic separation, transfer injectivity, or
continuum/Clay closure. Cancellation-preserving growing-volume control
remains the next frontier.

**Established geometric bridge:** [actual growing channel polynomials and their original-action response](lean/YMGap/Continuum/BF4ExactSlabGrowingChannelExterior.lean).
Every selected all-spin channel now follows the **actual physical link
embedding**, together with the translated observable. Moving the source's
entire lower interaction along with them preserves its amplitude exactly;
a source-derived numerical cutoff works at every padding for this interior
integral. The full enlarged lower action is separately pinned to that
interior action times all added heat factors, with shared links retained.
The resulting amplitude difference has an explicit modulus and is proved
equal, in the limit, to the difference of the original coefficient limits.
Four modules passed 46 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. This closes the geometric polynomial bridge for this
enlargement, **not** normalized volume control. General full-spectator
packet estimates, thermodynamic separating data, transfer injectivity,
full-space time-zero continuity and the continuum/Clay target remain open.

**Established retention:** [arbitrary-spin local channels retain the full surrounding interface](lean/YMGap/Continuum/BF4ExactSlabAllSpinSpectatorRetention.lean).
An original Gram channel can now be followed to the physically shifted
crossing face in every larger slab, preserving its spin, branch and exact
heat weight. Selecting such channels need not freeze the surroundings:
every unselected face retains its **complete original channel expansion**.
The resulting packet has an explicit original-action bulk-limit modulus,
is nonnegative, and is bounded by the **same original normalized OS norm**.
Three modules passed 50 focused axiom checks, 18 axiom-free and the rest
within `{propext, Quot.sound}`; no full-tree run.
Only the selected channel's heat weight is independent of enlargement;
its interacting amplitude and the original partition reciprocal are not.
Geometric polynomial pullback is now proved above. Normalized growing-volume
control remains open, as do thermodynamic coefficient separation, transfer injectivity,
full-space time-zero continuity and the continuum/Clay target.

**Established scalar bridge:** [original channel packets approximate actual thermodynamic translated norms](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTranslatedChannelPacket.lean).
For any dense presentation, integer time lag and positive rational
`epsilon`, the construction now computes a volume, crossing cutoff and
numerical precision. Its actual original channel-square sample encloses
the **existing translated thermodynamic state's squared norm** in
`[sample - epsilon, sample + epsilon]`, including the actual two-step
transfer. The original partition reciprocal is retained; its
finite-volume dependence is explicit.
Two modules passed 27 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. This is at the existing nome `1/1024` and fixed spacing.
The channel family changes with volume: scalar norm approximation does
not yet transport separating coefficients or prove transfer injectivity,
range density, continuity at time zero, or the continuum/Clay target.

**Established separation:** [original channel coefficients distinguish original completed states](lean/YMGap/Continuum/BF4ExactSlabCompletedChannelSeparation.lean).
At each finite slab and `0 < w < 1`, two states of the original completed
OS space are now proved equal **if and only if all their actual channel
coefficients agree**. The proof bounds each entire retained packet by
the original normalized norm, uses the existing dense packet reconstruction,
and passes through the original explicit-modulus state approximation.
It assumes neither a channel resolution nor a transfer inverse.
Two modules passed 17 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. Scalar packet approximation through growing volume and
actual time translation is now constructed above; coefficient-level
transport remains open. The active two-step transfer
acts on the **thermodynamic** completion; this finite-slab separation
does not prove its injectivity, range density, or continuity at time zero.
The physical Hamiltonian, continuum control and Clay target remain open.

**Established extension:** [original channel coefficients extend to the original completed OS space](lean/YMGap/Continuum/BF4ExactSlabIntrinsicChannelCompletion.lean).
At fixed finite volume, every actual packet-leaf coefficient is now a
well-defined functional on the **same original null quotient and completion**.
The construction retains explicit outer and numerical Cauchy moduli,
agrees with the original coefficient on dense expressions, and preserves
addition and rational scalar multiplication. The same computed positive
factor gives `F*A(x)² <= <x,x>` for every completed state `x`.
The tolerance `F*epsilon²/2` controls coefficient differences; a computed
precision index selects an actual dense approximant with that accuracy.
Two modules passed 46 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. Whole-packet control and completed separation are now
proved above. Growing-volume and actual time-translation compatibility
remain open for this coefficient construction.
The floor depends on the channel, heat parameter and finite volume; no
volume/beta/spacing-uniform gap or continuum/Clay theorem is claimed.

**Established norm bounds:** [every actual packet-leaf coefficient is bounded by the original OS form](lean/YMGap/Continuum/BF4ExactSlabIntrinsicChannelNormBound.lean).
Enlarging the crossing cutoff retains the original coefficients and adds
nonnegative channel contributions, with shared links preserved. Every
actual leaf has a strictly positive weight and remains bounded by the
original full action through bulk cutoff removal. Normalizing by the
**same original partition function** gives `F*A(e)² <= form(e,e)`, with
a computed `F > 0` independent of the observable `e`.
An embedded dense expression is now proved zero **if and only if** all
its actual packet-leaf coefficients vanish.
Three modules passed 35 focused axiom checks within `{propext, Quot.sound}`
(three axiom-free); no full-tree run. The coefficient extensions are now
constructed above, as is completed separation. Actual time-translation
compatibility remains open. `F` depends on the leaf, heat parameter and finite volume;
this is not a uniform transfer gap or a continuum/Clay result.

**Established reconstruction:** [actual channel squares reconstruct the original reflected numerator](lean/YMGap/Continuum/BF4ExactSlabOriginalChannelReconstruction.lean).
At fixed finite volume, each crossing packet's bulk limit equals its
actual finite sum of nonnegative-weight channel amplitudes squared. The
amplitudes use the original lower action, not a replacement measure.
These sums approximate the original full reflected numerator with
computed packet and numerical thresholds. If every actual packet-leaf
coefficient of a dense expression vanishes, its **original normalized
OS form and embedded completed state are zero**.
Two modules passed 28 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. The coefficient norm bounds and reverse null implication
are now proved above, as are completed coefficient descent and separation.
Compatibility with actual time translation remains open. This is not yet a
Hilbert-space channel resolution or a zero-transfer-kernel theorem.
Volume/physical-scale control and continuum/Clay remain open.

**Established two-stage limit:** [finite crossing packets recover the original full-action limit](lean/YMGap/Continuum/BF4ExactSlabCrossingPacketBulkLimit.lean).
An explicit crossing-tail cutoff now works for **every bulk spin cutoff**,
at fixed heat parameters, volume and observable. The bulk limit of each
retained finite crossing packet is constructed with a numerical modulus.
These packet limits then converge to the pre-existing original full-action
reflected numerator limit, with both stage and representative thresholds
returned as data. All shared links and original heat factors are retained.
Two modules passed 30 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. Each limiting packet is now identified with its finite
sum of limiting channel squares above. Completed channel resolution,
transfer range density, volume/physical-scale control and continuum/Clay
remain open. The bound is **not** uniform in volume, beta or spacing.

**Established channel limits:** [all-spin channel bounds survive the original bulk limit](lean/YMGap/Continuum/BF4ExactSlabRetainedChannelBulkLimit.lean).
At each finite volume, an arbitrary fixed spin and actual Gram channel
on every crossing face retains its exact positive heat weight `W` at
all sufficiently large cutoffs. Its original bulk-dressed amplitude has
a constructed limit `A`, with explicit numerical moduli, and the proof
gives `W*A² <= Q_original` after **all** action cutoffs are removed
together. Thus an original OS-null polynomial has zero amplitude in
every such channel. No uniform lower bound over channels is assumed.
Two modules passed 34 focused axiom checks within `{propext, Quot.sound}`
(one axiom-free); no full-tree run.
Crossing-packet tail control and reconstruction from limiting channel
squares are now proved above. Next: completed coefficient descent and
compatibility with actual time translation.
Completed channel resolution, volume control, zero completed transfer kernel,
full-space time-zero continuity, physical scaling and continuum/Clay
remain open.

**Established fixed-insertion limit:** [crossing-cutoff removal for each fixed original bulk insertion](lean/YMGap/Continuum/BF4ExactSlabSelectedInterfaceCoercivity.lean).
The bulk and crossing cutoffs are now independently pinned to the
original action. For each fixed bulk-dressed observable, a computed
degree cutoff `N` makes every later crossing pairing exactly constant.
The positive comparison factor is therefore `v^(N*(N+2)*F)`, independent
of every later crossing cutoff `K >= N`; the reference and observable
stay fixed. The exact original-interface limit and nullity equivalence
are retained. Two modules passed 20 focused axiom checks within
`{propext, Quot.sound}`; no full-tree run.
This removes only the crossing cutoff with the bulk insertion fixed.
Growing bulk cutoffs, volume, completed transfer range/density,
full-space time-zero continuity, physical scaling and continuum/Clay
remain open. Fixed-channel control through the original bulk limit is
now proved above; no uniform positive bulk/volume floor is assumed.

**Established finite comparison:** [an explicit finite interface comparison for the original action](lean/YMGap/Continuum/BF4ExactSlabOriginalInterfaceCoercivity.lean).
At `0 < w <= 1`, the original reflected numerator is bounded above
by its retained-bulk reference and below by that reference times
`w^(K*(K+2)*F)`, where `K` is the spin cutoff and `F` counts the
actual crossing faces. Only the crossing coefficients change in the
reference: the observable, original lower bulk interaction and shared
links are retained. The two finite forms have exactly the same nullity.
Three modules passed 34 focused axiom checks within `{propext, Quot.sound}`
(two axiom-free); no full-tree run. The positive factor is explicitly
coupling-, cutoff- and volume-dependent. This is not a uniform limit
bound, a transfer inverse, or a proof of a zero completed transfer kernel.
Crossing-cutoff removal for each fixed insertion is now proved above.
Full-space time-zero continuity, physical scaling and continuum/Clay
remain open.

**Established range certificates:** [finite original-moment certificates for continuity at zero](lean/YMGap/Continuum/BF4ExactSlabThermodynamicZeroTimeCertificate.lean).
With `D = I - T2`, a computed finite sum satisfies
`T2 (x + D x + ... + D^(n-1) x) + D^n x = x`.
Its squared approximation error is exactly the existing original moment
`m_x(0,2n)`. A finite rational sample, checked against that moment's
explicit modulus, can therefore certify a time-zero continuity radius
for the **same original state**. The test is not presumed to succeed:
acceptance is constructed for every actual `T2` output, using the proved
bound `n ||D^n T2 y||² <= ||y||²`. Any supplied sufficiently close
original transfer output also computes an accepted test.
Three modules passed 40 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. Next: prove residual decay for every original dense
observable. Neither full range density nor a zero transfer kernel is
established; a possible kernel vector's residual is proved unchanged.
Full-space continuity at zero, physical Hamiltonian identification and
continuum/Clay remain open. Nome and spacing are fixed.

**Established continuity:** [quantitative real-time continuity on the original space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveRealLocalContinuity.lean).
At every positive real time, the same operator action now has computed
time and state continuity radii. A uniform estimate away from zero
compares actual real-time values, independently of their numerical
representations. Local bounds ensure that a sufficiently nearby time
automatically stays in that interval. The semigroup law also gives
[continuity at zero on every original positive-time range](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.lean),
including the range of the pre-existing `T2`, with explicit output data
and radii. Four modules passed 41 focused axiom checks within
`{propext, Quot.sound}` (two axiom-free); no full-tree run.
Next: the full-space time-zero boundary. Positive-time range density
and a zero transfer kernel are not proved or assumed. Geometric `T1`
identification, the Hamiltonian, physical-scale control and continuum/Clay
remain open; nome and spacing are fixed.

**Established semigroup:** [positive real-time composition on the original space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveRealSemigroup.lean).
Addition of positive real times now gives composition of the existing
operators: `A(s+t)x = A(s)(A(t)x)`. Time addition is pinned to the
existing real-number addition. The proof passes an exact dyadic
inner-product identity through computed Cauchy limits; it requires no
inverse or supplied spectral model. The same original vacuum complement
is invariant and carries the same semigroup. Output representatives,
sum-time convergence rates and mixed-time moment identities are explicit.
Three modules passed 47 focused axiom checks within `{propext, Quot.sound}`
(three axiom-free); no full-tree run.
Quantitative positive-time and range-zero continuity are now proved above.
Full-space continuity at zero, geometric `T1`
identification, the Hamiltonian, physical-scale control and continuum/Clay
remain open. Nome and spacing are fixed.

**Established operator family:** [positive real-time operators on the original space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveTimePins.lean).
Every supplied positive real time, with explicit numerical Cauchy data,
now constructs an operator on the same completed state space. Certified
dyadic rounding and the energy estimate give computed convergence rates
and output representatives. Different representations of the same time
give the same operator; positive dyadic times recover the existing
operators exactly. Positivity, symmetry, contraction, rational linearity,
the original unit and centering are retained.
Four modules passed 79 focused axiom checks within `{propext, Quot.sound}`
(13 axiom-free); no full-tree run.
The time-addition/composition law is now proved above.
Full-space continuity at zero, geometric `T1` identification, the
Hamiltonian, physical-scale control and continuum/Clay remain open;
nome and spacing are fixed.

**Established energy estimate:** [quantitative positive-time continuity on the original space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicEnergy.lean).
A finite energy argument now proves
`||A(t)A(s)x - A(s)x||² <= 2^(-k)||x||²`
whenever dyadic `t <= s/2^k`. The next finer square root controls each
step's norm loss; telescoping and contraction give the estimate without
an inverse or spectral representation. Different time meshes are compared
by exact refinement. A supplied state representative and tolerance produce
an explicit depth threshold. This proves positive-time right continuity
on every original state, and continuity at zero on the range of `T2`.
One module passed 29 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run.
Controlled positive-time Cauchy families and the positive-real-time
operator family and its time-addition law are now constructed above.
Density of the `T2` range, zero transfer kernel and full-space continuity
at zero are not proved. Geometric `T1` identification, the Hamiltonian,
physical-scale control and continuum/Clay remain open; nome and spacing
are fixed.

**Established dyadic semigroup:** [representation-independent time on the original space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicSemigroup.lean).
Different mesh descriptions of the same nonnegative dyadic time now give
exactly the same operator. Addition of times gives composition, on the
same original completed carrier. Positivity, symmetry, contraction,
rational linearity, centering and the original unit are preserved.
Whole time `n` is exactly the existing geometric time `2*n`.
Supplied time and state representatives construct output Cauchy data;
no representative is selected from a quotient.
Two modules passed 51 focused axiom checks within `{propext, Quot.sound}`
(six axiom-free); no full-tree run.
Quantitative positive-time right continuity and zero-time continuity on
the `T2` range are now proved above. Full-space continuity at zero and a
strongly continuous nonnegative-time semigroup are not established;
the possible kernel of `T2` remains open. Geometric `T1` identification, the Hamiltonian,
physical-scale control and continuum/Clay remain open; nome and spacing
are fixed.

**Established coherent meshes:** [positive dyadic time meshes on the original space](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicTimeMeshes.lean).
Repeated roots are now constructed at every finite depth with explicit
polynomial Cauchy rates. The first generators are exactly the existing
`T2` and `S`; every finer generator squares to its parent. Each mesh is a
positive symmetric contraction semigroup, fixes the same original unit,
and preserves centering. Doubling the step count gives exactly the same
operator on the next finer mesh; the coarsest mesh equals all original
even geometric times. Output representatives are constructed.
Three modules passed 70 focused axiom checks within `{propext, Quot.sound}`
(six axiom-free); no full-tree run.
Representation-independent dyadic-time indexing, its addition law and
quantitative positive-time right continuity are now proved above. Full-space
continuity at zero remains open: all generators retain the possible kernel of `T2`.
Geometric `T1` identification, physical-scale control and continuum/Clay
remain open; nome and spacing are fixed.

**Established original square root:** [a positive square root of the original two-step transfer is constructed](lean/YMGap/Continuum/BF4ExactSlabThermodynamicSquareRootAction.lean).
The explicit iteration `p₀(t)=0`, `pₙ₊₁=pₙ+(t-pₙ²)/2` has a proved
uniform Cauchy rate on `[0,1]`, including zero. Its polynomial limits
define a positive symmetric contraction `S` on the full original space,
and Lean proves `S(Sx)=T2x` through exact original pairing limits.
The existing unit complement is invariant; there `||Sv||² <= ½||v||²`
follows from the previously proved fixed-spacing `T2` gap.
The output representatives and convergence rates are explicit.
Three modules passed 64 focused axiom checks within `{propext, Quot.sound}`
(nine axiom-free); two older-timestamp rational dependencies were also
validated by narrow build targets. No full-tree run.
Original-unit compatibility and coherent finite dyadic mesh refinement
are now proved above. `S` is not yet identified with geometric `T1`;
`ker(S)=ker(T2)` is proved, but neither kernel is proved zero.
Nome and spacing remain fixed; physical-scale control and continuum/Clay
remain open.

**Established uniform-limit action:** [uniform polynomial limits act on the full original carrier](lean/YMGap/Continuum/BF4ExactSlabThermodynamicUniformPolynomialAction.lean),
with [computed boundedness and symmetric linear laws](lean/YMGap/Continuum/BF4ExactSlabThermodynamicUniformPolynomialLinear.lean).
An explicit uniform Cauchy rate now constructs the limiting operator,
output representatives and convergence rates. Equivalent sequences give
the same action; constant and Bernstein sequences recover the existing
polynomial and continuous operators. Boundedness needs no extra hypothesis:
one explicitly indexed polynomial controls the tail and supplies a
continuity modulus. Two modules passed 34 focused axiom checks within
`{propext, Quot.sound}` (two axiom-free); no full-tree run.
The explicit square-root sequence and original operator square identity
are now constructed above. Geometric half-time identification and time
injectivity remain open. Nome and spacing remain fixed;
physical-scale control and continuum/Clay remain open.

**Established projection pin:** [an explicit continuous filter equals the original unit projection](lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousUnitProjection.lean).
For `h(t) = clamp(4t-3, 0, 1)`, Lean proves `h(T2)x = unitProjection x`
for every original completed state. The filter fixes the original unit.
On its complement, the filter's `3/4` lower form bound conflicts with the
existing `1/2` upper bound unless the filtered vector is zero. All symbol
data, output representatives and Bernstein convergence rates are explicit;
no spectral projection is assumed. Three modules passed 40 focused axiom
checks within `{propext, Quot.sound}` (four axiom-free); no full-tree run.
Original-carrier action for represented uniform polynomial limits is now
constructed above, preparing for CReal-valued symbols. This is a
fixed-nome, fixed-spacing result; time injectivity, physical-scale control
and continuum/Clay remain open.

**Established full-carrier calculus:** [multiplication](lean/YMGap/Continuum/BF4ExactSlabThermodynamicAllVectorMultiplication.lean),
[positive symbol algebra](lean/YMGap/Continuum/BF4ExactSlabThermodynamicAllVectorSymbolOrder.lean),
and the [original unit-complement restriction](lean/YMGap/Continuum/BF4ExactSlabThermodynamicAllVectorCenteredCalculus.lean)
now hold on the full original completed carrier.
`(FG)(T2)x = F(T2)G(T2)x`; nonnegative symbols give nonnegative forms,
and `|F-G| <= M` on `[0,1]` gives the sharp bound
`||F(T2)x-G(T2)x||² <= M² ||x||²`. Continuous action commutes with the
existing centering map, so the original unit complement is invariant.
The previously proved fixed-spacing gap applies to those filtered states;
this is not a new physical-scale gap. Three modules passed 35 focused
axiom checks within `{propext, Quot.sound}`; no full-tree run.
The continuous unit-isolating filter and its equality with the existing
unit projection are now proved above. Nome and spacing remain fixed;
physical-scale control and continuum/Clay remain open.

**Established full-carrier action:** [continuous action is constructed on the full original completed carrier](lean/YMGap/Continuum/BF4ExactSlabThermodynamicAllVectorContinuousAction.lean),
with [bounded symmetric rational-linear operator laws](lean/YMGap/Continuum/BF4ExactSlabThermodynamicAllVectorContinuousLinear.lean).
Bernstein approximations now define `F(T2)x` for every original completed
state, with explicit output representatives and convergence rates for
supplied input representatives. The value is independent of the representative,
recovers the original polynomial operators, and agrees with the earlier
cyclic action. The bound `||F(T2)x||² <= F.bound² ||x||²` retains the
original norm; no assumption that one probe generates the whole space is
needed. Two modules passed 30 focused axiom checks within
`{propext, Quot.sound}`; no full-tree run. Full-space multiplication and
form-order laws are now proved above. Nome and spacing remain fixed; physical-scale
control and continuum/Clay remain open.

**Established polynomial bound:** [sharp polynomial bounds hold on the full original completed carrier](lean/YMGap/Continuum/BF4ExactSlabThermodynamicAllVectorPolynomialBound.lean).
For every original completed vector `x`, `|p| <= M` on `[0,1]` gives
`||p(T2)x||² <= M² ||x||²`. Positive Bernstein rows have total mass
`||x||²`; their signed-polynomial moments converge to the same original
operator forms with explicit rates. No normalization or assumption that
one probe generates the whole carrier is needed. The final bound has
no coefficient-size or computed norm-cap factor.
Three modules passed 53 focused axiom checks within `{propext, Quot.sound}`
(one axiom-free); no full-tree run. Continuous action on the full carrier
is now constructed above. Nome and spacing remain fixed; physical-scale control and
continuum/Clay remain open.

**Established cyclic calculus:** [constructed symbol algebra gives sharp uniform-error bounds for the original actions](lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousUniformBound.lean).
On represented original cyclic states, `|F-G| <= M` on `[0,1]` implies
`||F(T2)x-G(T2)x||² <= M² ||x||²`. Sums, constants, scaling and differences
have constructed continuity data and act as the original completed
operations. An explicit uniform symbol-convergence rate gives an explicit
action-convergence rate, with the original target representative retained.
Three modules passed 35 focused axiom checks within `{propext, Quot.sound}`
(one axiom-free); no full-tree run. Full-carrier polynomial bounds are now
proved above. Continuous action in this checkpoint remains on the
represented cyclic sector; physical-scale control and continuum/Clay
remain open.

**Established multiplication:** [products of arbitrary admissible continuous symbols have fully constructed data and compose as the original operators](lean/YMGap/Continuum/BF4ExactSlabThermodynamicProductSymbol.lean).
The product symbol, bound, continuity modulus and vanishing selector are
computed from those of `F` and `G`; `(FG)(T2)x = F(T2)G(T2)x` requires no
extra product-symbol package. A finite rational encoding handles the fact
that the input continuity bounds need not be monotone. The construction
retains original action representatives and explicit convergence rates.
Two modules passed 27 focused axiom checks within `{propext, Quot.sound}`
(four axiom-free); no full-tree run. Sum/unit/scalar/difference algebra
is now proved above; full-carrier and continuum/Clay bridges remain open.
SU(2) nome and spacing stay fixed;
this is not a beta/spacing-uniform physical gap.

**Established form laws:** [continuous action is symmetric and preserves quadratic-form order on the represented original cyclic sector](lean/YMGap/Continuum/BF4ExactSlabThermodynamicContinuousFormOrder.lean).
If `F <= G` on `[0,1]`, then `<F(T2)x,x> <= <G(T2)x,x>`; nonnegative
symbols give nonnegative forms. For a represented square `H=F*F`,
`<H(T2)x,x> = ||F(T2)x||²`, with a fully supplied cusp-squared instance.
The proofs use the original positive moment functional and explicit
pairing-limit moduli, not a supplied spectral decomposition.
Three modules passed 21 focused axiom checks within `{propext, Quot.sound}`;
no full-tree run. General product data and symbol algebra are now constructed
above; full-carrier and continuum/Clay bridges remain open.
SU(2) nome and spacing remain fixed. Nonnegative forms are not
a strictly positive physical gap or beta/spacing-uniform gap estimate.

**Established limit bound:** [relative operator bounds hold on constructed original cyclic limits](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCyclicLimitBound.lean).
For `|p| <= M` on `[0,1]`,
`||p(T2)F(T2)v||² <= M² ||F(T2)v||²` for every constructed Bernstein
symbol vector. The image limit is proved equal to the existing original
polynomial operator value; its Cauchy representative and convergence rate
are returned. A coefficient estimate supplies continuity but does not
appear in the final relative bound. Three modules passed 30 focused axiom
checks within `{propext, Quot.sound}` (one axiom-free); no full-tree run.
Continuous-symbol action is now constructed above. Full continuous
operator algebra, physical-scale control and continuum/Clay remain open;
SU(2) nome and spacing remain fixed.

**Established polynomial bound:** [relative polynomial operator bounds on the original cyclic sector](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCyclicOperatorBound.lean).
For `|p| <= M` on `[0,1]`, the original operator satisfies
`||p(T2)q(T2)v||² <= M² ||q(T2)v||²` for every polynomial `q`,
without a coefficient-size factor or supplied spectral decomposition.
[Polynomial products compose as the actual operators](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialOperator.lean),
and the coordinate polynomial recovers the original `T2`.
[Equivalent symbols on the spectral interval give identical constructed vectors](lean/YMGap/Continuum/BF4ExactSlabThermodynamicSymbolCompatibility.lean),
even with different bounds, moduli or outside values. Three modules passed
28 focused axiom checks within `{propext, Quot.sound}`; no full-tree run.
The extension to represented cyclic limits is now proved above.
Full continuous operator calculus, physical-scale control and
continuum/Clay remain open; SU(2) nome and spacing remain fixed.

**Established limit laws:** [norm bounds and pairing limits for the original Bernstein symbol vectors](lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinLimitPairing.lean).
The constructed vector for a symbol `F` satisfies `||F(T2)v||² <= F.bound²`.
Pairings of two such vectors are limits of the same original polynomial
moment functional, with computed convergence rates and retained real
Cauchy data. No new Yang--Mills assumption or diagonal model is supplied.
Three modules passed 31 focused axiom checks within `{propext, Quot.sound}`;
no full-tree build or audit ran. Full continuous operator calculus,
physical-scale control and continuum/Clay remain open.
These results use fixed SU(2) nome and lattice spacing.

**Established carrier milestone:** [Bernstein symbol vectors have constructed limits in the original OS completion](lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinCarrier.lean).
For bounded rational-valued symbols with explicit continuity data, the
construction returns original Cauchy representatives and convergence rates;
the limit is unique and independent of the chosen continuity modulus.
A [concrete bounded cusp symbol](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCuspProbe.lean),
`min(|t - 1/2|, 1)`, supplies a proved nonconstant instance with all its
continuity data constructed. Its symbol vector is not claimed nonzero.
Four modules passed 54 focused axiom checks within `{propext, Quot.sound}`
(six axiom-free). Their limit pairing/norm laws are now proved by the
limit-laws milestone above; full continuous operator calculus and continuum
remain open.

**Established polynomial milestone:** the original transfer has a
[constructed positive, normalized, bounded polynomial moment functional](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialFunctional.lean).
Signed-polynomial row averages converge with computed error
`Σ |c_r| C(r) / N` and explicit moduli. The
[same-operator norm identity](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialProbeNorm.lean)
proves `<p(T2)v,q(T2)v> = F(pq)` and `||p(T2)v||² <= M²` whenever
`|p(t)| <= M` on `[0,1]`. These are actual original cyclic probe vectors,
not a supplied diagonal model. Four modules passed 57 focused axiom
checks within `{propext, Quot.sound}` (three axiom-free).
Continuous functional calculus, full spectral realization, continuum
scaling and the Clay target remain open; nome and spacing are fixed.

**Established moment convergence:** [all moments of the finite Bernstein rows converge to the original transfer moments](lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinMomentConvergence.lean).
At degree `N`, the two-sided error for the `r`th moment is at most
`C(r)/N`, where `C(0)=0` and `C(r+1)=C(r)+r`. The certificate returns
the original limiting moment `<v,T2^r v>`, its Cauchy data, the operator
identity and a computed tolerance threshold. Three modules passed 61
focused axiom checks within `{propext, Quot.sound}` (five axiom-free).
This is an all-order moment result at fixed nome and lattice spacing.

**Established finite rows:** [positive mixed time/defect moments](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeDefectMoments.lean)
now produce [finite Bernstein probability rows for the original normalized probe](lean/YMGap/Continuum/BF4ExactSlabThermodynamicBernsteinProbeRows.lean).
Their rational grid nodes lie in `[0,1]`; their nonnegative real weights
have explicit Cauchy moduli, sum to one, and have first moment exactly
`<v,T2 v>`. Positivity is derived from the original operator's symmetry
and contraction, without a supplied spectral decomposition. The binary-word
representation retains repeated grid nodes, not alleged eigenvalues.
Three modules passed 55 focused axiom checks within `{propext, Quot.sound}`
(four axiom-free). These are finite probability rows, not assumed
eigenvalues or a supplied spectral decomposition.

**Established normalized excitation:** a [norm-one excitation with a certified strict transfer-response interval](lean/YMGap/Continuum/BF4ExactSlabThermodynamicNormalizedProbe.lean)
is now constructed in the original thermodynamic OS completion:
`||v||^2 = 1` and `0 < responseFloor/P <= <v,T2 v> <= 1/2`.
The normalization uses the same original squared norm and a
[constructed reciprocal square root with explicit moduli](lean/YMGap/Continuum/PositiveCRealNormalizationScalar.lean).
Its certificate returns the actual state, both rational interval endpoints,
the response real and its Cauchy data. Positive orbit floors survive the
normalization. Three modules passed 60 focused axiom checks within
`{propext, Quot.sound}` (five axiom-free); no full-tree build or audit ran.
This remains fixed-nome, fixed-spacing SU(2), not continuum Yang--Mills.

**Established discrete-time survival:** the [original excitation survives every discrete time](lean/YMGap/Continuum/BF4ExactSlabThermodynamicProbeOrbit.lean),
with a [computed positive squared-norm floor at each positive time](lean/YMGap/Continuum/BF4ExactSlabThermodynamicProbeOrbitFloor.lean).
The same symmetric time semigroup has [equal kernels at all positive integer times](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeKernel.lean).
For the existing probe, `r_0=w^36/16`, `r_(k+1)=r_k^2/P` gives
`0 < r_k <= ||T_(k+1)x||^2`, with the existing explicit observable bound `P`.
Each certificate retains the same moment and its Cauchy modulus. These
time-dependent floors do not assert a nondecaying response or injectivity
on the entire completion. Three modules passed 28 focused axiom checks
within `{propext, Quot.sound}`; no full-tree build or audit ran.
The [source-level reconstruction audit](audits/AUDIT-ORIGINAL-OS-RECONSTRUCTION.md)
records the closed normalization and the remaining full-observable,
scalar-codomain, completion, spectral and continuum-limit boundaries.

**Established fixed-spacing dynamics:** the original thermodynamic geometric OS time
evolution [converges quantitatively to its unit projection](lean/YMGap/Continuum/BF4ExactSlabThermodynamicRelaxation.lean),
and [its positive-time fixed space is exactly that unit line](lean/YMGap/Continuum/BF4ExactSlabThermodynamicFixedUnit.lean).
These follow from the proved completed unit-complement form gap, at SU(2)
nome `1/1024` and fixed spacing. A [nonzero thermodynamic excitation](lean/YMGap/Continuum/BF4ExactSlabThermodynamicProbeExcitation.lean)
is now constructed in that same completion: the centered plaquette probe
has an explicit positive squared-norm floor and is not fixed by any positive
integer time. The [two-step defect now has a constructive bounded inverse](lean/YMGap/Continuum/BF4ExactSlabThermodynamicResolventBound.lean)
on that completion's unit complement: `(I-T2) R x = center x`,
`R (I-T2) x = center x`, and `||R x||^2 <= 4||center x||^2`.
The geometric-series solver retains its explicit approximation modulus.
The [original excited response is now proved strictly positive](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveResponse.lean):
`<x,T2 x> = ||T1 x||^2 >= w^36/16 > 0`, with `w=1/1024`.
The existing response-certificate format now has a concrete accepted witness,
with computed tolerance, volume margin and representative index. Thus neither
`T1 x` nor `T2 x` vanishes. Acceptance follows from the original analytic
bound, not an asserted numerical sample. Full observable realization/
completeness, continuous-time generator and physical spectral identification,
continuum scaling and the Clay target remain open.

**Latest mathematical step:** the [entire remaining original signed spatial remainder is bounded](lean/YMGap/Continuum/BF4ExactSlabSpatialForestRemainderBound.lean),
including every higher-spin label and every core's own detached partition
square. Summing the actual two-mass count gives a pair-weight budget of
`w^36/16`; restoring the partitions gives `w^36 * Z_full^2 / 8`.
Absorbing that remainder proves the [complete original numerator floor](lean/YMGap/Continuum/BF4ExactSlabOriginalResponseNumeratorFloor.lean)
`N_full >= w^36 * Z_full^2 / 16`, for every `K>=1` and margin.

The [same-partition lower-bound transport](lean/YMGap/Continuum/BF4ExactSlabCovarianceLowerTransport.lean)
removes the representation cutoff and cancels `Z_full^2` using the original
reciprocal. The already constructed thermodynamic limit preserves the floor
and yields the original operator response above. This is fixed SU(2) nome
and spacing, **not a beta-uniform or continuum mass-gap theorem**.
Six modules passed 43 focused axiom checks within `{propext, Quot.sound}`
(seven axiom-free); no full-tree build or audit ran.

**Previous local mathematical step:** [the entire remaining spatial family is counted](lean/YMGap/Continuum/BF4ExactSlabSpatialForestPairCount.lean),
including all higher-spin labels. For every cutoff, margin and cut-filter
time, the actual stratum with `S` spatial odd occurrences and higher-label
mass `H` has at most `7,200,000^S * 241,813,452^H` configurations.
The [reversible whole-forest code](lean/YMGap/Continuum/FiniteRootedForestCode.lean)
retains replica tags and full original plaquettes. Together with the
higher-label word it recovers both complete original labellings; no source
is deduplicated. Every nonzero remaining pair has `S>=6`.

The counting gain comes from pairing each component's root cost with one
descent: there are no isolated vertices. The forest construction and its
finite carrier bound are proved, not assumed. The subsequent increment
above now sums the unchanged weights, restores the original partitions and
proves the positive thermodynamic response. Nine modules in this preceding
increment passed 109 focused axiom checks within
`{propext, Quot.sound}` (18 axiom-free); no full-tree build or audit ran.

**Previous local mathematical step:** the remaining spatial occurrences have
[actual connected components with at most half as many components as occurrences](lean/YMGap/Continuum/BF4ExactSlabSpatialOccurrenceComponents.lean).
Replica tags and original times are retained. Even projected incidence gives
each occurrence a distinct neighbor; the components have total size exactly
`S`, and each has at least two members. For short pairs, every graph neighbor
lies in an explicit list of 3,216 candidates, independent of cutoff and margin.

A [reversible descent-only tree code](lean/YMGap/Continuum/FiniteRootedAnimalDescentCode.lean)
also improves the rooted size-`k` code-space bound from
`(D+1)^(2*(k-1))` to `(4*D)^(k-1)`. Returns need no new neighbor choice.
The forest assembly and original configuration count are now closed by the
latest increment above; the weighted aggregate estimate remains open.
Five modules in this preceding increment passed 52 focused axiom checks within
`{propext, Quot.sound}` (seven axiom-free); no full-tree build or audit ran.

**Previous local mathematical step:** [the whole remaining four-spatial-face family is bounded](lean/YMGap/Continuum/BF4ExactSlabFourCapRemainderBound.lean),
including all higher spins and each core's own detached partition square.
The original pair's [projected spatial boundary is even](lean/YMGap/Continuum/BF4ExactSlabProjectedSpatialCycle.lean).
Four such faces must pair in projection: distinct plaquettes share at most
one edge, so three distinct faces cannot cancel a fourth face's four edges.
This gives a reversible two-anchor code and an actual configuration count.

At fixed SU(2) nome `w=1/1024`, for every cutoff, margin and cut-filter time,
`|fourCapRemainder| <= 2^-14 * w^36 * Z_full^2`.
The [exact original absorption theorem](lean/YMGap/Continuum/BF4ExactSlabAfterFourCapRemainder.lean)
gives, for every `K>=1`:

`N_full >= (1/4 - 2^-19 - 2^-26 - 2^-14 - 2^-14) * w^36 * Z_full^2 + w^54 * afterFourCapHeatResidual54`.

Every nonzero remaining term has **at least six spatial odd faces**.
**Next:** count and bound that actual family. Positive full response,
coupling-uniform physical mass gap and continuum/Clay remain open.
Nine new modules passed 72 focused axiom checks within `{propext, Quot.sound}`
(eleven axiom-free); no full-tree build or audit ran.

**Previous local mathematical step:** [the whole remaining two-spatial-cap family is bounded](lean/YMGap/Continuum/BF4ExactSlabTwoCapRemainderBound.lean),
at every cutoff and volume margin, including each core's own detached
partition square. This covers all higher-spin labels in that family,
not just the previously classified power-42 sector.

The two caps [share one spatial projection](lean/YMGap/Continuum/BF4ExactSlabTwoCapSpatialCode.lean).
A bounded spatial code plus a higher-label unit word
[recovers the complete original pair](lean/YMGap/Continuum/BF4ExactSlabTwoCapPairCount.lean),
preserving its multiplicity. Summing the SU(2) heat costs gives, at fixed
nome `w=1/1024`, for all cutoffs, margins and cut-filter times:

`|twoCapRemainder| <= 2^-14 * w^36 * Z_full^2`.

The [exact split and absorption](lean/YMGap/Continuum/BF4ExactSlabAfterTwoCapRemainder.lean)
give, for every `K>=1`:

`N_full >= (1/4 - 2^-19 - 2^-26 - 2^-14) * w^36 * Z_full^2 + w^48 * afterTwoCapHeatResidual48`.

Every nonzero term in that literal remaining sum has **at least four
spatial odd faces**. The four-face part is now bounded above; six-or-more
spatial faces still need an aggregate estimate. Positive full
response, coupling-uniform physical mass gap and continuum/Clay remain open.
Seven new modules passed 68 focused axiom checks within `{propext, Quot.sound}`
(fifteen axiom-free); no full-tree build or audit ran.

**Previous local mathematical step:** [the original joint power-42 spatial sector is excluded](lean/YMGap/Continuum/BF4ExactSlabPower42JointExclusion.lean).
The two caps have the same spatial projection and distinct times. A cut
between them either has an impossible four-link symmetric difference of
plaquette boundaries, or is occupied by both replicas; both contradict
the already proved saturated cut budget. This uses the original moment
checker, not an assumed cap geometry or Haar sign.

Every nonzero spatial pair also needs at least fourteen occupied faces.
SU(2) Casimir excess and even-power arithmetic then exclude all powers
between 42 and 48. After the previously bounded means sector is removed,
[the actual remaining sum factors exactly](lean/YMGap/Continuum/BF4ExactSlabAfterMeansHeatPower48.lean),
at every rational nome and cutoff:

`afterMeans42Remainder = w^48 * afterMeansHeatResidual48`.

At fixed nome `w=1/1024`, for every `K>=1`, margin and cut-filter time:

`N_full >= (1/4 - 2^-19 - 2^-26) * w^36 * Z_full^2 + w^48 * afterMeansHeatResidual48`.

The cofactor retains the original signed amplitudes, multiplicities and
each core's own detached partition. The two-cap part is now bounded above;
the four-or-more-spatial-face part still needs an aggregate estimate.
The factorization alone does not establish a positive full response,
coupling-uniform mass gap, or continuum/Clay closure. Eight new modules
passed 55 focused axiom checks within `{propext, Quot.sound}` (four
axiom-free); no full-tree build or audit ran.

**Previous local mathematical step:** [the entire original power-42 means sector is bounded](lean/YMGap/Continuum/BF4ExactSlabPower42MeansBound.lean),
including each core's own detached partition square. Finite temporal
conservation [aligns each lone spatial cap with the original probe](lean/YMGap/Continuum/BF4ExactSlabSingleSpatialCap.lean).
The exact temporal decoder and saturated area budget then force the two
replicas to [share one cap at slice 0, 1, 2, or 3](lean/YMGap/Continuum/BF4ExactSlabPower42MeansCaps.lean).
That slice is an [injective code for the original label pair](lean/YMGap/Continuum/BF4ExactSlabPower42MeansCount.lean),
so there are **at most four original terms**, with no deduplication or
assumed Haar sign. At fixed nome `w=1/1024`, for every cutoff, margin and
cut-filter time:

`|means42Remainder| <= 2^-26 * w^36 * Z_full^2`.

The [exact split and absorption](lean/YMGap/Continuum/BF4ExactSlabAfterMeans42Remainder.lean)
give, for every `K>=1`,

`N_full >= (1/4 - 2^-19 - 2^-26) * w^36 * Z_full^2 + afterMeans42Remainder`.

The joint power-42 sector is now excluded above; higher-power spatial terms
in that literal remaining sum still require a bound. This is not yet a positive full-response
theorem, a coupling-uniform mass gap, or continuum/Clay closure.
Eight new modules passed 54 focused axiom checks within `{propext, Quot.sound}`
(ten axiom-free); no full-tree audit ran.

The preceding [original spatial-defect remainder starts at heat power 42](lean/YMGap/Continuum/BF4ExactSlabSpatialHeatPower42.lean),
strengthening the previous power-39 factor. An [explicit finite incidence argument](lean/YMGap/Continuum/Z4WeightedIncidenceParity.lean)
proves even face-count constraints. Applied to the original Haar moments,
it [separates the joint and product-of-means channels](lean/YMGap/Continuum/BF4ExactSlabPairChannelParity.lean)
and makes every nonzero original pair's total heat power even.
At power 42, all fourteen replica occupations are fundamental, and a
[nonzero spatial defect has exactly two spatial odd-face occupations](lean/YMGap/Continuum/BF4ExactSlabPower42SpatialBudget.lean).
They split as `(2,0)` or `(0,2)` in the joint channel and `(1,1)` in the
means channel. Those theorems count occupations; the new result above
counts the means-channel configurations.
The exact `w^42` cofactor retains all original signed amplitudes, dimensions
and detached partitions. Its aggregate magnitude is still open.
Six new modules passed 46 focused axiom checks within `{propext, Quot.sound}`
(eight axiom-free); no full-tree audit ran. The new results above settle
the power-42 configurations; the higher-power tail still needs control.
Positive full response and continuum/Clay remain open.

The preceding [whole original zero-spatial short-core remainder is bounded](lean/YMGap/Continuum/BF4ExactSlabZeroSpatialRemainderBound.lean),
including every core's own detached partition square. The [exact split](lean/YMGap/Continuum/BF4ExactSlabShortSpatialRemainderSplit.lean)
preserves the original signed weights and removes only zero terms.
The [short-collar comparison](lean/YMGap/Continuum/BF4ExactSlabShortDetachedPartition.lean)
costs at most a factor of 2, independently of cutoff and volume.
At the unchanged nome `w=1/1024`, for every `K>=1`, margin and cut time:

`|zeroSpatialRemainder| <= 2^-19 * w^36 * Z_full^2`

Combining this with the tube reference and large-core tail gives
`N_full >= (1/4 - 2^-19) * w^36 * Z_full^2 + spatialDefectRemainder`.
**Next:** bound that actual spatial-defect remainder. Its sign and size are
still open; the inequality is not yet a positive full-response theorem.
Three new modules passed 26 focused axiom checks within `{propext, Quot.sound}`
(six axiom-free); no full-tree audit ran. Positive response, full observable
realization and continuum/Clay remain open.

The preceding [original zero-spatial short-pair weights have a uniform sum bound](lean/YMGap/Continuum/BF4ExactSlabZeroSpatialPairSum.lean).
Every original short core is [localized within radius 33 of the lower probe](lean/YMGap/Continuum/BF4ExactSlabShortCoreLocalization.lean),
independently of volume. An injective local code preserves its higher-label
cost `H`; [counting by that cost](lean/YMGap/Continuum/BF4ExactSlabZeroSpatialPairCount.lean)
turns the whole zero-spatial pair family into a convergent geometric bound.
At the unchanged nome `w=1/1024`, the **sum of absolute original pair weights**
is at most `2^-20 * w^36`, uniformly in cutoff, margin and cut-filter time.
This advances the previous per-pair estimate to a sum estimate.
That pair-weight theorem alone does not include detached partition squares;
the new result above restores them.
Six new modules passed 66 focused axiom checks within `{propext, Quot.sound}`
(13 axiom-free); no full-tree audit ran. The separate spatial-defect family,
the complete short-remainder bound, positive full response and continuum/Clay
remain open.

The preceding [exact defect filter shows every surviving original non-tube term must pay a defect cost](lean/YMGap/Continuum/BF4ExactSlabZeroSpatialHigherCost.lean).
Finite temporal charge conservation [rejects the one-endpoint channels exactly](lean/YMGap/Continuum/BF4ExactSlabZeroSpatialChannels.lean)
when there are no spatial odd faces, at all spins and without an assumed
three-layer window. The mixed channel then has the tube's parity pattern;
the partition channel is even. Each original non-tube coefficient is
exactly filtered to spatial defects or positive higher-label count.
In the zero-spatial sector, [each original non-tube pair has magnitude at most
`(9/2^53)*w^36`](lean/YMGap/Continuum/BF4ExactSlabZeroSpatialHeatBound.lean)
at the unchanged nome `1/1024`. **This is per pair, not a bound on their sum.**
That checkpoint passed 34 focused axiom checks within `{propext, Quot.sound}`
(7 axiom-free), not a full-tree audit.

The preceding [original pair weights separate into parity and higher-label costs](lean/YMGap/Continuum/BF4ExactSlabParityHigherPairBound.lean).
Writing each label as `j=2h+b`, the [all-spin heat envelope](lean/YMGap/Continuum/SU2ParityHigherHeatEnvelope.lean)
gives `|weightedPairTerm| <= 8*(4w^3)^B*(9w^8)^H`, with both counts
computed from the original physical labels. At the unchanged nome `1/1024`,
the rates are exactly `2^-28` and `9*2^-80`. Fixed-parity higher-label
tails have an explicit geometric bound; the even-sector total cap is
at most `1+2*(9*2^-80)`, independent of cutoff.
That checkpoint passed 33 focused axiom checks within `{propext, Quot.sound}`
(12 axiom-free), not a full-tree audit.

The preceding [sharp SU(2) character bounds control the original signed pair weights](lean/YMGap/Continuum/BF4ExactSlabSharpCharacterWeights.lean).
An [exact Chebyshev energy identity](lean/YMGap/Continuum/QuaternionHaarChebyshevEnergy.lean)
constructs sum-of-squares certificates for [both bounds `|chi_n| <= n+1`](lean/YMGap/Continuum/QuaternionHaarSharpCharacterInterval.lean),
replacing the exponential character envelope in these new estimates.
The original heat-weighted pair is bounded by `8 * D^2 * w^P`, where
`D` is its original two-replica dimension product and `P` its exact Casimir
power. Every original moment and shared link remains present. Three
focused modules passed 27 axiom checks within `{propext, Quot.sound}`
(three axiom-free); no full-tree audit ran. **Next:** sum these sharper
weights over admissible spatial defects and higher labels. The short
signed-remainder bound, positive full response and continuum/Clay remain open.

The preceding [spatial defects reconstruct the original temporal label parities](lean/YMGap/Continuum/BF4ExactSlabSpatialDefectReconstruction.lean).
For every accepted original moment, spatial odd-face incidence and the
endpoint charges determine all temporal cut bits through an [explicit binary
recurrence](lean/YMGap/Continuum/Z4SpatialDefectTemporalDecoder.lean).
This holds at every spin and volume margin, without a three-layer window
restriction. Equal spatial odd-face data fix all physical label parities;
adding each label's quotient by two fixes the original physical labels.
Two focused modules passed 20 axiom checks within `{propext, Quot.sound}`
(five axiom-free); no full-tree audit ran. **Next:** turn this injective
encoding into a useful weighted defect count for the signed short-core
remainder. The encoding alone is not that estimate. Positive full response
and continuum/Clay remain open.

The preceding [remaining short-core sum has an exact `w^39` factor](lean/YMGap/Continuum/BF4ExactSlabShortCoreHeatFactor.lean).
The [leading-pair support is pinned to the literal tube](lean/YMGap/Continuum/BF4ExactSlabNonTubeHeatPower.lean),
so every non-tube core has zero original amplitude at power 36. The
[all-spin SU(2) Casimir gap](lean/YMGap/Continuum/SU2FiniteCasimirFirstExcess.lean)
excludes retained powers 37 and 38. The factorization preserves every
signed Haar amplitude, representation dimension and detached partition,
and holds even at zero or negative rational nome, for every `K >= 1`.
At nome `1/1024`, the original bound is now
`N_full >= (w^36/4) * Z_full^2 + w^39 * shortHeatResidual`.
Three focused modules passed 17 axiom checks within `{propext, Quot.sound}`;
no full-tree audit ran. **Next:** prove a useful cutoff- and volume-uniform
bound on that explicit signed cofactor. The extra power alone does not
make it small. Positive full response and continuum/Clay remain open.

The preceding [large signed core remainder is controlled](lean/YMGap/Continuum/BF4ExactSlabOriginalCoreTailCertificate.lean)
at nome `1/1024`, uniformly in cutoff and volume margin. The [exact split](lean/YMGap/Continuum/BF4ExactSlabOriginalCoreTailWindow.lean)
retains the original coefficients, multiplicities and detached partitions.
All other cores with at least 33 faces cost at most `(w^36/4) * Z_full^2`
in absolute value. Absorbing this into the tube reference gives
`N_full >= (w^36/4) * Z_full^2 + shortOtherRemainder`.
Three focused modules passed 27 axiom checks within `{propext, Quot.sound}`
(three axiom-free); no full-tree audit ran.
**Next:** control the exact signed non-tube remainder with 12–32 faces.
The bounded-size window still retains every cutoff spin and original
partition factor; its sign is not assumed. Positive full response, limit
persistence and continuum/Clay closure remain open.

The preceding [actual dressed tube term has a positive reference floor](lean/YMGap/Continuum/BF4ExactSlabOriginalTubeReferenceFloor.lean)
relative to the original full partition, at every cutoff and volume margin
at nome `1/1024`. Its collar has at most 336 faces. Iterating the [original
one-face partition comparison](lean/YMGap/Continuum/BF4ExactSlabRelativePartitionCeiling.lean)
charges only for that collar; a [short inductive power bound](lean/YMGap/Continuum/RationalLinearPowerCeiling.lean)
gives `Z_detached^2 >= Z_full^2/2`. The dressed tube contribution is therefore
at least `(w^36/2) * Z_full^2`. Three focused modules passed 17 axiom checks
within `{propext, Quot.sound}` (three axiom-free); no full-tree audit ran.
**Next:** bound the signed `otherCoreRemainder` at this reference scale.
It is retained in the full numerator's lower bound, not discarded.
Positive full response, limit persistence and continuum/Clay closure remain open.

The preceding [full original tube core is evaluated exactly](lean/YMGap/Continuum/BF4ExactSlabOriginalTubeCoreSplit.lean),
including every cutoff spin, not only its leading term. A [common sweep](lean/YMGap/Continuum/BF4ExactSlabConnectedTemporalSweep.lean)
preserves the partition, both means and mixed moment. The [original ordered
tube heat sub-action](lean/YMGap/Continuum/BF4ExactSlabOriginalTubeActionSweep.lean)
then contracts to [exactly `w^36`](lean/YMGap/Continuum/BF4ExactSlabOriginalTubeHeatValue.lean)
for every rational nome, cutoff `K >= 1` and margin. Its proper selections
vanish, so its complete connected coefficient is also exactly `w^36`.
The full original resummed numerator is now
`w^36 * Z_detached^2 + otherCoreRemainder`, with the tube proved to belong
to the actual computed core list. Four focused modules passed 30 axiom
checks within `{propext, Quot.sound}` (two axiom-free); no full-tree audit ran.
**Next:** control the signed other-core sum relative to this dressed tube
term. The detached partition is not silently replaced by the full partition.
Positive full response, limit persistence and continuum/Clay closure remain open.

The preceding [exact cancellation on fewer than twelve selected faces](lean/YMGap/Continuum/BF4ExactSlabShortSupportCancellation.lean)
now feeds the [original partition-relative resummation](lean/YMGap/Continuum/BF4ExactSlabOriginalTwelveFaceBudget.lean).
Each occupied replica cut embeds in the [selected support's cut](lean/YMGap/Continuum/BF4ExactSlabRetainedSelectedArea.lean),
so overlaps are counted once. Three four-face cuts force twelve selected
faces. Smaller original coefficients vanish exactly; their detached partition
factors are retained until cancellation, before absolute values are taken.
The resulting bound `|N| <= responseBudget(w) * Z^2` names the coupling and
smallness guards, and holds at every cutoff and margin. Four focused modules
passed 21 axiom checks within `{propext, Quot.sound}`; no full-tree audit ran.
**Boundary:** this bounds the full numerator, not the signed higher remainder.
At nome `1/1024`, the exact-rational scalar pilot finds the budget about
`3.52e69` times `w^36`, so it does not certify positivity. The next frontier
was to isolate and control the dressed tube corrections within this same
resummed sum. The tube core is now evaluated above; the other-core sum,
positive response and continuum/Clay closure remain open.

The preceding [complete original leading coefficient is exactly one](lean/YMGap/Continuum/BF4ExactSlabLeadingCoefficientOne.lean)
for every cutoff `K >= 1`, margin and filter time. The [explicit tube pair](lean/YMGap/Continuum/BF4ExactSlabCanonicalTubeSupport.lean)
belongs to the unchanged representation enumeration. Its [nonzero original
Haar moment](lean/YMGap/Continuum/BF4ExactSlabCanonicalTubeMoments.lean)
forces the charge, odd-cut and leaf filters to accept it. A [three-face
strip](lean/YMGap/Continuum/BF4ExactSlabCanonicalTubeConnected.lean)
rules out every actual separating cut: shared edges force all three faces
onto the lower-probe side until the last meets the upper probe.
Together with [proved uniqueness](lean/YMGap/Continuum/BF4ExactSlabLeadingCountUniqueness.lean),
this gives `leadingCount = 1` and the exact full original numerator
`w^36 * (1 + w*B(w))`. Five focused modules passed 49 axiom checks within
`{propext, Quot.sound}` (four axiom-free); no full-tree audit was run.
**Next:** control the signed higher remainder relative to the original
partition. Positive full response, normalization/limit persistence and
continuum/Clay closure remain open. A positive leading coefficient alone
does not bound the full response or prove a coupling-uniform mass gap.

The preceding [finite-count identity](lean/YMGap/Continuum/BF4ExactSlabLeadingCoefficientCount.lean)
retains the complete original coefficient. The [accepted mixed-moment support](lean/YMGap/Continuum/BF4ExactSlabMinimalMixedTube.lean)
is proved to be exactly the literal twelve-face tube, including its physical
labels. A common gauge sweep and the existing full-carrier contraction prove
`4096 * bareTubeMoment = 1`. The [actual original dimension products](lean/YMGap/Continuum/BF4ExactSlabMinimalPairAmplitude.lean)
give that same 4096, so every retained leading amplitude is exactly zero or
one. Summation preserves the original connected selections, label filters
and multiplicities: `A = ofNat (leadingCount K margin time)`.
Seven focused modules passed 38 axiom checks within `{propext, Quot.sound}`
(four axiom-free). Existence and uniqueness are now proved above.
**Still open:** bound the signed higher
remainder, establish original positive response and limit persistence,
and close the continuum/Clay obligations. Nonnegative leading terms alone
do not bound the complete response or give a coupling-uniform gap.

The preceding [minimal-power spatial continuation](lean/YMGap/Continuum/BF4ExactSlabMinimalMomentContinuation.lean)
now eliminates both one-endpoint moments from the leading connected term.
[Saturation of the original twelve-face bound](lean/YMGap/Continuum/BF4ExactSlabMinimalPowerWindow.lean)
confines every occupied face to the three intervening temporal layers.
Exact spatial-link incidence and the original SU(2) center-charge checker
then force the same boundary bit through all three cuts. A passing
partition moment has empty occupied support; any leading pair with an
occupied partition-replica face contributes zero. This uses the original
signed Haar moments, not a replacement measure or an assumed tube path.
Six focused modules passed 40 axiom checks within `{propext, Quot.sound}`
(seven axiom-free). The mixed-moment carrier and complete leading coefficient
are now evaluated above. The signed remainder, original positive response
and continuum/Clay closure remain open.
These are exact support/cancellation statements, not a uniform gap estimate.

The preceding [complete original connected numerator](lean/YMGap/Continuum/BF4ExactSlabOriginalLeadingRemainder.lean)
is now proved to equal `w^36 * (A + w*B(w))`, with explicit signed finite
sums for `A` and `B`. This is a division-free identity, including at `w = 0`,
for every cutoff and volume margin. The [original two-replica heat weights](lean/YMGap/Continuum/BF4ExactSlabOriginalPairHeatPower.lean)
retain every representation dimension and the original signed Haar term.
The twelve-face bound forces combined Casimir power at least 36; attaining
36 forces exactly twelve occupied faces, all with label one (the fundamental
representation). Four focused modules passed 30 axiom checks within
`{propext, Quot.sound}` (five axiom-free).
The value of `A` is now proved above. **Still open:** a useful relative bound
on `B`, positive original response, normalization and cutoff/volume persistence, and the
continuum/Clay obligations. The identity does not assert a coupling-uniform gap.

The preceding geometric step proves that every pair retained by the complete original
connected-numerator expansion has [at least twelve positive-spin faces in total](lean/YMGap/Continuum/BF4ExactSlabConnectedReplicaArea.lean).
An [explicit temporal separator](lean/YMGap/Continuum/BF4ExactSlabConnectedTemporalCrossing.lean)
proves that connected selected support crosses each of the three intervening
cuts. The existing replica labels cover each selected face, so some replica
occupies each cut; it need not be the same replica on all three cuts.
[No temporal leaves](lean/YMGap/Continuum/BF4ExactSlabPositiveFaceCutMinimum.lean)
forces at least four faces per occupied cut, including even-spin faces.
The proof uses a [simple bipartite obstruction](lean/YMGap/Continuum/LeaflessBipartiteEdgeMinimum.lean),
not cycle extraction or an assumed path. Five focused modules passed 25 axiom
checks within `{propext, Quot.sound}` (one axiom-free). The exact heat-power
factorization is now proved above. Surviving signs, relative signed remainder
bounds, positive response and continuum/Clay closure remain open.
This support theorem is not a coupling-uniform gap estimate.

The preceding [all-spin leaf filter](lean/YMGap/Continuum/BF4ExactSlabShiftedProbeLeafFilter.lean)
now removes singly occupied temporal links from the **same complete original
connected numerator**, including even-spin cases missed by parity.
[Cyclic word exposure](lean/YMGap/Continuum/SU2QuaternionOrientedWordSelection.lean)
works at any of the four literal plaquette links, preserving quaternion order.
The [full-action cancellation](lean/YMGap/Continuum/BF4ExactSlabSingletonOccupiedLink.lean)
derives independence from the other incident faces' zero labels; it does not
assume that the full interacting action splits. All four original moments,
both replica weights and the connected-support filter remain in the identity.
Four focused modules passed 31 axiom checks within `{propext, Quot.sound}`
(one axiom-free). The finite pilot rejects 64 additional parity-surviving
assignments on a four-face cut. **No positive response bound is claimed:**
the global positive-support area argument is now proved above, but the signed
relative remainder and continuum/Clay obligations remain open. This all-nome
cancellation is not a uniform gap bound.

The preceding common expansion puts both cancellations on the
[same complete original connected numerator](lean/YMGap/Continuum/BF4ExactSlabShiftedProbeCoveredExpansion.lean).
The outer sum removes separating selected supports; the inner sum removes
thin odd cuts in either replica. An [exact covering-pair expansion](lean/YMGap/Continuum/PairedPositiveFacePolynomialExpansion.lean)
and [full-slab integrand pin](lean/YMGap/Continuum/BF4ExactSlabCoveredPairExpansion.lean)
preserve the original heat weights, signed Haar terms, partition and both
endpoint means. Each selected face has positive spin in at least one replica;
both replicas are spin zero outside the selection. This holds for every
cutoff, volume margin and rational nome, without an independence premise.
Five focused modules passed 32 axiom checks within `{propext, Quot.sound}`
(two axiom-free). **This is an exact identity, not a coupling-uniform bound.**
Empty odd cuts and even-spin interactions remain. Surviving-pair classification,
signed relative remainder control and a positive response certificate are open,
as are the continuum/Clay obligations.

The preceding geometric obstruction rejects
terms of the [original shifted-probe moments](lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTemporalCut.lean).
The [exact incidence bridge](lean/YMGap/Continuum/BF4ExactSlabOddFaceIncidence.lean)
identifies all-spin charge modulo two with odd-labelled physical faces.
A temporal cut containing one, two or three such faces forces the moment
to vanish, at every volume margin. The [two-replica filter](lean/YMGap/Continuum/BF4ExactSlabShiftedProbeConnectedCut.lean)
then preserves finite signed connected sums with the original heat weights,
keeping the partition and both endpoint means together. Three focused
modules passed 27 axiom checks within `{propext, Quot.sound}` (three axiom-free).
Empty odd cuts and even-spin contributions remain allowed. The common
connected-selection expansion is now proved above; bounding surviving pairs
remains open. No positive-response or continuum theorem is claimed.

The preceding [temporal-cut area bound](lean/YMGap/Continuum/Z4TemporalCutParityMinimum.lean)
now proves that a nonempty cut of distinct plaquettes, with even incidence at
every vertical link, contains at least four faces. Three nonempty consecutive
cuts therefore require at least twelve faces. The proof identifies cut-graph
degree with the original vertical-link incidence and uses a
[simple bipartite-graph obstruction](lean/YMGap/Continuum/EvenBipartiteEdgeMinimum.lean),
without extracting a cycle. Three focused modules passed 15 axiom checks
within `{propext, Quot.sound}` (two axiom-free).
**The odd-cut nonemptiness hypotheses remain explicit.** The newer no-leaf
argument above instead uses FULL positive-spin support and replica coverage
to prove the original retained-pair area bound. Neither area result proves
`w^36` divisibility, positivity or a continuum theorem.

The preceding [all-spin center-charge filter](lean/YMGap/Continuum/BF4ExactSlabCenterCharge.lean)
now removes exactly zero terms from the **original shared-link heat sum**.
An odd total label at an integrated link forces its signed Haar coefficient
to vanish. The proof uses actual face incidences, all spins and every slab
extent; it does not assume the other plaquettes are independent.
The [four shifted-probe moment filters](lean/YMGap/Continuum/BF4ExactSlabShiftedProbeCenterCharge.lean)
include each observable's charge in the same test. Partition, endpoint means
and mixed moment require different tests. Three focused modules passed
30 axiom checks within `{propext, Quot.sound}` (three axiom-free).
This is zero-term cancellation, **not** a positive-response bound: disconnected
caps can pass parity, and surviving connected interactions remain to be bounded.

The preceding [connected full-tube transmission](lean/YMGap/Continuum/BF4ExactSlabFullHeatTubeCovariance.lean)
now includes the partition and **both endpoint means**. The original twelve
full heat factors preserve the retained boundary mass. Their connected
numerator is exactly `w^36` times the upper boundary variance numerator,
at every volume margin and `K >= 1`. A nonzero boundary mean is retained,
not discarded. The [all-length identity](lean/YMGap/Continuum/SU2QuaternionFullHeatTubeCovariance.lean)
also allows a separate nome in each layer. Four focused modules passed
20 axiom checks within `{propext, Quot.sound}`; no full-tree audit is claimed.

The preceding [full heat-kernel tube contraction](lean/YMGap/Continuum/BF4ExactSlabFullHeatTubeContraction.lean)
now holds on the original slab at **every volume margin and every cutoff
`K >= 1`**, for arbitrary rational nome `w`. Its twelve factors use the
existing original `heatWeights`, retaining every spin before integration;
the exact transmission is `w^36`, with the boundary and all spectators kept
on the same carrier. The [arbitrary-length identity](lean/YMGap/Continuum/SU2QuaternionFullHeatTubeComposition.lean)
gives `w^(12*n)`, or the product of the layer-dependent nomes to power 12.
It composes the [two-link transmission](lean/YMGap/Continuum/SU2QuaternionRelativeHeatTransmission.lean)
through the four ordered quaternion factors without commuting them.

**What this does not prove:** the retained boundary must be independent of
the twelve integrated links. The other interacting plaquettes need not
satisfy that guard. Their cancellation-preserving signed estimate, the
centered normalized response floor, and its cutoff/volume persistence remain
open. The conditional connected identity holds even for signed boundary
weights; it does not assert positivity for arbitrary such weights. It is
not the full interacting covariance or a coupling-uniform mass gap.

The preceding [three-layer conditional tube identity](lean/YMGap/Continuum/BF4ExactSlabTubeCarrierContraction.lean)
now holds on the **original full link carrier at every volume margin**, with
exact coefficient `w^36` for its selected fundamental factors. One [explicit permutation](lean/YMGap/Continuum/BF4ExactSlabTubeCarrierEmbedding.lean)
places the sixteen tube links first and retains every spectator. The
[ordered word and product pins](lean/YMGap/Continuum/BF4ExactSlabTubeCarrierWords.lean)
identify all twelve actual swept side faces, including centered endpoint
products. The preceding [common gauge sweep](lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTemporalSweep.lean)
preserves the full original action and probe. **The conditional identity is
not a positive lower bound for the full interacting covariance:** it accepts
arbitrary retained boundary data, but not dependence on the twelve integrated
links. Controlling the remaining signed interactions and preserving the
signal through cutoff and volume limits are still open.

## Whole-project goal

The Clay target requires a non-trivial quantum Yang--Mills theory on
`R^4`, satisfying suitable QFT axioms, with an isolated vacuum and a uniform
mass gap `Delta > 0` for every compact simple gauge group. The repository is
currently pursuing SU(2) as the concrete non-abelian construction; a valid
all-group lift remains separate work.

```text
WHOLE-PROJECT GOAL / CLAY TARGET
Continuum 4D Yang--Mills + QFT axioms + isolated vacuum + Delta > 0
for every compact simple gauge group, in Lean within the MLTT/HoTT gate
                                  |
                   EXPAND into necessary inputs
                                  v
CURRENT CONDITIONAL BRANCH: positive multiplicity-product law
  finite contraction, 0<w<=1/2 and K>=K0(w); rate depends on w      [PROVED]
    + cutoff limit + reflected marginal completion                 [PROVED]
    -> completed gap / decay / vacuum isolation at w=1/400, extent 1 [PROVED]
                                  |
        identity with the ORIGINAL signed exact-Haar law
                                  X                               [REFUTED]
        The original vacuum-delta quadratic is 1; the positive-law
        value is strictly smaller, every w>0 and K>=1.
        NO causal arrow from this identity to a Yang--Mills gap.

REQUIRED PHYSICAL ROUTE: ORIGINAL signed SU(2) slab law
  original weights, signed boundary sums, same Haar carrier        [PROVED]
       |
       +--> full Haar pin + literal U = theta(L)
       |      + lower locality + actual square channels            [PROVED]
       |      -> ORIGINAL mixed Gram identity
       |      -> symmetry + positivity, all odd extents, w>=0      [PROVED]
       |                       |
       |                       +----------------------------------+
       |                                                          |
       +--> exposed links + four swaps + harmonic degree selection |
              + SAME boundary zero extension                       |
              -> ORIGINAL full bilinear cutoff limit              |
                 + computed pair-dependent modulus                [PROVED]
                                  |                               |
                                  +<---- BOTH inputs --------------+
                                  v
  One common original GNS form per odd slab, w>=0                   [PROVED]
    -> null quotient + constructive CReal Hilbert completion       [PROVED]
    -> all cutoff anchors in that slab share ONE completed carrier [PROVED]
       with exact original finite/limit inner-product pins         [PROVED]
                                  |
                                  +<-- all-extent norm-one,
                                  |    non-null boundary CODE       [PROVED]
                                  |      -> code-centered completed
                                  |         pairing = original
                                  |         finite code covariance  [PROVED]
                                  +--> full heat-unit sequence:
                                  |    ORIGINAL three-cutoff pairing[PROVED]
                                  |      + original face remainders
                                  |        with w-dependent moduli  [PROVED]
                                  |      -> shared-variable product
                                  |         remainder + norm pin    [PROVED]
                                  |      -> growing-unit GNS Cauchy
                                  |         + explicit modulus      [PROVED]
                                  |      -> completed full unit     [PROVED]
                                  |         for each 0<w<1, odd slab
                                  |      + full action-integral limit
                                  |      + vanishing interface error[PROVED]
                                  |      -> completed squared norm
                                  |         = ORIGINAL action limit [PROVED]
                                  |      -> finite-floor criterion
                                  |         and nonzero consequence [PROVED]
                                  |      + retained original channel
                                  |         Z_K >= lowerHaar_K^2    [PROVED]
                                  |      -> lower-half finite margin
                                  |         suffices for full floor [PROVED]
                                  |      + differentiated JTP
                                  |        + Euler prefix/tail floor
                                  |        + first positive S term  [PROVED]
                                  |        -> original heat floor
                                  |           c(w)>0 on [-1,1]      [PROVED]
                                  |        + finite derivative error
                                  |          with computed cutoff   [PROVED]
                                  |        -> late character prefixes
                                  |           >= c(w)/2             [PROVED]
                                  |        + exact face evaluation  [PROVED]
                                  |          + scalar boxes at the
                                  |            common environment    [INPUT]
                                  |        -> shared-link product
                                  |           pointwise floor b(w)^F[PROVED]
                                  |      + actual Haar-unit holonomy
                                  |        -> four-square certificate
                                  |           for 1+face scalar     [PROVED]
                                  |      + finite Jacobi derivative
                                  |        has nonnegative shifted
                                  |        coefficients, constant>=c[PROVED]
                                  |        -> SAME shared-link Haar
                                  |           approximant floor c^F [PROVED]
                                  |        + coefficient-level pin
                                  |          to weighted heat terms [PROVED]
                                  |        -> same floor for WEIGHTED
                                  |           original face-product [PROVED]
                                  |        + finite-band weight loss
                                  |          + original coefficient tail
                                  |          + shared-link telescope[PROVED]
                                  |        -> quantified Haar passage
                                  |           to ORIGINAL heat action[PROVED]
                                  |      -> strict positive floor
                                  |         for THAT action limit   [PROVED]
                                  |      -> successful finite certificate
                                  |         + non-null full heat unit[PROVED]
                                  |      -> explicit reciprocal of Z
                                  |         with positive bounds    [PROVED]
                                  |      -> SAME completed pairing / Z
                                  |         + full unit norm one
                                  |         + norm/rate comparison  [PROVED]
                                  |      + original action with
                                  |        arbitrary polynomial p
                                  |        + insertion-tail modulus [PROVED]
                                  |        + same-link positive
                                  |          approximants and limit [PROVED]
                                  |      -> E(p)=N(p)/SAME Z
                                  |         + E(1)=1 + E(p^2)>=0
                                  |         + explicit real modulus [PROVED]
                                  |      + concrete lower plaquette
                                  |        algebra + literal reflection
                                  |        + temporal Haar pin       [PROVED]
                                  |      -> SAME full-action reflected
                                  |         numerator = square value [PROVED]
                                  |      -> E(theta(p)*p)>=0
                                  |         + reflected unit = 1     [PROVED]
                                  |      + ORIGINAL action reflection
                                  |        invariance at every cutoff[PROVED]
                                  |      -> finite plaquette GNS / CS[PROVED]
                                  |        + original numerator limits
                                  |          + SAME positive Z       [PROVED]
                                  |      -> normalized reflected form
                                  |         symmetric, bilinear, CS
                                  |         + norm-null descent
                                  |         + explicit real modulus [PROVED]
                                  |      -> actual null quotient
                                  |         + positive-definite form[PROVED]
                                  |      -> Cauchy completion CARRIER
                                  |         + injective embedding
                                  |         + nonzero unit          [PROVED]
                                  |      + explicit pairing tolerance
                                  |        + computed Cauchy bounds
                                  |        + two-level limit moduli [PROVED]
                                  |      -> completed mixed pairing
                                  |         + representative descent
                                  |         + original-form pin
                                  |         + symmetry/positivity
                                  |         + unit diagonal one     [PROVED]
                                  |      + explicit addition/scaling
                                  |        continuity tolerances    [PROVED]
                                  |      -> completed rational linear
                                  |         laws + bilinearity      [PROVED]
                                  |      + pairing rate controls
                                  |        distance to its limit    [PROVED]
                                  |      -> completed norm zero
                                  |         iff completed state zero[PROVED]
                                  |      +--> original CS + product
                                  |      |    continuity through limits[PROVED]
                                  |      |    -> sharp completed CS
                                  |      |       + distance geometry [PROVED]
                                  |      |    -> explicit approximants
                                  |      |       from supplied reps [PROVED]
                                  |      |    -> represented-row limits
                                  |      |       + computed rate
                                  |      |       + row independence [PROVED]
                                  |      |
                                  |      +--> supplied scalar QCauchy data
                                  |           + computed tail ceilings
                                  |           -> SAME real-scalar action
                                  |              + representative descent
                                  |              + arithmetic laws/moduli
                                  |              + distance scaling [PROVED]
                                  |      + SAME pairing modulus
                                  |        + original unit norm one [PROVED]
                                  |      -> P(x)=<x,u>u; C(x)=x-P(x)
                                  |         + orthogonal projections
                                  |         + Pythagoras / no norm loss[PROVED]
                                  |      + literal mean E(p) pin
                                  |      -> <C(p),C(q)> equals
                                  |         E(theta(p)q)-E(p)E(q)
                                  |         + explicit real modulus [PROVED]
                                  |      + original approximants/rows
                                  |      -> centered approximation
                                  |         + represented-row limits[PROVED]
                                  |      + original square-tree channels
                                  |        -> two distinct retained leaves
                                  |        -> centering-invariant minor
                                  |        -> finite raw norm floor [PROVED]
                                  |      + fundamental coordinate leaves
                                  |        -> literal plaquette-boundary
                                  |           channels + heat weights[PROVED]
                                  |      + reference Haar mixed moment
                                  |        = 1/128; determinant nonzero[PROVED]
                                  |      + original heat-dressed
                                  |        four-moment identity      [PROVED]
                                  |      + small-nome face guards
                                  |        -> shared-link moment error
                                  |           bound, independent of K[PROVED]
                                  |      + w=1/1024, extent-one
                                  |        kernel guard certificate
                                  |        -> D <= -1/1024, every K [PROVED]
                                  |        -> concrete positive minor
                                  |           for every K>=1         [PROVED]
                                  |        -> one raw norm floor,
                                  |           every K>=1 and center c[PROVED]
                                  |      + SAME action reciprocal
                                  |        + cutoff/centering limits [PROVED]
                                  |      -> nonzero centered observable
                                  |         + positive normalized floor
                                  |         + norm Cauchy modulus,
                                  |         at THAT w and slab       [PROVED]
                                  |      + actual geometric face maps
                                  |        + independent padding/lags
                                  |        -> original time-separated
                                  |           connected correlations
                                  |           = completed pairings,
                                  |           with Cauchy moduli     [PROVED]
                                  |      + space AND time placement
                                  |        + explicit boundary margin
                                  |        -> ORIGINAL bulk correlations
                                  |           = completed pairings  [PROVED]
                                  |      + actual embedded face list
                                  |        + exterior face complement
                                  |        -> exact ORIGINAL action
                                  |           = interior * exterior [PROVED]
                                  |        -> boundary covariance D
                                  |           + same-cutoff modulus
                                  |           + limit comparison
                                  |             E_full(p) I(1)-I(p)
                                  |               = D(p)/Z_full     [PROVED]
                                  |      + injective actual link map
                                  |        + Haar/ordered action pins
                                  |        -> I(embed p) = N_small(p)
                                  |           I(1) = Z_small        [PROVED]
                                  |        + BOTH original reciprocals
                                  |        -> E_large(embed p)-E_small(p)
                                  |           = D/(Z_large Z_small) [PROVED]
                                  |           for actual bulk means,
                                  |           with Cauchy data      [PROVED]
                                  |      + original unit holonomies
                                  |        + computed square bounds
                                  |        + positivity and E(1)=1
                                  |        -> original bulk means,
                                  |           OS/centered norms and
                                  |           correlation SIZE bounds
                                  |           independent of w/padding
                                  |           for fixed expressions [PROVED]
                                  |      + all-spin Haar certificates
                                  |        + ORIGINAL Casimir weights
                                  |        + explicit small-nome guard
                                  |        -> one-face remainder
                                  |           delta(w)=128*w^3,
                                  |           all K and extents     [PROVED]
                                  |        + constructed ORIGINAL
                                  |          positive face backgrounds
                                  |        -> ONE-face integral factors
                                  |           1-delta(w),1+delta(w)
                                  |           independent of volume [PROVED]
                                  |      + exact finite face selections
                                  |        + shared-link interval products
                                  |        -> ORIGINAL activities bounded
                                  |           by delta(w)^n          [PROVED]
                                  |      + literal face-link locality
                                  |        + original Haar factorization
                                  |        -> disconnected-split connected
                                  |           numerator cancels     [PROVED]
                                  |      + actual exterior selections
                                  |        -> EXISTING boundary D equals
                                  |           sum of selection responses
                                  |           at the SAME cutoff    [PROVED]
                                  |        -> empty / entirely detached
                                  |           selections vanish     [PROVED]
                                  |      + finite inclusion-exclusion
                                  |        of ORIGINAL connected numerator
                                  |        + computed selected-face cuts
                                  |        -> separated coefficients vanish
                                  |           even in interacting slabs
                                  |        -> SAME boundary D: exterior sum
                                  |           of filtered interior sums
                                  |           with no separating cut [PROVED]
                                  |      + SAME two-copy Haar moment form
                                  |        + exact three-term insertion
                                  |        -> two-probe coefficient bound
                                  |           2*c_p*c_q*kappa(w)^n,
                                  |           kappa=2*delta+delta^2 [PROVED]
                                  |        -> original boundary D has a
                                  |           computed finite majorant
                                  |           independent of cutoff [PROVED]
                                  |      + ANCHORED spectator families:
                                  |        exact signed resummation
                                  |        -> original spectator Z^2
                                  |        + computed detached/collar split
                                  |        + removed-face partition cost
                                  |        -> F^2*|family| <= cap*Z^2 [PROVED]
                                  |      + literal rooted graph + Type paths
                                  |        + input-order core/complement
                                  |        -> complement = detached filter
                                  |        + coefficient permutation pin
                                  |        -> ORIGINAL D grouped by cores
                                  |           with no double counting[PROVED]
                                  |      + fixed-core stability
                                  |        + ambient-order merge/decode
                                  |        -> actual fiber = ALL detached
                                  |           spectator selections  [PROVED]
                                  |        -> family = core coefficient * Z^2
                                  |        -> FULL original D exhausted
                                  |           by bounded families   [PROVED]
                                  |      + MIXED-ACTION probe-only root:
                                  |        same D, two original actions
                                  |        -> exterior spectators resummed
                                  |           into Z_det * Z_inside-det
                                  |        + all-interior cores cancel
                                  |        -> SINGLE rooted sum for D
                                  |           + explicit root-to-exterior
                                  |             path for each retained core
                                  |        + two removed-face comparisons
                                  |        -> R*|actual family| <=
                                  |           |NEW mixed coefficient| *
                                  |           Z_full * Z_inside     [PROVED]
                                  |      + selective two-slot insertion:
                                  |        exterior cost delta(w),
                                  |        interior cost 2*delta+delta^2
                                  |        -> NEW mixed-coefficient bound
                                  |           at every cutoff K     [PROVED]
                                  |        + positive local collar floor
                                  |        -> computed finite budget B
                                  |           with NO cutoff K
                                  |        -> |D_K| <= 2*c*B*
                                  |           Z_full,K * Z_inside,K [PROVED]
                                  |      + six faces per literal link
                                  |        -> |collar| <= 6*(ell+4*n)[PROVED]
                                  |        -> collar absorbed into
                                  |           A(w,ell)*rho(w)^n     [PROVED]
                                  |        -> SAME D controlled by
                                  |           sum_active rho^|core| [PROVED]
                                  |      + connected M-face probe carrier
                                  |        (singleton constructed)  [INPUT]
                                  |        -> actual core becomes a
                                  |           literal animal, <=M+n [PROVED]
                                  |        + carrier-intersection mask
                                  |        -> tour decoder restores
                                  |           ORIGINAL core exactly [PROVED]
                                  |        -> actual size-n count
                                  |           <=C(probe)*625^n      [PROVED]
                                  |           singleton C=1250      [PROVED]
                                  |        + s(w)=625*rho(w)<1
                                  |          at w=1/1024            [PROVED]
                                  |        -> actual weighted sum
                                  |           <= C*s^d/(1-s)        [PROVED]
                                  |           when all sizes >= d
                                  |        + active sizes >= 1      [PROVED]
                                  |        -> ORIGINAL D_K bounded by
                                  |           2*c*A*C*s/(1-s) times
                                  |           its two unit moments [PROVED]
                                  |        + grow INNER margin around
                                  |          a fixed base probe
                                  |        -> original exterior
                                  |           distance >= margin    [PROVED]
                                  |        -> core size >= margin+1-M
                                  |           singleton: >= margin  [PROVED]
                                  |        -> ORIGINAL D_K bounded by
                                  |           2*c*amplitude*s^margin
                                  |           times its unit moments[PROVED]
                                  |           singleton; w=1/1024
                                  |           ANY outer padding
                                  |        + ORIGINAL reciprocals
                                  |          and literal image pins [PROVED]
                                  |        -> cancel SAME partitions
                                  |           at cutoff limits      [PROVED]
                                  |        -> |E_(m+p)(chi)-E_m(chi)|
                                  |           <= A_spin*s^m         [PROVED]
                                  |           ANY outer padding p
                                  |        + explicit outer/inner
                                  |          Cauchy moduli          [PROVED]
                                  |        -> thermodynamic limit of
                                  |           ONE plaquette's
                                  |           character means       [PROVED]
                                  |           fixed w=1/1024
                                  |        + connected box carrier,
                                  |          size-preserving shifts [PROVED]
                                  |        + expression support,
                                  |          bounds + image pins    [PROVED]
                                  |        -> mixed-expression
                                  |           normalized comparison [PROVED]
                                  |           A(e,base,w)*s^(m+1-M)
                                  |        + explicit volume moduli
                                  |        -> mixed-expression
                                  |           thermodynamic limits  [PROVED]
                                  |           unit, linearity,
                                  |           square positivity     [PROVED]
                                  |        + base-change tail pin
                                  |        + original Haar-carrier
                                  |          semantic equality      [PROVED]
                                  |        -> ONE lower observable
                                  |           quotient algebra      [PROVED]
                                  |           positive functional,
                                  |           unit distinct from 0  [PROVED]
                                  |        + all-face support/bounds
                                  |          + reflected-product pin[PROVED]
                                  |        -> all-face moments with
                                  |           volume moduli          [PROVED]
                                  |        + ORIGINAL finite OS
                                  |          positivity and CS       [PROVED]
                                  |        -> thermodynamic reflected
                                  |           form + connected means[PROVED]
                                  |        + original mean size caps [PROVED]
                                  |        -> connected covariance
                                  |           boundary-error modulus[PROVED]
                                  |        + common-volume tails and
                                  |          lower-carrier equality [PROVED]
                                  |        -> ONE semantic OS pairing[PROVED]
                                  |        + radical-zero law       [PROVED]
                                  |        -> positive-definite OS
                                  |           null quotient         [PROVED]
                                  |        + squared-distance laws
                                  |          and Cauchy moduli      [PROVED]
                                  |        -> completion CARRIER,
                                  |           injective OS embedding[PROVED]
                                  |           nonzero unit          [PROVED]
                                  |        + SAME form continuity
                                  |          + computed Cauchy caps
                                  |          + two-level limit rates[PROVED]
                                  |        -> completed pairing with
                                  |           original-form pins,
                                  |           unit norm one and CS  [PROVED]
                                  |        + SAME rate gives explicit
                                  |          zero-closeness witness [PROVED]
                                  |        -> zero norm iff zero
                                  |           completed state       [PROVED]
                                  |        + semantic addition/scaling
                                  |          + continuity moduli    [PROVED]
                                  |        -> completed rational laws
                                  |           and bilinearity       [PROVED]
                                  |        -> SAME squared distance,
                                  |           certified approximants[PROVED]
                                  |        + supplied Cauchy rows
                                  |          and outer modulus       [INPUT]
                                  |        -> diagonal limit + rate,
                                  |           row independence and
                                  |           same-class recovery   [PROVED]
                                  |        + modulus-bearing real action
                                  |          + actual pairing moduli[PROVED]
                                  |        -> SAME unit projection
                                  |           and exact centering   [PROVED]
                                  |        -> Pythagoras, no norm loss
                                  |           and unit complement   [PROVED]
                                  |        + original mean/form pins[PROVED]
                                  |        -> centered pairing equals
                                  |           ORIGINAL covariance,
                                  |           with volume error rate[PROVED]
                                  |        -> centered approximants
                                  |           and represented limits
                                  |           preserve their rates  [PROVED]
                                  |        + literal physical time
                                  |          composition and rebasing[PROVED]
                                  |        -> actual translated states
                                  |           in SAME completion,
                                  |           lag-uniform size cap  [PROVED]
                                  |        -> SAME original two-time
                                  |           covariance limits,
                                  |           explicit volume rate  [PROVED]
                                  |      + off-center actual link map
                                  |        + full/interior action pin
                                  |        + exterior distance floor[PROVED]
                                  |        -> ORIGINAL boundary decay
                                  |           for allowed time offsets
                                  |           + same-cutoff modulus [PROVED]
                                  |        + SAME partition cancellation
                                  |        -> normalized off-center
                                  |           expectation comparison[PROVED]
                                  |        + shifted-expression producer
                                  |          and limit comparison   [PROVED]
                                  |        -> ORIGINAL spacetime-law
                                  |           time invariance       [PROVED]
                                  |        + literal reflected-product
                                  |          coordinate identity    [PROVED]
                                  |        -> reflected time balance
                                  |           + same-object sum-lag
                                  |             covariance identity [PROVED]
                                  |        + linearity and positivity
                                  |        -> OS-null preservation  [PROVED]
                                  |        -> time semigroup on the
                                  |           EXISTING dense OS space
                                  |           symmetric, linear,
                                  |           unit/mean preserving  [PROVED]
                                  |        + lag-independent original cap
                                  |          and reflected positivity
                                  |        -> bounded midpoint doubling
                                  |           with EVENTUAL bounds  [PROVED]
                                  |        -> ORIGINAL OS-norm and
                                  |           distance contraction  [PROVED]
                                  |        -> completed time semigroup
                                  |           SAME Cauchy moduli;
                                  |           symmetric, linear,
                                  |           fixed nonzero unit    [PROVED]
                                  |        -> positive two-step transfer
                                  |           + invariant unit complement
                                  |           + ORIGINAL connected
                                  |             correlation moments [PROVED]
                                  |      + ORIGINAL signed connected
                                  |        numerator expansion      [PROVED]
                                  |        + no separating cut
                                  |        -> actual TWO-probe path
                                  |        -> literal animal, size
                                  |           <= M_left+M_right+n   [PROVED]
                                  |        -> faithful tour+mask count
                                  |           <= 2^M*625^(M+n),
                                  |           M=M_left+M_right      [PROVED]
                                  |        + SAME spectator Z^2
                                  |          and local collar floor
                                  |        + distance+1 <= M+n
                                  |        -> |ORIGINAL D_K| <=
                                  |           A(w,probes)*s(w)^
                                  |           (distance+1-M)*Z_K^2 [PROVED]
                                  |        + SAME cutoff limits and
                                  |          exact Z^2 cancellation
                                  |        -> normalized covariance [PROVED]
                                  |        + separate fixed-size
                                  |          reflected-time probes
                                  |        -> root distance = s+t   [PROVED]
                                  |        + ORIGINAL volume limit
                                  |          and operator-moment pin
                                  |        -> time decay of THESE
                                  |           completed OS moments,
                                  |           explicit time modulus [PROVED]
                                  |        + contraction and sharp CS
                                  |        -> dyadic moments remove
                                  |           observable prefactor
                                  |        -> dense strict form gap [PROVED]
                                  |        + SAME centered Cauchy
                                  |          pairing limits
                                  |        -> 0 <= <v,T_2 v>
                                  |           <= (1/2)<v,v>, every
                                  |           unit-complement v     [PROVED]
                                  |        + SAME time composition,
                                  |          unit projection and
                                  |          squared-norm identity
                                  |        -> relaxation to unit line
                                  |           with computed modulus [PROVED]
                                  |        -> every positive-time
                                  |           fixed state lies in
                                  |           that SAME unit line   [PROVED]
                                  |        + exact geometric sums of T_2
                                  |          + explicit tail modulus [PROVED]
                                  |        + SAME represented Cauchy
                                  |          limit, no representative
                                  |          selection              [PROVED]
                                  |        -> R=(I-T_2)^(-1) on the
                                  |           unit complement,
                                  |           norm^2 bound 4        [PROVED]
                                  |      + local channel selection,
                                  |        ALL spectator channels kept
                                  |        -> ORIGINAL raw-form bound
                                  |        + whole-forest CS tests
                                  |        -> centering-invariant
                                  |           two-test minor bound  [PROVED]
                                  |        + translated probe geometry:
                                  |          four crossing faces,
                                  |          lower collar <= 24     [PROVED]
                                  |        + SAME local Haar moments
                                  |          0, 0, 1/128, all volumes
                                  |        -> explicit local tests,
                                  |           detached reference
                                  |           determinant -Zref^2/128
                                  |                                 [PROVED]
                                  |        + full spectator interface Isp
                                  |        -> actual test Haar formulas
                                  |           + positive OS background
                                  |           Zsp=H(theta Lfar*Lfar*Isp)
                                  |           (volume-dependent floor)
                                  |                                 [PROVED]
                                  |        + every spectator channel
                                  |          avoids the probe links
                                  |        -> full-Zsp local reference
                                  |           Dref=s^2 Zsp^4,
                                  |           Rref=s Zsp^3           [PROVED]
                                  |           s=(2*w^3)^4/32768
                                  |        + ordinary Haar positivity
                                  |          on SAME spectator law
                                  |        + sharp local caps 2,1
                                  |          + exact scalar-square
                                  |            background Zsp/256
                                  |        + relative collar errors [PROVED]
                                  |        -> ORIGINAL interacting
                                  |           det <= -(s/2)*Zsp^2
                                  |           minor >= (s/2)^2*Zsp^4
                                  |           > 0, all K>=1,half    [PROVED]
                                  |        + reference budget <=2*s*Zsp^3
                                  |          AND full Z<=2*Zsp     [PROVED]
                                  |        -> normalized floor s/16
                                  |           through cutoff limit,
                                  |           every volume         [PROVED]
                                  |        + SAME covariance volume
                                  |          limit and centered pin
                                  |        -> nonzero thermodynamic
                                  |           excitation, norm^2>=s/16
                                  |           with explicit moduli [PROVED]
                                  |        + positive-time fixed-space
                                  |          characterization
                                  |        -> probe not fixed at any
                                  |           positive integer time[PROVED]
                                  |      + full quotient-level
                                  |        completeness              [OPEN]
                                  |      + physical realization and
                                  |        observable-action maps    [OPEN]
                                  |      + all required gauge observables
                                  |        beyond this subalgebra     [OPEN]
                                  |      + physical vacuum
                                  |        identification             [OPEN]
                                  +<-- larger-slab compatibility      [OPEN]
                                  +<-- physical observable/unit
                                  |    realization                    [OPEN]
                                  v
  Full required positive-time physical realization                  [OPEN]
                                  |
                                  +<-- continuum continuous-time
                                  |    semigroup / generator         [OPEN]
                                  +<-- stationary physical vacuum     [OPEN]
                                  +<-- strict bound on ITS completed
                                  |    vacuum complement              [OPEN]
                                  v
  Physical spectral gap on the SAME objects                         [OPEN]
                                  |
                                  +<-- volume + spacing mass control  [OPEN]
                                  +<-- constructive limits + QFT      [OPEN]
                                  +<-- remaining compact simple groups[OPEN]
                                  v
                 CONTRACT through proved same-object bridges
Continuum 4D Yang--Mills + QFT axioms + isolated vacuum + Delta > 0
WHOLE-PROJECT GOAL / CLAY TARGET

Scope: arbitrary signed boundary coefficients; original overlapping links.
Finite-slab positivity is not a strict gap, compatibility or continuum limit.
The normalized FULL heat unit is not yet a stationary physical vacuum.
```

`INPUT` marks an explicit hypothesis, not a discharged prerequisite.
`PROVED` means kernel-checked at exactly the displayed scope. It does not mean
that downstream arrows have been proved. `PARTIAL` means concrete objects and
useful theorems exist but a required bridge is missing.

## Current frontier

For the live frontier, use the latest result at the top of this page and
the [current work plan](work_plan.md#current-original-action-gap-and-continuum-frontier-2026-09-17-utc).
The route correction and resolvent account below are historical checkpoints.

**Route correction: the literal exact-Haar/positive-law identity is
refuted, not an open identity to prove.** The preceding roadmap mislabeled
`ExactHaarPhysicalPerronSameActionAt` as an available next bridge. The
repository already refutes it at cutoff one and every positive coupling:
[`exactHaarPhysicalPerronSameActionAt_cutoffOne_uninhabited`](lean/YMGap/Continuum/BF4ExactPhysicalPerronSameActionFence.lean#L565).
The canonical `[BF4-exact-physical-Perron]` ledger entry already records
this obstruction. The completed conditional gap remains valid for its
own operator; it cannot cross that refuted identity.

**Historical result: a bounded constructive inverse on the original unit complement.**
The [finite geometric series](lean/YMGap/Continuum/BF4ExactSlabThermodynamicResolventPartial.lean)
is `S_n x = sum_{j<n} T_(2j)(center x)`. The existing decay gives
`||T_2 v||^2 <= (1/4)||v||^2` on the complement. The squared-norm triangle
inequality therefore proves `||S_n x||^2 <= 4||center x||^2` by induction;
exact tail splitting and the original relaxation modulus give Cauchy data.

The [same-carrier limit](lean/YMGap/Continuum/BF4ExactSlabThermodynamicResolvent.lean)
defines `R` on every completion class, independently of the supplied
representative. It proves both inverse equations and returns a
`solutionCertificate` with its actual vector and approximation modulus.
The [boundedness theorem](lean/YMGap/Continuum/BF4ExactSlabThermodynamicResolventBound.lean)
proves addition, modulus-bearing real-scalar linearity, and
`||R x-R y||^2 <= 4||x-y||^2`. The norm proof is linear cancellation, with
no spectral decomposition or division by a vector norm.

This is the reduced resolvent of the existing geometric `T_2`, not a
link-variable heat-bath generator or a continuum Hamiltonian. Supplied
Cauchy rows suffice for this construction; full quotient-level completeness
has not thereby been proved. In particular, a nonzero excitation and this
inverse do not prove a strictly positive `T_2` response on that excitation.
That response, full positive-time observable realization, continuum scaling,
generator/spectral identification, QFT axioms and the remaining groups stay open.

Verification: three modules, 19+16+13=48 exactly matched focused axiom gates,
all within `{propext, Quot.sound}`; final logs error/warning free and
own/direct-import artifacts fresh. The exact scalar pilot passed. One monitored
worker, mandatory 20 GiB ceiling; no full build/audit/guard/progress run.
Root imports updated, not rebuilt. No canonical frontier atom/type/flag changed.

**Preceding result: a spectator-preserving construction of a nonzero thermodynamic excitation.**
The new witness concerns the original thermodynamic plaquette OS completion,
not only the earlier extent-one slab. Its normalized floor survives both
cutoff removal and increasing volume. The following chain records why.
[Partial interface retention](lean/YMGap/Continuum/BF4ExactSlabPartialInterfaceRetention.lean)
now selects original unit/fundamental channels locally while leaving all
channels of unselected faces intact. Its lower-bound theorem applies to
the ORIGINAL reflected numerator, every odd extent and `K>=1`, `w>=0`.
Keeping all channels recovers that numerator exactly.

[Whole-forest tests](lean/YMGap/Continuum/BF4ExactSlabPartialInterfaceTests.lean)
then produce explicit amplitudes `A_i(e)` and reference energies `E_i`, with
`A_i(e)^2 <= rawForm(e,e)*E_i`. The computed determinant square
`D(e)=(A_0(e)A_1(1)-A_1(e)A_0(1))^2` is unchanged by rational recentering
and satisfies `D(e) <= rawForm(e-c,e-c)*R`, with explicit reference budget
`R=2*(E_0*A_1(1)^2+E_1*A_0(1)^2)`.

The [translated local geometry](lean/YMGap/Continuum/BF4ExactSlabBulkProbeInterface.lean)
now identifies exactly four crossing faces and a lower collar of at most
24 faces, independently of volume. The [original local Haar moments](lean/YMGap/Continuum/BF4ExactSlabBulkProbeHaarReference.lean)
are `0, 0, 1/128` at every translated volume. The scalar polynomial is
exactly the selected original coordinate-channel product.

[Concrete tests](lean/YMGap/Continuum/BF4ExactSlabBulkProbeSpectatorTests.lean)
use `Lfar` and `scalarLoop*Lfar`, where `Lfar` is the original detached
lower heat product. The probe is pinned to the existing thermodynamic
family. Its detached squared-background reference determinant is exactly
`-Zref^2/128`, where `Zref = Haar(Lfar^2)`. This reference is **not** the
full spectator OS partition or the interacting whole-forest minor.

[Exact interface factorization](lean/YMGap/Continuum/BF4ExactSlabBulkProbeInterfaceFactorization.lean)
now identifies the retained unit interface as the full spectator heat
product `Isp`, and the scalar interface as
`(2*w^3)^4 * theta(scalarLoop) * scalarLoop * Isp`.
[Interacting amplitude formulas](lean/YMGap/Continuum/BF4ExactSlabBulkProbeInteractingAmplitudes.lean)
keep the full original lower action in both tests. The unit reference
energy is exactly `Zsp=Haar(theta(Lfar)*Lfar*Isp)`. It is strictly positive
at the existing nome `w=1/1024`, for every cutoff and half-size, with the
explicit floor `((1-128*w^3)^N)^2`, `N=lowerSpectators.length`.
This floor is cutoff-independent but **volume-dependent**; `Zsp` has not
been equated to the earlier bare reference `Zref`.

[Full spectator factorization](lean/YMGap/Continuum/BF4ExactSlabBulkProbeSpectatorFactorization.lean)
now proves that every spectator channel avoids the probe links. Removing
only the local lower collar gives the exact reflected pairing
`Haar(p)*Haar(q)*Zsp`. The [reference calculation](lean/YMGap/Continuum/BF4ExactSlabBulkProbeSpectatorReferenceMinor.lean)
then gives `Dref=s^2*Zsp^4`, `Rref=s*Zsp^3`, and
`Dref=(s*Zsp)*Rref`, with `s=(2*w^3)^4/32768`.
The actual original test energies are `Zsp` and `(s/2)*Zsp`.
The reference minor is positive at the fixed nome for every cutoff and
volume. These are reference values; the interacting minor is bounded
separately below.

The [ordinary spectator heat certificate](lean/YMGap/Continuum/BF4ExactSlabSpatialHeatCertificate.lean)
now strengthens OS positivity to positive-certificate integration, using the
actual two-link character/Gram identity under arbitrary Haar insertions.
The [same-background comparison](lean/YMGap/Continuum/BF4ExactSlabBulkProbePositiveBackground.lean)
preserves `Zsp` exactly. The [local collar interval](lean/YMGap/Continuum/BF4ExactSlabBulkProbeCollarInterval.lean)
has cap `(1+128*w^3)^24-1`, for the lower collar and its explicit reflected
face list, independently of cutoff and volume. At `w=1/1024`, the cap is
kernel-checked to be at most `1/262144`; the signed lower-collar remainder
integral is at most `Zsp/262144` in absolute value. Additional interval
insertions retain their stated caps.

[Sharp local intervals](lean/YMGap/Continuum/BF4ExactSlabBulkProbeLocalIntervals.lean)
give cap `2` for the actual fundamental probe and `1` for the scalar loop,
including their reflected presentations. Keeping the lower scalar square
inside the [positive background](lean/YMGap/Continuum/BF4ExactSlabBulkProbeScalarBackground.lean)
retains its exact mass `Zsp/256`. The [original interacting amplitudes](lean/YMGap/Continuum/BF4ExactSlabBulkProbeAmplitudePerturbation.lean)
are now their full-spectator references plus explicit signed errors:
`|E0| <= c*eta(w)*Zsp`, `|E1| <= lambda(w)*c*eta(w)*Zsp/256`, with
`c=2` for the probe and `c=1` for the unit. All original collar factors
and selected-channel weights are retained in these identities.

The [interacting minor theorem](lean/YMGap/Continuum/BF4ExactSlabBulkProbeInteractingMinor.lean)
now proves `det <= -(s/2)*Zsp^2` and `minor >= ((s/2)*Zsp^2)^2 > 0`,
at `w=1/1024`, every `K>=1` and translated half-size. This is the actual
original whole-forest minor **with the local collar reinstated**.

The [homogeneous floor](lean/YMGap/Continuum/BF4ExactSlabBulkProbeHomogeneousFloor.lean)
now bounds the matching original reference budget by `2*s*Zsp^3`.
Cancellation against the minor floor gives `rawForm(P-c,P-c)>=(s/8)*Zsp`
for every rational centering `c`, cutoff `K>=1` and translated volume.
The [full-partition comparison](lean/YMGap/Continuum/BF4ExactSlabBulkProbePartitionComparison.lean)
restores at most 24 lower, 24 upper and four crossing heat factors and
proves `Zfull<=2*Zsp`, using the SAME original action and its proved
temporal change of variables.

The [normalized floor](lean/YMGap/Continuum/BF4ExactSlabBulkProbeNormalizedFloor.lean)
therefore gives `gamma*Zfull<=rawForm(P-c,P-c)`, `gamma=s/16>0`.
The original cutoff limit and its exact reciprocal preserve the estimate;
the constructed centering limit gives connected covariance at least `gamma`
at every translated volume. The [thermodynamic excitation](lean/YMGap/Continuum/BF4ExactSlabThermodynamicProbeExcitation.lean)
passes this bound through the SAME covariance sequence and pins it to the
completed norm of the actual centered embedded probe. `state_ne_zero`,
`state_not_time_fixed` and `twoStep_not_identity` prove nontriviality;
`excitationCertificate`, `normCauchy` and `volumeModulus` retain the witnesses
and moduli as data.

**Open next:** the full required positive-time observable realization,
observable-action maps and quotient-level completeness on the physical
carrier. Continuum scaling, the continuous-time generator/spectral pin,
QFT axioms and the remaining compact simple groups are still open. The new
excitation and the existing form gap concern the current SU(2) plaquette
completion at fixed nome and spacing, not a continuum theory.

Latest four modules: 13+15+17+14=59 exactly matched focused gates;
nine axiom-free, all others within `{propext, Quot.sound}`. The extended
exact-rational pilot passed; its new budget, partition and normalized-floor
constants were independently kernel-checked in Lean. Final logs
error/warning free and own/direct-import artifacts fresh. One monitored
worker, mandatory 20 GiB ceiling; no full build/audit/guard/progress run.
Root imports updated, not rebuilt. No canonical frontier atom is closed.

**Most recent completed dynamical result: quantitative relaxation and uniqueness of the ORIGINAL unit fixed space.**
The completed form gap and geometric time identities now give

```text
||T_n x - P x||^2 <= (1/2)^n ||center x||^2 <= (1/2)^n ||x||^2.
T_n x = x  <=>  P x = x, for every positive integer n.
```

Here `P` is the existing original rank-one unit projection, not a newly
chosen state. [`relaxationCertificate`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicRelaxation.lean)
returns a time threshold for each positive squared-distance tolerance from
a supplied Cauchy representative and its existing pairing modulus.
[`fixedScalarWitness`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicFixedUnit.lean)
returns the actual scalar coefficient and its Cauchy data for a fixed state.
The unique fixed vector with unit coefficient one is the existing nonzero unit.

The nonzero thermodynamic excitation witness is now proved above. Full required
observable realization and quotient-level completeness, continuum scaling,
continuous-time generator/spectral identification and continuum/QFT/all-group
Clay remain open. These results concern the current plaquette OS completion
at fixed nome `1/1024` and fixed spacing, not a continuum vacuum theorem.

Two modules: 14+6=20 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final logs error/warning free and own/direct-import
artifacts fresh. One monitored worker, mandatory 20 GiB ceiling. No full
build/audit/guard/progress run; root imports updated but not rebuilt.

**Preceding result: a strict form gap for the ORIGINAL thermodynamic OS two-step transfer.**
For every vector `v` in the constructed completed unit complement,

```text
0 <= <v,T_2 v> <= (1/2)<v,v>.
```

[`complement_twoStep_form_gap`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedGap.lean)
proves this for the actual geometric two-step time operator at SU(2) nome
`1/1024` and fixed lattice spacing. No gap premise or replacement law is
supplied. This is not a continuum Hamiltonian spectral theorem, and no
nonzero excitation is established by the bound alone.

The causal proof uses the preceding signed numerator estimate:

- [Cutoff removal and normalization](lean/YMGap/Continuum/BF4ExactSlabTwoProbeCovariance.lean)
  retain explicit moduli and cancel the SAME original partition square.
- [Separate spacetime probes](lean/YMGap/Continuum/BF4ExactSlabTwoProbeSpacetimeDecay.lean)
  keep the original base-box sizes independent of time separation and volume.
- [Thermodynamic time decay](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeDecay.lean)
  identifies their distance with `s+t` and reaches the existing operator moments.
- [Temporal rate data](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeDecayRate.lean)
  supply a computed time modulus and a positive envelope `P(e,f)*(1/2)^(s+t)`.
- [Dyadic moments](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDenseGap.lean)
  remove `P`; the existing centered Cauchy limits extend the strict form
  bound to every completed unit-complement vector.

This bound feeds the relaxation and fixed-space results above; the new
thermodynamic probe supplies a nonzero excitation. Full required observable
realization and continuum scaling remain open. The coupling is fixed here; no beta- or
spacing-uniform gap is claimed.

Six new modules: 11+4+7+10+10+10=52 exactly matched focused axiom gates
within `{propext, Quot.sound}`; error/warning-free final logs and fresh
own/direct-import artifacts. One monitored worker, mandatory 20 GiB ceiling.
No full build/audit/guard/progress run; root imports updated but not rebuilt.

**Preceding result: distance decay of the ORIGINAL signed finite-slab connected numerator.**
The new [two-probe graph](lean/YMGap/Continuum/BF4ExactSlabTwoProbeGraph.lean)
keeps the probes distinct: a missing path would construct a separating cut
forbidden by the existing retained-coefficient test. Its Type-valued paths
give a [literal connected animal](lean/YMGap/Continuum/BF4ExactSlabTwoProbeAnimal.lean)
of at most `M_left+M_right+n` faces. No connecting corridor is added.
The [tour-plus-mask code](lean/YMGap/Continuum/BF4ExactSlabTwoProbeCoreCount.lean)
recovers the original face IDs in ambient order and bounds the actual
size-`n` connecting cores by `2^M*625^(M+n)`, where `M=M_left+M_right`.
The SAME original signed numerator expands exactly over this counted list.

The [local partition-relative estimate](lean/YMGap/Continuum/BF4ExactSlabTwoProbeTailBudget.lean)
resums spectators before taking absolute values and retains the original
full partition square. The [distance theorem](lean/YMGap/Continuum/BF4ExactSlabTwoProbeDistanceDecay.lean)
then supplies the geometric core-size floor, yielding

```text
|D_K(p,q)| <= A(w,p,q,probe sizes/link counts)
             * s(w)^(distance+1-M) * Z_K^2,
s(w) = 625*adjustedCoreRate(w) < 1.
```

The prefactor has no representation cutoff, ambient volume or separation
parameter. All coupling guards are explicit; the existing nome `1/1024`
satisfies them. The distance is between the two supplied probe-carrier
roots. Both observable bounds and carrier sizes remain in the prefactor.

The normalized cutoff/thermodynamic passage, reflected-time instances
and strict completed form bound requested at this stage are now proved
in the six modules above. The subsequent results above supply the unit
fixed-space theorem and a nonzero excitation on this restricted completion;
the full physical realization and continuum/QFT/all-group Clay remain open.

Five new modules: 16+18+21+6+5=66 exactly matched focused axiom gates
within `{propext, Quot.sound}`; final error/warning-free logs and fresh
own/direct-import artifacts. One monitored worker, mandatory 20 GiB ceiling.
No full build/audit/guard/progress run; root imports updated but not rebuilt.

**Preceding result: a contractive completed ORIGINAL time semigroup and positive two-step transfer.**
[`timeNorm_midpoint` and `timeNorm_le_anchor`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeContraction.lean)
derive, rather than assume, `||T^n p||^2 <= ||p||^2`. Reflection positivity
gives `2*a(n) <= a(0)+a(2*n)`; the existing original polynomial cap is
independent of lag. The new
[`bounded_midpointDoubling_leEv_anchor`](lean/YMGap/Continuum/BoundedMidpointDoublingEventual.lean)
handles eventual bounds by synchronizing only a finite doubling orbit.
`distSq_translate` gives exact nonexpansiveness on original presentations.

[`completedTime`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean)
extends that actual map to the EXISTING Cauchy completion without changing
any supplied Cauchy modulus. It preserves composition, rational and supplied
constructive-real scalar multiplication, symmetry, the unit and the unit
complement. Its norm and squared distance are nonincreasing at every lag.
`twoStepTransfer` is positive and symmetric, fixes the original nonzero unit,
and is the actual two-step geometric time map, not a heat-bath generator.
`timeCovariance_operator_sum` pins its time-semigroup moments to the
already-constructed ORIGINAL connected-correlation limits.

The subsequent results above supply the strict time-separation estimate,
completed gap, unit fixed-space theorem and nonzero thermodynamic excitation.
The norm bound of this earlier module is **one**, not itself a strict gap.
The full required observable algebra and quotient-level completeness, continuum
scaling, QFT reconstruction and all-group Clay remain open. Nome `w=1/1024` and
lattice spacing remain fixed; no coupling-uniform or continuum claim follows.

Three new modules: 1+10+35=46 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning-free logs and fresh own/direct-import
artifacts. One monitored worker with the mandatory 20 GiB ceiling. No full
build/audit/guard/progress run; root imports updated but not rebuilt.

**Preceding result: original time invariance and a well-defined dense OS time semigroup.**
The [shifted probe](lean/YMGap/Continuum/BF4ExactSlabOffsetProbeCarrier.lean)
and [spacetime expression](lean/YMGap/Continuum/BF4ExactSlabOffsetSpacetimeExpression.lean)
supply every observable/geometric premise of the original comparison.
[`difference_bound`](lean/YMGap/Continuum/BF4ExactSlabOffsetSpacetimeDecay.lean)
retains the original support size; its shrinking coefficient is independent
of outer padding and time offset.
[`meanLimit_embed`](lean/YMGap/Continuum/BF4ExactSlabSpacetimeTimeInvariance.lean)
proves equality of the two existing ORIGINAL thermodynamic limits, using
the original expression's explicit volume modulus.

A [literal reflected-product identity](lean/YMGap/Continuum/BF4ExactSlabSpacetimeReflectedTimeGeometry.lean)
then gives [`one_step_balance`, `time_sum`, `timeCovariance_sum`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeBalance.lean)
on the SAME completed-state family: its two-time covariance equals its
sum-lag row, and the original mean is time invariant.
[`timeState_of_zero`, `denseTime`, `denseTime_completed_pin`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicDenseTime.lean)
prove null preservation and construct the actual time semigroup on the
EXISTING original OS null quotient. It is linear and symmetric, fixes the
unit and preserves the original mean. No contraction premise is used.

The norm-relative bound and completed extension were open at this checkpoint;
the latest result above closes those two steps at the same fixed nome and
spacing. A strict gap and the larger physical/continuum obligations remain open.

Seven new modules: 64 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final logs error/warning free and own/direct-import
artifacts fresh. The safe-build procedure used one monitored worker and the
mandatory 20 GiB ceiling. No new hole, analytic premise, raised limit or
canonical frontier change. Root imports updated, not rebuilt; no full
build/audit/guard/progress run. GitHub Actions remains disabled.

**Preceding result: off-center comparisons retain the original interacting law and its normalization.**
[`Placement.embedding`, `Placement.haar`](lean/YMGap/Continuum/BF4ExactSlabOffsetHaarEmbedding.lean)
construct the actual link map for every allowed time offset.
[`interiorMoment_small`, `interiorPartition_small`](lean/YMGap/Continuum/BF4ExactSlabOffsetInteriorHaarPin.lean)
identify the embedded interior integral with the original smaller slab,
at every cutoff and at its explicit-modulus limit.
The [exterior distance floor](lean/YMGap/Continuum/BF4ExactSlabOffsetExteriorSeparation.lean)
feeds the existing core sum, giving [off-center boundary decay](lean/YMGap/Continuum/BF4ExactSlabOffsetBoundaryDecay.lean).
[`protected_expectationDifference_bound`](lean/YMGap/Continuum/BF4ExactSlabOffsetExpectationComparison.lean)
cancels the two SAME original partition factors after cutoff removal.
The resulting bound names the coupling, observable interval, probe and
margin; its coefficient does not depend on the outer padding or time offset.
It is boundary sensitivity, **not** time decay or a spectral gap.

**Next at that checkpoint:** construct the shifted-expression inputs to this estimate and
compare their original thermodynamic limits to establish time invariance,
then reflected one-step balance. These identities are not assumed or proved
by the new comparison theorem. Completed time-operator descent, strict gap,
physical vacuum and continuum/QFT/all-group Clay remain open.

Seven new modules: 93 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final logs error/warning free and own/direct-import
artifacts fresh. Checks used one monitored worker with the mandatory 20 GiB
ceiling. No new hole, analytic premise, raised limit or canonical frontier
change. Root imports updated, not rebuilt; no full build/audit/guard/progress
run. GitHub Actions remains disabled.

**Preceding result: actual translated states and their original two-time correlations are constructed.**
The [literal time geometry](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeGeometry.lean)
proves that outward physical lags add and commute with changing the base
box. [Original observable comparisons](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeAlgebra.lean)
retain sums, products, rational scales and arbitrary common bulk padding,
with explicit comparison thresholds.

[`timeState`, `centeredTimeState`, `timeState_norm_le`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeStates.lean)
construct translated states in the SAME original completion. Their squared
norms have the original polynomial-size ceiling, independent of time lag.
This is **not** a norm-relative contraction or a strict gap.
[`timeCovariance_bulk`, `timeCovarianceRepresentative`, `timeCovariance_error_le`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeCorrelations.lean)
identify their completed centered pairing with the ORIGINAL finite-slab
covariance limit. The construction computes common padding `max(s,t)` and
retains the CReal/Cauchy and volume-error moduli. Both lags remain explicit;
the geometric estimate controls receding boundaries, not time decay.

**Next at that checkpoint:** prove the original reflected one-step time-balance identity,
then establish representative independence and norm-controlled extension
to a completed time operator. The current time family takes finite
presentations, not arbitrary completed states. The existing dyadic gap
engine already assumes contraction and cannot be used to prove that premise.
Nonzero thermodynamic excitations, physical vacuum, strict gap, full
observables/completeness and continuum/QFT/all-group Clay remain open.
Nome `w=1/1024` and lattice spacing remain fixed.

Four new modules: 65 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final logs error/warning free, own/direct-import
artifacts fresh. The safe-build skill kept checks to one monitored worker
and the mandatory 20 GiB ceiling. No new hole, analytic premise, raised
limit or canonical frontier change. No full build/audit/guard/progress run;
root imports updated, not rebuilt.

**Preceding result: original thermodynamic connected covariance is realized by centered completed-state pairings.**
[`realScalarCauchy`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicRealScalarCauchy.lean)
constructs scalar-multiplied original streams using explicit scalar and
vector moduli. [`completedRealSmul`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedRealScalar.lean)
descends to the SAME carrier, independently of representatives and supplied
scalar moduli. [Arithmetic and distance-scaling laws](lean/YMGap/Continuum/BF4ExactSlabThermodynamicRealScalarAlgebra.lean)
hold for these modulus-bearing scalars; no arbitrary quotient modulus is
selected.

[`unitProjection`, `unitCoefficientCauchy`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicUnitProjection.lean)
construct the projection onto the SAME original unit using its actual
mixed-pairing coefficient and modulus. It is self-adjoint, idempotent,
linear and norm-contractive.
[`center`, `orthogonal_decomposition_inner`, `centered_inner_sameBase`, `centeredPairing_error_le`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCenteredCompletion.lean)
construct exact unit centering, prove Pythagoras and identify its completed
pairing with the previously constructed ORIGINAL covariance limit.
The actual centered pairing retains CReal/QCauchy data and the same
explicit volume-error modulus. That estimate concerns receding boundaries,
**not physical-time decay**.

[`approximateCentered`, `rowLimit_centeredRows`, `complementRowLimit`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCenteredDensity.lean)
preserve approximation and represented-row convergence rates in the
unit complement, returning the required states and presentations as data.

**Next at that checkpoint:** physical time translation and state homogeneity, with original-law
compatibility, OS norm control and stationary-unit identification. The unit
complement is not yet proved nontrivial. Nonzero thermodynamic excitations,
strict gap, full required observables, full quotient-level completeness,
spacing/continuum/QFT and all-group Clay remain open. Coupling `w=1/1024`
and lattice spacing remain fixed; a norm-one unit is not a proved vacuum.

Six new modules: 6+13+6+20+33+12=90 exactly matched focused axiom gates
within `{propext, Quot.sound}`, final error/warning free;
source/direct-import artifacts fresh. The safe-build skill kept checks to
one monitored worker and the mandatory 20 GiB ceiling. No new hole,
analytic premise, raised limit or canonical frontier change; no full
build/audit/guard/progress run. Root imports updated, not rebuilt.

**Preceding result: the thermodynamic completion has compatible rational linear geometry and explicit represented-row limits.**
[`addition`, `scalarContinuous`, `completedAdd`, `completedSmul`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletionLinear.lean)
construct the operations with explicit continuity moduli, prove their
rational linear laws, and identify them with the existing observable and
OS quotient operations. [Completed bilinearity](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedBilinear.lean)
follows from the SAME original pairing limits.

[`completedDist`, `completedDist_zero_iff`, `completedDist_embedObservable`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedGeometry.lean)
give the actual original squared-distance geometry, including its triangle
law and real-representative modulus.
[`approximationData`, `approximant_bound`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedApproximation.lean)
return nearby original presentations and their certified distance errors.

[`CauchyRows`, `rowLimit`, `rowLimit_bound`, `rowLimit_independent`, `rowLimit_presentationRows`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCauchyRows.lean)
construct a unique limit for a family with **supplied row representatives
and outer Cauchy modulus**. Its convergence rate is `M(epsilon/16)`;
the diagonal Cauchy rate is `max(M(epsilon/16),(epsilon/16).den)`.
Changing supplied representatives does not change the limit, and rows of
original presentations recover the existing completion class.

**Next:** modulus-bearing real-scalar action and unit-orthogonal
projection/covariance realization. Full quotient-level completeness
remains open: the row construction does not select representatives for
arbitrary quotient-valued sequences. Physical time, stationary vacuum,
nonzero excitations, strict gap, full gauge observables,
spacing/continuum/QFT and all-group Clay also remain open. Coupling
`w=1/1024` and lattice spacing are still fixed.

Five new modules: 32+8+20+7+16=83 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source/direct-import
artifacts fresh. The safe-build skill kept checks to one monitored worker
and the mandatory 20 GiB ceiling. No new hole, analytic premise, raised
limit or canonical frontier change; no full build/audit/guard/progress
run. Root imports updated, not rebuilt.

**Preceding result: the SAME original thermodynamic pairing extends to Cauchy classes and is positive definite.**
[`pairing_close`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPairingContinuity.lean)
combines sharp Cauchy--Schwarz with the bilinear difference identity.
The explicit tolerance is `epsilon^2/(8*(B+1))`, requiring no square root.
[`diagonal_le_ceiling`, `normCeiling`, `pairRate`, `representativeInner`, `representativeInnerCauchy`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPairingLimit.lean)
construct the pairing limit and its moduli: the original size cap bounds
one Cauchy anchor, then continuity supplies the outer rate and the original
presented forms supply inner regularity. No boundedness or convergence
premise is added.

[`completedInner`, `completedInner_embedObservable`, `completedInner_embedOSQuotient`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedInner.lean)
descend that limit to the existing completion and identify it with the
original OS pairing on embedded states. It is symmetric and positive,
retains the norm-one unit and original mean coefficient, and satisfies
sharp Cauchy--Schwarz.
[`closeZeroOfInnerZero`, `completedInner_posdef`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedPosdef.lean)
use the same explicit rate to prove that zero norm is exactly the zero
completed state. No representatives are selected from quotient classes.

**Next:** completed linear operations and laws, bilinearity and the
appropriate constructive completeness theorem on this SAME carrier.
A positive-definite pairing alone is not a completed Hilbert structure.
Physical time, stationary vacuum, nonzero excitations, strict gap, full
gauge observables, spacing/continuum/QFT and all-group Clay remain open.
The coupling `w=1/1024` and lattice spacing remain fixed.

Four new modules: 6+22+17+8=53 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source/direct-import
artifacts fresh. The safe-build skill kept checks to one monitored worker
and the mandatory 20 GiB ceiling. No new hole, analytic premise, raised
limit or canonical frontier change; no full build/audit/guard/progress
run. Root imports updated, not rebuilt.

**Preceding result: one original thermodynamic OS quotient embeds injectively into an explicit-modulus completion carrier.**
[`form_lower_congr`, `basedForm_compatible`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCommonForm.lean)
give the compatibility argument: lower-observable Haar equality preserves
one slot, symmetry handles the other, and two base presentations are
compared as tails at the same absolute volume. No new analytic
reflection-compatibility assumption is added; volume and real-representative
moduli remain explicit.

[`presentedForm_same`, `pairing`, `pairingRepresentative`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicReflectedObservable.lean)
descend the original form to the **existing semantic observable quotient**.
The relation is equality under every original Haar insertion, independent
of the interacting mean. Presented pairings retain real/Cauchy data without
choosing representatives from quotient classes.
[`pairing_cauchySchwarz`, `pairing_unit_left_value`, `connectedPairing_sameBase`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicReflectedBilinear.lean)
retain rational bilinearity, positivity, the same mean functional, and the
actual connected covariance on this common carrier.

[`null_iff_pairing`, `Carrier`, `inner_posdef`, `unit_norm_one`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicNullQuotient.lean)
construct the positive-definite OS null quotient. Addition and rational
scaling descend; multiplication or an observable action is **not** assumed
to descend. The unit has norm one, and its coefficient is the original mean.
[`distSqCauchy`, `seminorm`, `Completion`, `embedOSQuotient_injective`, `completedUnit_ne_zero`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicSeminormCompletion.lean)
construct the squared seminorm and explicit-modulus completion carrier,
with an injective embedding of that OS quotient and a nonzero unit.

**Next:** extend the SAME inner product to Cauchy classes, with explicit
pairing-limit data. The completion carrier is not yet a completed Hilbert
structure or a proof of full quotient-level completeness. Physical time
action, stationary vacuum, nonzero excitations, strict gap, full gauge
observables, spacing/continuum/QFT and all-group Clay remain open. This
increment retains fixed `w=1/1024`, fixed spacing and plaquette observables.

Five new modules: 17+13+20+31+27=108 exactly matched focused axiom gates
within `{propext, Quot.sound}`, final error/warning free;
source/direct-import artifacts fresh. The safe-build skill kept checks to
one monitored worker and the mandatory 20 GiB ceiling. No new hole,
analytic premise, raised limit or canonical frontier change; no full
build/audit/guard/progress run. Root imports updated, not rebuilt.

**Preceding result: the original reflected form and connected covariance reach thermodynamic volume, with explicit error moduli.**
[`SpacetimeExpression`, `reflectedProduct_pin`](lean/YMGap/Continuum/BF4ExactSlabSpacetimeExpression.lean)
extend the finite expression carrier to all physical faces of a base slab.
The evaluated reflected product is literally the existing upper/lower
product, with constructed bounds, locality and original embedding pins.
[`difference_bound`](lean/YMGap/Continuum/BF4ExactSlabSpacetimeExpectationDecay.lean)
therefore applies the original normalized inter-volume comparison to it.
[`meanLimit`, `volumeModulus`, `lower_limit_pin`](lean/YMGap/Continuum/BF4ExactSlabSpacetimeThermodynamicLimit.lean)
construct all-face limits and pin their lower restriction to the previous
mean. The volume modulus is `M(base)+geoOuterModulus(A(e),epsilon)`;
inner and limit-representative Cauchy moduli are also data.

[`form_converges`, `form_nonnegative`, `form_cauchySchwarz`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicReflectedForm.lean)
pass the **original finite-slab OS forms** to the constructed limit.
Symmetry, rational bilinearity, unit normalization and the radical-zero law
hold; `form_unit_left_mean` pins the unit row to the same lower mean.
[`covariance_converges`, `covarianceSequence_centeredPairing`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicConnectedCovariance.lean)
identify the connected limit with the actual prior centered finite-volume
pairings. Its diagonal is positive and it satisfies sharp Cauchy–Schwarz.

[`covariance_geometric_bound`, `covarianceVolumeModulus`, `covariance_error_le`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicCovarianceRate.lean)
give `|Cov_limit-Cov_m| <= A_cov*s^(m+1-M)` and a computed volume modulus.
Here `A_cov = A_reflected + B_e*A_f + B_f*A_e`, with the existing original
mean caps `B_e=bound(e)+1`. This is **receding-boundary error**, not decay
with physical time separation. The constructed limits are at fixed
`w=1/1024` and fixed spacing, for plaquette-generated expressions.

At that checkpoint, descent across base presentations and the thermodynamic
OS quotient/completion were next. Full spacetime-state compatibility, physical
stationary vacuum, strict completed gap, spacing/continuum/QFT control and
the all-group Clay target remain open. A positive form is not a strict gap.

Six new modules: 16+5+21+21+9+10=82 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source/direct-import
artifacts fresh. The safe-build skill kept checks to one monitored worker
and the mandatory 20 GiB ceiling. No new hole, analytic premise, raised
limit or canonical frontier change; no full build/audit/guard/progress run.
Root imports updated, not rebuilt.

**Preceding result: one presentation-independent positive thermodynamic functional on the lower plaquette algebra.**
[`shiftedExpression_enlarge`, `meanLimit_enlarge`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicBaseCompatibility.lean)
prove the short compatibility argument: zero-lag enlargement of a base box
gives literally a tail of the SAME original expectation sequence, so the
constructed limits agree.

[`SameObservable`, `meanLimit_same`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicPresentation.lean)
handle common-volume semantic equality. The comparison threshold is data;
equality is under **every polynomial insertion on the original Haar carrier**
at sufficiently large common volumes. It does not mention the interacting
mean and is not defined as equality of means. Computed common-base addition,
multiplication and scaling preserve this relation.

[`Observable`, `value`](lean/YMGap/Continuum/BF4ExactSlabThermodynamicLowerFunctional.lean)
descend to the semantic quotient. `value_unit`, `value_add`, `value_smul`,
and `value_square_nonnegative` prove normalization, rational linearity and
ordinary-square positivity. `unit_ne_zero` proves nontriviality.
`valueRepresentative` returns a presented value's constructive real,
QCauchy modulus and exact quotient pin, without choosing a representative
from an arbitrary quotient class.
[`qadd_assoc`, `qmul_assoc`, `qmul_add` and scalar laws](lean/YMGap/Continuum/BF4ExactSlabThermodynamicLowerAlgebra.lean)
prove the actual commutative rational algebra laws for these operations.

At that checkpoint, full-spacetime/reflected thermodynamic moments and the
required state/time/reflection properties were next. That functional
is on the **lower plaquette-generated algebra**, at fixed `w=1/1024` and
fixed spacing. It is not a full spacetime state, an OS form, a stationary
vacuum, a physical transfer/gap, or continuum QFT. All-group Clay remains open.

Four new modules: 6+28+18+16=68 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source/direct-import
artifacts fresh. The safe-build skill kept checks to one monitored worker
and the mandatory 20 GiB ceiling. No new hole, analytic premise, raised
limit or canonical frontier change; no full build/audit/guard/progress run.
Root imports updated, not rebuilt.

**Preceding result: constructed thermodynamic limits for finite plaquette expressions, including mixed products.**
[`boxAnimal`](lean/YMGap/Continuum/Z4FiniteBoxConnectedAnimal.lean) constructs
shared-link paths throughout the literal six-plane box.
[`shiftedBoxProbe`](lean/YMGap/Continuum/BF4ExactSlabShiftedProbeCarrier.lean)
translates those paths and preserves the carrier size; preimages are computed
by coordinate subtraction. No connected-carrier hypothesis remains for a
finite expression.

[`shiftedExpressionBound`, `shiftedExpression_local`, `shiftedExpression_image`](lean/YMGap/Continuum/BF4ExactSlabShiftedPlaquetteExpression.lean)
construct bounds, locality and the SAME original Haar embedding for the
existing expression language's products, sums and signed rational scales.
[`expressionMean_difference_bound`](lean/YMGap/Continuum/BF4ExactSlabExpressionExpectationDecay.lean)
gives `|E_(m+p)(e)-E_m(e)| <= A(w,base,e)*s(w)^(m+1-M(base))` for any
outer padding `p`. Here `n=centralExtent(base)+1`, `M=6*n^4`, the probe
has `24*n^4` link occurrences, and its counting prefactor is `2^M*625^M`.
The amplitude explicitly retains support and coupling dependence; natural
subtraction truncates the exponent at zero.

[`meanLimit`](lean/YMGap/Continuum/BF4ExactSlabExpressionThermodynamicLimit.lean)
constructs the limit at `w=1/1024`. Its explicit volume modulus is
`M(base)+geoOuterModulus(A(e),epsilon)`; per-volume and limit-representative
moduli are also returned. The actual geometric error bound survives.
`meanLimit_one`, `meanLimit_add`, `meanLimit_smul`, and
`meanLimit_square_nonnegative` prove normalization, linearity and ordinary
square positivity. No multiplicativity is claimed: mixed-product limits
are interacting moments.

**Next at that checkpoint:** compatibility across presentations/base boxes of the same observable,
then the required state/time/reflection properties. These expression-level
limits are not yet a full physical state, transfer/vacuum/gap, or continuum
QFT. The result is fixed-coupling/fixed-spacing, not beta/spacing-uniform.
The all-group Clay target remains open.

Five new modules: 13+12+6+13+19=63 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free, source/direct-import
artifacts fresh. The safe-build skill kept verification to one monitored
worker and the mandatory 20 GiB ceiling. No new hole, analytic premise,
raised limit or canonical frontier change; no full build/audit/guard/progress
run. Root imports updated, not rebuilt.

**Preceding result: normalized comparison and a constructed thermodynamic limit for single-plaquette character means.**
[`expectationDifference_bound`](lean/YMGap/Continuum/BF4ExactSlabBoundaryLimitNormalization.lean)
passes the common-cutoff determinant estimate to the original moment limits
and cancels the SAME two partition functions using their proved reciprocals.
No volume-dependent reciprocal ceiling enters the resulting bound.
`boundaryNumerator_prefix` and `expectationDifference_bound_of_prefix`
preserve the literal quaternion-Haar observable pin.

[`characterMean_difference_bound`](lean/YMGap/Continuum/BF4ExactSlabInnerMarginExpectationDecay.lean)
constructs the carrier, locality, interval certificate and embedding pin
for the actual character of a translated plaquette holonomy. It proves
`|E_(m+p)(chi_spin)-E_m(chi_spin)| <= A_spin(w)*s(w)^m` for ANY outer
padding `p`, where `A_spin(w)=4*16^spin*singlePlaquetteAmplitude(w)`.
Coupling guards remain explicit; all are discharged at `w=1/1024`.
The amplitude and rate do not depend on base size, position or padding.

[`meanLimit`](lean/YMGap/Continuum/BF4ExactSlabCharacterThermodynamicLimit.lean)
constructs the thermodynamic limit of these SAME normalized means at that
fixed coupling. `volumeModulus` and `innerModulus` are returned as data;
`meanLimitCauchy` also supplies the returned representative's modulus.
The existing completeness diagonal is reused, with no choice or new
analytic convergence input. `meanLimit_geometric_bound` retains
`|E_infinity(chi_spin)-E_m(chi_spin)| <= A_spin*s^m`;
`meanLimit_error_le` applies the explicit volume modulus to the actual limit.
The proved `s<=1/2` envelope is used for the modulus, not substituted for
the original geometric error rate.

**Next at that checkpoint:** construct finite-product/mixed-observable thermodynamic limits and
their algebraic compatibility. A limit for each single-plaquette character
is not yet a full thermodynamic state, much less a physical transfer, vacuum,
spectral gap or continuum QFT. This is fixed-coupling/fixed-spacing progress;
beta/spacing-uniform control and the all-group Clay target remain open.

Three new modules: 7+8+18=33 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source/direct-import
artifacts fresh. The safe-build skill kept checks to one monitored worker
and the mandatory 20 GiB ceiling. No new hole, analytic premise, raised
limit or canonical frontier change; no full build/audit/guard/progress run.
Root imports updated, not rebuilt.

**Preceding result: a shrinking inner-margin coefficient for the original boundary comparison.**
[`shifted_base_exterior_linf_floor`](lean/YMGap/Continuum/BF4ExactSlabEmbeddedExteriorSeparation.lean)
proves separation from the ORIGINAL embedded smaller-slab exterior. The
smaller slab has half-size `base+margin`; arbitrary outer `padding` embeds it
into the comparison slab. A fixed physical base face is shifted by
`margin+padding`. Every original exterior face is at distance at least
`margin`. The embedded-face preimage is computed, not assumed.

[`protected_root_core_size_floor`](lean/YMGap/Continuum/BF4ExactSlabCoreDistanceFloor.lean)
uses the existing animal decoder to force `|core| >= margin+1-M` (natural
subtraction), where `M` is the connected carrier's size. For the constructed
single-plaquette carrier this is `|core| >= margin`.

[`singlePlaquette_boundary_geometric_bound`](lean/YMGap/Continuum/BF4ExactSlabInnerMarginBoundaryDecay.lean)
substitutes that size floor into the original weighted sum, giving
`|D_K| <= 2*c*amplitude(w)*s(w)^margin*Z_full,K*Z_inside,K` at every cutoff.
Here `amplitude(w)=A(w,4)*1250/(1-s(w))` and `s(w)=625*rho(w)` are explicit
rational data, with no cutoff, base-size, position, margin or outer-padding
parameter. `existingNome_singlePlaquette_boundary_bound` supplies all
coupling guards at `w=1/1024`, where `0<s<1`. The observable's interval
bound `c` and literal single-plaquette locality remain explicit hypotheses.

**Parameter correction:** decay is in the INNER margin, growing the smaller
slab around a fixed probe, uniformly in further OUTER padding. Increasing
outer padding at fixed smaller slab does not move that slab's boundary
away from its probe. This is not a beta- or spacing-uniform estimate.

**Next at that checkpoint:** finite normalization and transport to the existing normalized
cutoff-limit expectations. The theorem still multiplies by the two original
unit moments: a shrinking comparison coefficient does not assert that the
raw determinant tends to zero. Thermodynamic Cauchy data, general probe
construction, physical transfer/vacuum, strict physical gap and continuum/
QFT/all-group Clay remain open. Normalization is now proved directly at the
cutoff limits, and single-plaquette character thermodynamic limits are
constructed above; no intermediate finite reciprocal construction was needed.

Three new modules: 13+5+9=27 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free, source/direct-import
artifacts fresh. The safe-build skill kept verification to one monitored
worker and the mandatory 20 GiB ceiling. No new hole, analytic premise,
raised limit or canonical frontier change; no full build/audit/guard/progress
run. Root imports updated, not rebuilt.

**Preceding result: the original weighted core sum has a volume-independent budget.**
[`size_sum_bound`](lean/YMGap/Continuum/FiniteSizeGeometricSum.lean)
groups the finite source by its actual sizes. A count `count_n<=C*D^n`
and weights `rate^n` give the explicit rational budget
`C*(D*rate)^d/(1-D*rate)` when every size is at least `d` and `D*rate<1`.
The finite upper size bound disappears; no infinite rearrangement is used.

[`existingNome_entropyRate`](lean/YMGap/Continuum/BF4ExactSlabSummableCoreRate.lean)
checks **the combined rate** `s(w)=625*rho(w)<1` at the existing `w=1/1024`
pilot. This is coupling-specific, not beta- or spacing-uniform.

[`geometricCoreSum_uniform_bound`](lean/YMGap/Continuum/BF4ExactSlabUniformCoreBudget.lean)
applies the actual core count, proving `sum_active rho^|core| <= C*s/(1-s)`.
The size-one floor is proved from the exterior-face witness.
`boundaryNumerator_uniform_bound` then gives the ORIGINAL
`|D_K| <= 2*c*A(w,ell)*C(probe)*s(w)/(1-s(w))*Z_full,K*Z_inside,K`.
`existingNome_boundary_bound` supplies all coupling guards at the stated
pilot. The coefficient has no extent, volume or cutoff parameter; its probe
and coupling dependence remains explicit. General connected probe carriers
are supplied geometric data; the singleton carrier is already constructed.

**Next at that checkpoint:** prove a distance-growing lower bound on core size. The proved
`boundaryNumerator_tail_bound` already carries that size bound as the
exponent `d`; no such distance estimate is assumed in the size-one result.
Normalized cutoff-limit transport, padding convergence, physical transfer/
vacuum, strict physical gap and continuum/QFT/all-group Clay remain open.
A bounded boundary response is not a boundary-decay theorem. The inner-margin
size floor and shrinking coefficient are now proved above at the stated scope.

Three new modules: 8+2+9=19 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free, with fresh source and
direct-import artifacts. Safe-build verification used one monitored worker
and the mandatory 20 GiB ceiling. No new hole, analytic premise or raised
limit; no full build/audit/guard/progress run. Root imports updated, not rebuilt.

**Preceding result: a faithful count of the original probe-rooted cores.**
[`augmentedAnimal`](lean/YMGap/Continuum/BF4ExactSlabProbeCarrierAnimal.lean)
replaces the virtual probe root by an explicit connected plaquette carrier.
For a carrier of `M` faces and a core of `n` faces, it constructs a genuine
4D plaquette animal with at most `M+n` faces. A singleton carrier covering
the four links of one plaquette is constructed, without supplied connectivity.

[`decodeCore_encode`](lean/YMGap/Continuum/BF4ExactSlabProbeCoreCode.lean)
proves that the padded tour **plus the core's intersection with the carrier**
recovers the original face identifiers in their original ambient order.
The mask matters: augmentation alone loses that intersection information.
The finite code carrier has length `2^M * 625^(M+n)`.

[`activeAtSize_length_le`](lean/YMGap/Continuum/BF4ExactSlabActiveCoreCount.lean)
applies this injection to the EXISTING active-core list and proves its
size-`n` count is at most `C(probe)*625^n`, with `C=2^M*625^M`.
`singleton_activeAtSize_length_le` gives the concrete prefactor `1250`.
For a fixed carrier, neither volume, cutoff, coupling nor the interior test
enters this count. General probe carriers remain explicit geometric data.

The weighted sum and combined-rate guard left open at that checkpoint are
now proved above. The distance-growing size cost is now proved for protected
roots, including the shifted single-plaquette instance. Normalized
cutoff-limit transport, padding limits,
physical transfer/vacuum, a strict physical gap and continuum/QFT/all-group
Clay remain open.

Three new modules: 14+11+10=35 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free, with fresh source and
direct-import artifacts. One monitored worker, mandatory 20 GiB ceiling;
no new hole, analytic premise, raised limit or full-tree build/audit.
The safe-build discipline kept verification targeted; root imports were
updated but the root was not rebuilt.

**Preceding result: the local collar cost is absorbed into a geometric rate.**
[`collarIds_length_le`](lean/YMGap/Continuum/BF4ExactSlabCollarDegreeBound.lean)
uses the existing six-plaquettes-per-link enumeration and physical face-ID
injectivity to prove `|collar| <= 6*(ell+4*n)`, where `ell` is the number of
probe links and `n` the number of core faces. Shared links are returned as
explicit witnesses; no independence assumption is introduced.

[`normalizedCoreWeight_geometric_bound`](lean/YMGap/Continuum/BF4ExactSlabCollarAdjustedRate.lean)
then bounds the existing normalized core weight by `A(w,ell)*rho(w)^n`, with
`r(w)=1/(1-delta(w))`, `A(w,ell)=r(w)^(12*ell)` and
`rho(w)=(2*delta(w)+delta(w)^2)*r(w)^48`. The rate depends on the coupling,
not the slab volume, cutoff or probe size. The probe size remains in `A`.

[`boundaryNumerator_geometric_bound`](lean/YMGap/Continuum/BF4ExactSlabGeometricBoundaryBudget.lean)
controls the ORIGINAL `D_K` by
`2*c*A(w,ell)*sum_active rho(w)^|core|*Z_full,K*Z_inside,K`.
At the existing `w=1/1024` pilot, `0<rho<1` is kernel checked using small
power blocks. The actual rooted-core sum is **not yet bounded uniformly**.

The formerly missing virtual-root/ordinary-animal bridge, faithful size
count, weighted sum and protected-root exterior size floor are now proved
above. Normalized limit transport,
volume-uniform decay, physical transfer/vacuum, a strict physical gap and
the continuum/QFT/all-group Clay target remain open. Bounds retain
`0<=w<=1`, `heatRatio(w)<=1/2` and `delta(w)<1`.

Three modules, 8+10+7=25 exactly matched focused gates within
`{propext, Quot.sound}`, final error/warning free; source and direct-import
artifacts fresh. One monitored worker, mandatory 20 GiB ceiling; no new
holes, analytic assumptions, oracle or raised limits. No full build/audit/
guard/progress run; root imports updated but not rebuilt.

**Preceding result: an explicit finite boundary budget for the ORIGINAL action.**
[`mixedCoefficient_selective_pin` and `mixedCoefficient_bound`](lean/YMGap/Continuum/BF4ExactSlabMixedCoefficientBound.lean)
identify and bound the NEW mixed coefficient by an exact two-slot insertion
recursion. Each exterior face costs `delta(w)=128*w^3`; each interior face
costs `kappa(w)=2*delta(w)+delta(w)^2`. The bound is `2*c*W(core)`, where
`c` is the supplied polynomial interval cap and `W` is the computed product
of those respective costs. This is a theorem about the original signed
Haar moments, not the auxiliary positive law.

[`mixedFamily_weight_bound`](lean/YMGap/Continuum/BF4ExactSlabMixedBoundedFamilies.lean)
combines that estimate with the matching partition comparison.
[`finiteBoundaryBudget` and `boundaryNumerator_budget_bound`](lean/YMGap/Continuum/BF4ExactSlabMixedFiniteBoundaryBudget.lean)
sum `W(core)/R(collar)` over the actual probe-to-exterior cores and prove
`|D_K| <= 2*c*B*Z_full,K*Z_inside,K`. The positive reciprocal of each local
collar floor is constructed. `B` contains no representation cutoff `K`;
it explicitly depends on the coupling, slab, probe links and interior test.
This is a **denominator-cleared finite bound**, not yet volume-uniform decay.

The collar-size part of that checkpoint is now closed above. Rooted-core
counts, probe-to-exterior path length and quantitative transport through
the original normalized limits remain open. Bounds retain `0<=w<=1` and
`heatRatio(w)<=1/2`; the reciprocal budget requires the explicit strict
guard `delta(w)<1`. No uniform boundary decay, physical gap, continuum/QFT
construction or all-group Clay closure follows yet.

Four new modules, 15+9+3+8=35 exactly matched focused gates within
`{propext, Quot.sound}`, final error/warning free; source and direct-import
artifact freshness checked. Two older dependency artifacts were refreshed
by focused checks without source changes; `Sqrt` emitted three existing
unused-code warnings. Checks used one monitored worker and the mandatory
20 GiB ceiling. No new
holes, analytic assumptions, oracle or raised limits. No full build/audit/
guard/progress run; the root import list was updated but not rebuilt.

**Preceding result: a probe-only mixed-action expansion with matching partition factors.**
[`boundary_mixedNumerator`](lean/YMGap/Continuum/BF4ExactSlabMixedAction.lean)
identifies the EXISTING boundary determinant with a face functional whose
first action uses every selected face and whose second uses only interior
faces. Its all-interior coefficients vanish exactly.
[`mixedFamily_resummed`](lean/YMGap/Continuum/BF4ExactSlabMixedRootedResummation.lean)
resums interior AND exterior spectators into `Z_detached * Z_inside-detached`.
The root now contains only the probe support, not selected exterior faces.

[`boundary_probe_rooted_expansion` and `boundary_anchor_path`](lean/YMGap/Continuum/BF4ExactSlabProbeRootedBoundaryExpansion.lean)
give a single exact sum for the original D and return an explicit path from
the probe root to an actual exterior face for every retained core.
[`boundary_mixedFamily_cleared_bound`](lean/YMGap/Continuum/BF4ExactSlabMixedRelativePartition.lean)
proves `R*|actual family| <= |mixed coefficient|*F(1)*I(1)` using the two
ORIGINAL unit moments in the boundary determinant, at the same cutoff.
The removal cost R is `(1-delta)^|collar| * (1-delta)^|inside collar|`, strictly
positive at the existing `w=1/1024` pilot for every finite collar.

The mixed-coefficient obligation at that checkpoint is discharged by the
new selective-insertion theorem above; collar/path counts and normalized
summability remain open. The previous two-probe coefficient estimate is
not applied to this different finite difference. Exact identities
need no small-nome guard; the partition bound retains `0<=w<=1`,
`heatRatio(w)<=1/2`, and `delta(w)<=1`. No uniform boundary decay, physical
gap, continuum/QFT construction or all-group Clay closure follows yet.

Five modules, 14+3+6+8+11=42 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source and direct-import
artifact freshness checked. Monitored one-worker 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: the actual rooted families are fully resummed.**
[`core_merge` and `spectators_merge`](lean/YMGap/Continuum/BF4ExactSlabRootedSelectionStability.lean)
prove that adding any detached selection preserves a fixed core and that
decoding recovers the added spectators in ambient order.
[`family_spectators_perm` and `spectatorWeight_pin`](lean/YMGap/Continuum/BF4ExactSlabRootedFamilyResummation.lean)
prove the full bijection: the ACTUAL signed spectator weight is precisely the
original partition square on all detached ambient faces. Non-fixed keys
have empty fibers and are removed by a computed test.

[`boundaryNumerator_resummed_expansion`](lean/YMGap/Continuum/BF4ExactSlabBoundaryResummedFamilies.lean)
now expresses the EXISTING full boundary D as a double sum of the previously
bounded `boundarySpectatorFamily` objects. `boundaryRootedFamily_cleared_bound`
transfers that estimate to the actual computed fiber. The exact identities
require no small-nome restriction; the estimate retains its previous heat
guards and the original INTERIOR partition square.

The preceding root includes the selected exterior
support, and `Z_interior^2` is not the mixed boundary denominator
`Z_large*Z_small`. The result above supplies a probe-only mixed-action
expansion, matched partition comparison and a bound on its new coefficient.
Volume-uniform decay and the physical/continuum gap remain open.

Four modules, 6+10+13+6=35 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source and direct-import
artifact freshness checked. Monitored one-worker 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: canonical rooted families of the ORIGINAL boundary numerator.**
[`core_path`](lean/YMGap/Continuum/BF4ExactSlabRootedSelection.lean)
returns explicit paths in the literal plaquette-link graph. The computed
core keeps the input face order; its complement is proved equal to the
existing detached-region filter. Both probe supports are joined at the
root; this alone does not prove a path between the probes.

[`coefficient_rooted_pin`](lean/YMGap/Continuum/BF4ExactSlabRootedFamilyExpansion.lean)
proves the original signed coefficient equals its core coefficient times
the spectator partition-square coefficient. Permutation invariance makes
the ordered split legitimate. Duplicate-free selections and unique computed
keys give an exact family grouping without double counting.
[`boundaryNumerator_rooted_expansion`](lean/YMGap/Continuum/BF4ExactSlabBoundaryRootedFamilies.lean)
pins the resulting double sum to the EXISTING original boundary D.

The ordered-family saturation residue of this checkpoint is now closed by
the result above. Collar/path counting, mixed normalization, summability
and the physical/continuum gap remain open.

Four modules, 6+16+11+4=37 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: exact spectator resummation with an ORIGINAL partition-relative bound.**
[`spectatorSum_pin`](lean/YMGap/Continuum/BF4ExactSlabSpectatorResummation.lean#L114)
sums signed spectator coefficients before taking absolute values and returns
`anchor coefficient * Z_spectator^2`, with the original Haar partition.
The detached spectator faces and their removed collar are computed from
literal probe/anchor links; their partition and disjointness are proved.

[`relative_floor`](lean/YMGap/Continuum/BF4ExactSlabRelativePartitionBound.lean#L50)
proves `(1-delta)^|removed| Z_background <= Z_full`, retaining shared links.
Combined with resummation,
[`detached_cleared_bound`](lean/YMGap/Continuum/BF4ExactSlabResummedCoefficientBound.lean#L72)
gives `F^2 |family| <= anchorCap * Z_ambient^2`, where
`F=(1-delta(w))^(collar size)` and `anchorCap=2*c_p*c_q*kappa(w)^|anchor|`.
The loss counts removed faces, not spectator faces. The explicit small-nome
guards remain, with `delta<=1`; `F>0` is checked for every finite collar at
the existing `w=1/1024` pilot.

**Scope of this estimate:** it applies to an anchored family, now identified
with the actual computed fiber by the result above. The boundary-insertion
specialization uses the INTERIOR partition square, not the boundary
comparison's mixed denominator `Z_large*Z_small`. Collar/path counting,
mixed normalization and summability
remain open, before distance decay, padding limits and the physical/Clay gap.
Five modules, 4+8+6+7+6=31 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: actual connected-coefficient bounds and an ORIGINAL boundary majorant.**
[`connectedCoefficient_bound`](lean/YMGap/Continuum/BF4ExactSlabConnectedCoefficientBound.lean#L74)
bounds the existing inclusion–exclusion coefficient by `2*c_p*c_q*kappa(w)^n`,
where `c_p,c_q` are constructed Haar interval caps and
[`kappa(w)=2*delta(w)+delta(w)^2`](lean/YMGap/Continuum/BF4ExactSlabConnectedCoefficientBound.lean#L45),
with `delta(w)=128*w^3`. It holds at every cutoff and extent under
`0<=w<=1` and `(2*w^3)*16<=1/2`. The general guard does **not** imply
`kappa<1`; strict smallness is kernel-checked at the existing `w=1/1024` pilot.

The proof identifies the actual coefficient with repeated simultaneous
insertions into the original two-copy Haar moment form. Each step has exactly
three terms: remainder in the left copy, right copy, or both. This proves the
new bound rather than borrowing a single-copy activity estimate.

[`boundarySummand_bound`](lean/YMGap/Continuum/BF4ExactSlabBoundaryCoefficientBound.lean#L63)
gives `2*c_p*delta(w)^|S|*kappa(w)^|T|` for each exterior/interior selection
pair. [`boundaryNumerator_bound`](lean/YMGap/Continuum/BF4ExactSlabBoundaryCoefficientBound.lean#L86)
sums those caps over the actual separating-cut filtered expansion, producing
a computed finite bound for the EXISTING boundary numerator with **no cutoff
parameter**. Volume, nome and probe support/cap remain explicit.

**Next:** handle disconnected spectator pieces together with the original
partition factors, and prove geometric counting and normalized summability.
The finite majorant is not volume-uniform or a distance-decay bound. No
padding limit, physical gap or continuum/Clay theorem is proved here.
Five modules, 7+8+9+6+7=37 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: selected-cut cancellation reaches the ORIGINAL boundary response.**
[`boundaryNumerator_connecting_expansion`](lean/YMGap/Continuum/BF4ExactSlabBoundaryConnectingSelections.lean#L85)
is an exact double finite expansion of the existing boundary numerator:
exterior remainder selections, then interior inclusion–exclusion coefficients
filtered by a computed separating-cut search. The same probe, action, cutoff,
Haar carrier and determinant factors are retained.

[`coefficient_zero_of_separator`](lean/YMGap/Continuum/BF4ExactSlabConnectedSelectionExpansion.lean#L83)
proves a coefficient is zero whenever its selected faces admit a cut between
the probes. Every subselection inherits the separator and its original
connected numerator vanishes. Thus the FULL interior may remain interacting;
detachment from the entire interior is no longer required for this cancellation.
[`findSeparator`](lean/YMGap/Continuum/BF4ExactSlabSelectionSeparation.lean#L103)
returns an actual cut with a disjoint-support proof; retained selections
[`have no enumerated separating cut`](lean/YMGap/Continuum/BF4ExactSlabConnectedSelectionExpansion.lean#L102).
The search is exhaustive finite enumeration, not an efficient cluster algorithm.

**Next:** bounds on these inclusion–exclusion coefficients, geometric
path-length control and normalized summability yielding separation decay.
The previous `delta(w)^n` bounds concern remainder activities, not these new
coefficients; no such bound is inferred. No distance-decay, padding-limit,
physical-gap or continuum/Clay theorem is proved by this finite identity.
Four modules, 9+15+9+4=37 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: an exact expansion of the ORIGINAL boundary response.**
[`boundaryNumerator_expansion`](lean/YMGap/Continuum/BF4ExactSlabBoundarySelectionExpansion.lean#L92)
expresses the existing boundary numerator as a finite sum of actual exterior
face-selection responses. The interior action, probe, shared links, common
cutoff and partition factors are retained. This is an identity for the
tracked physical quantity, not a replacement correlation model.

[`moment_expansion`](lean/YMGap/Continuum/BF4ExactSlabRemainderExpansion.lean#L53)
and `partition_expansion` expand the original moments and partition into
products of original heat remainders. Under the explicit small-nome guard,
[`activity_bound`](lean/YMGap/Continuum/BF4ExactSlabRemainderExpansion.lean#L81)
gives `delta(w)^n` for each selection of `n` faces, at every cutoff and
extent, even when faces share links. `original_background_bound` retains
the same positive original background integral on the right-hand side.

Literal face-link locality and original Haar factorization give
[`connectedNumerator_zero`](lean/YMGap/Continuum/BF4ExactSlabDisconnectedHaarCancellation.lean#L122)
for a supplied disjoint split, including all four moment/partition factors.
In the boundary expansion, empty selections and selections detached from
the **entire interior/probe region** contribute exactly zero.

**Next mathematical frontier:** connecting-selection reorganization and
normalized summability that yield decay with probe-to-boundary distance.
The proved detachment condition is stronger than being far from the probe;
counting all selections can still grow with volume. No distance-decay,
padding-limit, physical-gap or continuum/Clay claim follows yet.
Six modules, 6+8+12+14+7+6=53 exactly matched focused axiom gates within
`{propext, Quot.sound}`; final error/warning free, with source and direct-import
artifact freshness checked. One-worker monitored 20 GiB checks; no new holes,
analytic inputs, numerical oracle or raised limits. No full build/audit/guard/
progress run; the root import list was updated but not rebuilt.

**Preceding result: local heat-weight comparisons on the ORIGINAL action.**
[`faceRemainderInterval`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean#L54)
constructs both signs of the original face-remainder bound under Haar
integration, retaining shared links. The explicit cap is
[`delta(w)=128*w^3`](lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean#L85),
at every representation cutoff and physical face in every finite slab,
under `0<=w<=1` and `(2*w^3)*16<=1/2`.

With `delta(w)<=1`, the actual original heat factors and their finite products
receive constructed positivity certificates.
[`originalBackground_comparison`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean#L160)
then proves that inserting one face multiplies any such background integral
by factors bounded between `1-delta(w)` and `1+delta(w)`. These factors do not
depend on cutoff, volume or the number of background faces. No link
independence or substitute probability law is used. The existing `w=1/1024`
pilot satisfies both guards by kernel calculation.

**Boundary of this result:** the finite-product floor `(1-delta(w))^F`
depends on the number of faces `F`; it is not a volume-uniform partition
floor. The local comparison has no separation factor. Quantitative
normalized boundary decay, padding convergence, nonzero-norm persistence,
physical transfer/gap and the continuum/Clay target remain open.
Three modules, 10+12+10=32 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free and artifacts current.
One-worker monitored 20 GiB checks; no new holes, analytic inputs,
numerical oracle or raised limits. No full build/audit/guard/progress run.

**Preceding result: uniform observable-size bounds on the ORIGINAL action.**
The computed [`bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformSquareBound.lean#L33)
depends only on an expression's spins, rational coefficients and operations.
Constructed sum-of-squares certificates bound its actual lower and reflected
upper polynomials; they retain all shared link variables. Positivity of the
original action and exact normalization then give
[`form_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L98)
and [`connected_norm_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L108).
No full-action coefficient bound or partition-reciprocal ceiling enters these estimates.

[`bound_bulkAtTime`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformSquareBound.lean#L69)
proves that padding and admissible time displacement leave the cap unchanged.
[`bulk_completed_norm_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L134)
bounds the actual completed centered state at every padding, and
[`bulk_correlation_square_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUniformMomentBound.lean#L141)
proves `C_bulk(e,f)^2 <= bound(e) * bound(f)` at any two admissible lags.
All rational `0<w<1` and finite odd slabs are quantified; means are bounded
on both sides by `bound(e)+1`. The cap is deliberately coarse, not optimal.

**Scope and next step:** these are a priori size bounds, with NO decaying
distance factor and NO norm-relative `q<1`. They do not prove boundary
insensitivity, persistence of a positive excitation norm, padding convergence,
bounded time descent, a physical gap, or the continuum/Clay target. Existing
cutoff moduli keep their parameter dependence; no uniform padding modulus
is claimed. Next remains quantitative normalized boundary-response control.
Three new modules: 21+6+15=42 exactly matched focused axiom gates within
`{propext, Quot.sound}`, final error/warning free and artifacts current.
One-worker monitored 20 GiB checks; no new holes, analytic inputs, numerical
oracle or raised limits. No full build/audit/guard/progress run.

**Preceding result: exact comparison of ORIGINAL expectations in two slabs.**
An explicit injective map places each source link in the larger slab.
[`haar_embedding`](lean/YMGap/Continuum/BF4ExactSlabBulkHaarEmbedding.lean#L145)
proves that unused target variables integrate to one; the same map preserves
the original ordered plaquette words, all-spin characters and heat action.
[`interiorLimit_small`](lean/YMGap/Continuum/BF4ExactSlabBulkInteriorHaarPin.lean#L148)
identifies the interior-weighted target integral with the original smaller
slab integral, after cutoff removal.
[`interiorPartition_small`](lean/YMGap/Continuum/BF4ExactSlabBulkInteriorHaarPin.lean#L157)
identifies its normalization with the original smaller partition function.

Combining those identities with the previous exact boundary response gives
[`expectationDifference_formula`](lean/YMGap/Continuum/BF4ExactSlabBulkExpectationComparison.lean#L115):
`E_large(embed p) - E_small(p) = D(embed p)/(Z_large Z_small)`.
Both partition reciprocals are constructed, not assumed. The
[`bulk_mean_comparison`](lean/YMGap/Continuum/BF4ExactSlabBulkExpectationComparison.lean#L136)
specialization uses the actual bulk-translated original plaquette expressions.
[`expectationDifferenceCauchy`](lean/YMGap/Continuum/BF4ExactSlabBulkExpectationComparison.lean#L132)
retains explicit representative-index modulus data at each fixed pair of slabs.

**Next:** quantitative control of this normalized response for deep-interior
observables, retaining the nome, volume, insertion and partition factors.
The identity does not assert smallness, volume-uniform reciprocal bounds,
padding convergence, persistence of the nonzero seed, time homogeneity or
a physical spectral gap. The continuum/Clay target remains open. Five new
modules: 23+14+12+9+7=65 exact focused axiom gates within
`{propext, Quot.sound}`, final error/warning free and artifacts current.
One-worker monitored 20 GiB checks; no new holes, analytic assumptions,
numerical constants, oracle or raised limits. No full build/audit/guard/progress run.

**Preceding result: bulk placement and an exact ORIGINAL boundary-response identity.**
The new geometry shifts all three spatial coordinates as well as time.
[`paddingForMargin_bound`](lean/YMGap/Continuum/BF4ExactSlabBulkEmbeddingGeometry.lean#L197)
proves that padding `lag+radius` places every translated plaquette-edge
endpoint at least `radius` from all box boundaries. The observable map uses
the existing original expression algebra;
[`bulkCorrelation_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteBulkEmbedding.lean#L147)
identifies its connected correlations with the actual completed centered
pairings at that stage.

[`fullHeatProduct_dressing`](lean/YMGap/Continuum/BF4ExactSlabBulkActionDressing.lean#L107)
partitions the full target action into the embedded original face factors
and their actual exterior complement, with all shared link variables retained.
Writing `I` for the interior-weighted Haar moment and `W` for the exterior
factor, [`boundaryNumerator_covariance`](lean/YMGap/Continuum/BF4ExactSlabBulkBoundaryResponse.lean#L68)
proves the exact same-cutoff identity
`D(p) = I(p W) I(1) - I(p) I(W)`.

This determinant has a constructed cutoff-limit CReal and explicit
[`boundaryCutoff`](lean/YMGap/Continuum/BF4ExactSlabBulkBoundaryResponse.lean#L114).
[`normalized_boundary_response`](lean/YMGap/Continuum/BF4ExactSlabBulkBoundaryResponse.lean#L150)
then proves `E_full(p) I(1) - I(p) = D(p)/Z_full` after cutoff removal,
using the SAME original full partition reciprocal. No reciprocal of `I(1)`
or independence of overlapping plaquettes is assumed.

**Scope at that checkpoint:** this exposed the boundary response but did not
bound its size as the boundary recedes. The smaller-carrier identification
is now proved in the latest result above. Quantitative response control remains, before
padding convergence, time homogeneity, physical transfer and a spectral gap.
The continuum/Clay target remains open. Four new modules: 79 focused axiom
gates within `{propext, Quot.sound}`, final error/warning free. No new holes,
analytic assumptions, numerical constants, oracle or raised limits; no full
build/audit/guard/progress run.

**Preceding result: literal time-separated ORIGINAL correlations, with separate stage padding and time lags.**
[`faceId_pin`](lean/YMGap/Continuum/BF4ExactSlabTimeEmbeddingGeometry.lean#L79)
constructs the actual translated physical face ID. Its map is injective and
composes correctly. Reflection changes a shift `s` under enlargement `n`
into the upper shift `2*n-s`. The observable maps preserve sums, products,
scalars, and literal all-spin plaquette evaluation.

[`displaced`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeEmbedding.lean#L132)
keeps the stage padding `n` independent of the lag. Lower and reflected upper
coordinates shift by `n-lag` and `n+lag`. The exact
[`reflected_time_separation`](lean/YMGap/Continuum/BF4ExactSlabTimeEmbeddingGeometry.lean#L179)
therefore grows by the sum of the two outward lags.

[`correlation_formula`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeCorrelations.lean#L80)
uses these original translated polynomials in three expectations under ONE
original slab action and partition function, after representation-cutoff
removal. Its `correlationCauchy` returns explicit Cauchy data.
[`correlation_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeCorrelations.lean#L94)
identifies it with the two actual centered states in THAT stage's existing
completion. Symmetry, nonnegative diagonal and sharp Cauchy--Schwarz hold
for every rational `0<w<1`. At zero padding/lags, `probe_zero_floor` recovers
the strictly positive original seed below.

**Scope:** no decay estimate, transfer-power identity, inter-stage isometry,
or stationary-vacuum claim. Geometry has sum-of-lags separation; the finite
correlations are NOT proved to depend only on that sum. Spatial coordinates
are unchanged, so this alone is not a bulk-centered 4D exhaustion.
**At that checkpoint:** spatial bulk placement and an exact boundary
comparison were next; the new result above constructs them. Quantitative
boundary control, padding limits and time homogeneity needed for bounded
physical transfer descent remain open. Three modules: 53 focused axiom gates within
`{propext, Quot.sound}`, final error/warning free; no new holes, numerical
constants, oracle, raised proof limits or full-tree build/audit.

**Preceding result: a nonzero centered state in the ORIGINAL completed plaquette space.**
At the certified nome `w=1/1024` on the extent-one slab,
[`determinant_negative`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeMinor.lean#L88)
proves `D<=-1/1024` at every representation cutoff. The actual channel
weight is positive for `K>=1`.
[`rawFloor_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeUniformFloor.lean#L85)
gives one strictly positive rational raw reflected-norm floor for every
`K>=1` and every rational centering coefficient.

That floor survives cutoff removal, normalization by the SAME original
partition function, and the actual Cauchy representative of orthogonal
centering. The constructed
[`state`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L112)
belongs to the existing original unit complement;
[`state_ne_zero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L123)
proves it is nonzero. Its normalized positive floor is computed from the raw
floor and original reciprocal bound, and
[`normCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L103)
retains the explicit norm modulus.
[`connectedCovariance_floor`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCenteredNontriviality.lean#L134)
pins this result to the ORIGINAL connected reflected covariance.

**Scope:** one fixed positive nome and finite slab, after representation-cutoff
removal and completion. This is not a stationary-vacuum identification,
physical transfer, spectral gap, or volume/spacing-uniform estimate.
**At that checkpoint:** geometric time translation on original observables
was next. The maps and finite-stage correlations are now constructed above;
slab comparison and a bound allowing physical transfer descent remain open.
The full physical OS root and continuum/Clay target remain open.
Four new Lean modules: 49 focused axiom gates within `{propext, Quot.sound}`,
final error/warning free; exact-rational pilot passed. No new proof holes,
native oracle, raised limits or full-tree build/audit.

**Preceding result: ORIGINAL interacting moment identity and small-nome error bound.**
[`scalarPlaquetteMinor_eq`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteHeatDressedMinor.lean#L91)
identifies the actual two-channel minor with `(2*w^3)^4 * D^2`, where
`D = H(p L)*H(r L)-H(p r L)*H(L)`. Here H is the same 116-link Haar
functional, p the original plaquette, r its scalar-coordinate loop, and L
the ORIGINAL lower heat product. No tree-path recoding remains in D.

Under the explicit per-face guard `(2*w^3)*R(face) <= 1/2`, where
`R(f)=2*coefficientL1(f)+1`,
[`faceTail_coefficientL1`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeFaceRemainder.lean#L76)
bounds all positive-label terms by twice the first character majorant.
A shared-variable telescope computes `E=product_i(1+delta_i)-1` from these
face bounds, without treating plaquettes as independent.
[`lowerMoment_eq`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHeatPerturbation.lean#L145)
and [`lowerMomentError_bound`](lean/YMGap/Continuum/BF4ExactSlabSmallNomeHeatPerturbation.lean#L149)
give `H(p L)=H(p)+error` and `abs(error)<=coefficientL1(p)*E` at every
representation cutoff. E depends explicitly on w and the face list.

**At that checkpoint:** the remaining task was to certify a positive nome
satisfying the finite guards, separate D from zero, and retain a positive
normalized floor through cutoff removal. The latest result above now
supplies these at w=1/1024, extent one. This estimate is not beta-, volume- or
spacing-uniform mass control. Three new modules: 40 focused axiom gates
within `{propext, Quot.sound}`, final error/warning free. No new proof holes
or full-tree build/audit; the Clay goal remains open.

**Preceding result: concrete ORIGINAL plaquette channels and exact reference Haar moments.**
[`interfaceChoice`](lean/YMGap/Continuum/BF4ExactSlabFundamentalRetainedChannels.lean#L150)
constructs the actual interface leaf for any selection of quaternion
coordinates, with coefficient-level polynomial and exact heat-weight pins.
[`loopChannel`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCoordinateChannels.lean#L108)
specializes this to the four boundary links of the original fundamental
plaquette `probe`: crossing faces `[2,4,20,40]` correspond to `A,D,C,B`.
Each resulting coordinate-product channel has weight `(2*w^3)^4`, positive
for w>0 and unchanged as the character cutoff increases past one.

The unit leaf and scalar-coordinate loop now give a fully specified
[`scalarPlaquetteFloor_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteConcreteMinor.lean#L124)
for the ORIGINAL raw reflected norm of `probe-c*unit`, for every rational c.
The two-probe bound allows overlap and pays a factor two; the sharper
distinct-path bound below remains available. No channel witness is assumed.

Bare product-Haar integration on the same 116-link carrier gives both
means zero and
[`probe_scalarChannel_haar`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteProbeHaarMoments.lean#L38)
equal to `1/128`. The resulting reference determinant is proved exactly
`-1/128`, with square `1/16384`.

**At that checkpoint:** the determinant still needed control after inserting
the ORIGINAL lower heat product, followed by a positive normalized floor
through cutoff removal. Both are now supplied above at w=1/1024, extent one.
The reference Haar computation omits that insertion; it is not the
interacting covariance. Positive channel weights alone do not establish a
positive minor. This reference computation alone did not prove a nonzero
completed centered state or mass gap.
Five new modules: 68 focused axiom gates within `{propext, Quot.sound}`,
final error/warning free, no new proof holes or full-tree build/audit.

**Preceding result: a centering-independent lower bound from ORIGINAL interface channels.**
Two distinct paths in the actual reflected-square expansion retain two
weighted Haar squares without double-counting. For their observable
amplitudes `a0,a1`, unit amplitudes `b0,b1`, and weights `w0,w1`, set
`D = a0*b1-a1*b0` and `B = w0*b0*b0+w1*b1*b1`.
[`retainedFloor_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRetainedMinor.lean#L134)
proves, for **every rational centering coefficient** `c`,

```text
w0*w1*D*D / (B+1) <= ORIGINAL raw reflected norm squared of (e-c*unit).
```

The weighted Lagrange identity proves the bound; subtracting `c*unit`
leaves `D` unchanged. The denominator is proved positive without assuming
any amplitude is nonzero. All four amplitudes retain the original lower
heat product, shared links, and finite cutoff. No surrogate action occurs.

The floor is computable but **may be zero**. A positive minor for a concrete
original observable/channel pair, and a positive floor surviving cutoff
removal and normalization, remain open. This does not yet construct a
nonzero completed centered state, transfer operator, or spectral gap.
Two new modules: 38 focused axiom gates within `{propext, Quot.sound}`,
final error/warning free; no new proof holes or full-tree build/audit.

**Preceding result: actual orthogonal centering and literal ORIGINAL connected covariance.**
[`unitProjection`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteUnitProjection.lean#L78)
constructs `P(x)=<x,u>u` from the actual pairing coefficient and its
computed modulus. It is self-adjoint, idempotent and contractive.
[`center`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredCompletion.lean#L81)
is `x-P(x)`, exactly orthogonal to the original norm-one unit. Its
projection/linearity laws and
[`orthogonal_decomposition_inner`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredCompletion.lean#L161)
give Pythagoras and nonexpansiveness with no extra factor.

[`approximateCentered`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredDensity.lean#L59)
returns an original expression whose exactly centered completed state
approximates a supplied centered Cauchy representative at its original
rate. Centering commutes with represented-row limits, and
[`complementRowLimit`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredDensity.lean#L94)
retains their explicit convergence rate. No arbitrary quotient
representative is selected.

[`connectedCovariance_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteConnectedCovariance.lean#L86)
proves the literal identity
`<C(p),C(q)> = E(theta(p)q)-E(p)E(q)` with the SAME original action and
partition function. Its real representative has a computed Cauchy
modulus, symmetry, nonnegative diagonal and sharp Cauchy--Schwarz.

This is a finite-slab unit complement, **not yet a stationary physical
vacuum complement**. Next: a concrete centered observable with a strictly
positive original reflected norm. Nontriviality, physical transfer,
compatible slabs, full quotient completeness, strict gap and
continuum/Clay remain open. No temporal decay is asserted here.

Four new modules: 72 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Preceding result: real-scalar action on the ORIGINAL completed plaquette space, with explicit moduli.**
[`realScalarCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarCauchy.lean#L160)
constructs the actual expression stream `s.approx n * X.seq n`. Its
modulus uses computed scalar/vector tail ceilings and explicit error
budgets, not a modulus extracted from an erased existence proof.
[`completedRealSmul`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedRealScalar.lean#L84)
descends to the SAME completion.
[`completedRealSmul_congr`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedRealScalar.lean#L105)
proves independence of the scalar representative and supplied modulus;
both-slot homogeneity and the rational-action pin are proved.

[`scalarMulCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarAlgebra.lean#L51)
computes product moduli from the two supplied scalar moduli. Addition
and negation also retain moduli. The action respects scalar addition,
composition and vector addition; its
[`completedDist_realSmul`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarAlgebra.lean#L123)
is exact squared-distance scaling by the scalar twice.

Scope: `CReal` scalars **with supplied `QCauchy` data** for their actual
streams. This does not select such data for arbitrary legacy quotient
reals, prove full quotient-level Hilbert completeness, or prove a gap.
Canonical centering against the original norm-one unit using its actual
pairing coefficient is now supplied above. Physical vacuum stationarity, transfer,
strict mass gap and continuum/Clay remain open.

Three new modules: 37 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Preceding result: sharp completed Cauchy--Schwarz and explicit limits of represented Cauchy families.**
[`completedInner_cauchySchwarz`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedGeometry.lean#L47)
passes the original sharp inequality through the actual pairing limits.
The reused product-continuity theorem has only constructive-real inputs;
no older gauge carrier or physical transfer is imported into the statement.
The completed squared distance is symmetric, nonnegative, obeys the
sqrt-free triangle bound, and is zero exactly when its states are equal.

[`constantApproximation_bound`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedApproximation.lean#L65)
shows how to approximate a state from its supplied Cauchy representative.
[`rowLimit`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCauchyRows.lean#L98)
constructs a limit for a Cauchy family supplied with such representatives
and an outer modulus `M`. The diagonal has rate
`max(M(epsilon/16), (epsilon/16).den)`; convergence to the completed limit
has rate `M(epsilon/16)`. Its value is unique and
[`rowLimit_independent`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCauchyRows.lean#L146)
proves independence from row representatives and their moduli.
[`rowLimit_expressionRows`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCauchyRows.lean#L168)
also proves that limiting the dense expressions of any supplied original
Cauchy representative recovers its same completion class.

This **does not select representatives of an arbitrary quotient-valued
Cauchy sequence**. Modulus-bearing real-scalar extension is supplied above;
the stronger completeness claim remains open. The `epsilon/16` split is an error budget, not a physical
decay rate. The physical observable/transfer/vacuum, strict mass-gap,
volume/spacing/QFT and all-group Clay obligations remain open.

Three new modules: 45 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Preceding result: the ORIGINAL completed pairing is rationally bilinear and positive definite on every completion state.**
[`addition`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletionLinear.lean#L93)
and [`scalarContinuous`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletionLinear.lean#L97)
construct completed operations from their proved distance estimates.
Scaling by `c` uses the explicit tolerance `epsilon/(c*c+1)`, including
negative and zero scalars. The additive-group and rational scalar laws
descend from original plaquette coefficient identities.

[`completedInner_add_left`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedBilinear.lean#L43)
and [`completedInner_smul_left`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedBilinear.lean#L55)
pass the original form laws through the constructed limits; both right-slot
laws follow by symmetry. The quotient embedding preserves these operations.
[`completedInner_posdef`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedPosdef.lean#L84)
proves zero completed squared norm **if and only if** the completed state
is zero. Its forward direction returns an explicit closeness witness
[`closeZeroOfInnerZero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedPosdef.lean#L70),
using the existing pairing rate, not a chosen modulus.

Three new modules: 41 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
Completed CS and limits of represented Cauchy rows are now supplied above.
Modulus-bearing real-scalar extension is now supplied above.
**Still open at the Hilbert boundary:** full quotient-level constructive
completeness. Observable action,
all required gauge observables, compatible slabs, physical transfer,
stationary vacuum, strict physical gap, continuum QFT and all-group Clay
remain open. No new analytic premise or substitute carrier is used.

**Preceding result: the ORIGINAL mixed pairing descends to its actual completion.**
[`pairing_close`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePairingContinuity.lean#L101)
controls changes in both arguments with the explicit squared-distance
tolerance `epsilon^2 / (8*(B+1))`. The required eventual diagonal bound
is computed from a Cauchy anchor and the original action bounds, not assumed.
[`representativeInner`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePairingLimit.lean#L137)
constructs the pairing limit with explicit outer and inner moduli;
[`representativeInnerCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePairingLimit.lean#L147)
retains its approximation modulus as data.

[`completedInner`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedInner.lean#L83)
is independent of both representatives. It is symmetric, nonnegative on
the diagonal, has unit diagonal one, and
[`completedInner_embedQuotient`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletedInner.lean#L105)
recovers exactly the original null-quotient form. All bounds retain their
coupling, slab and representative dependence; none is a strict gap bound.

That increment passed 45 focused axiom gates within `{propext, Quot.sound}`,
with no new holes or full-tree audit. Its completed rational linear laws,
bilinearity and positive-definiteness frontier is now discharged above.
The remaining Hilbert and physical obligations are explicitly open;
the older boundary-code completion is not substituted for this carrier.

**Preceding result: the ORIGINAL plaquette null quotient embeds faithfully into an explicit-modulus completion carrier.**
[`null_iff_pairing`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteNullQuotient.lean#L119)
characterizes zero reflected distance as equality of all mixed pairings.
The actual normalized form therefore descends to the null quotient, where
[`inner_posdef`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteNullQuotient.lean#L209)
proves positive definiteness. Addition and rational scaling descend, and
the unit has squared norm one.

[`distSq_reflected`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L77)
pins the squared distance to `E(theta(p-q)*(p-q))`.
Positivity of a difference gives its square-root-free triangle bound;
the radical theorem supplies null congruence. This constructs the existing
explicit-modulus Cauchy
[`Completion`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L144).
[`embedQuotient_injective`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L173)
proves that completion loses no additional quotient states, and
[`completedUnit_ne_zero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteSeminormCompletion.lean#L184)
proves the embedded unit is nonzero. These statements hold for every
rational `0<w<1` and odd slab, on the same plaquette-generated subalgebra.

That increment passed 53 focused axiom gates within
`{propext, Quot.sound}`, with no new proof holes or full-tree audit.
Its pairing-limit and representative-independence frontier is now
discharged by the latest result above; the remaining Hilbert/physical
obligations are unchanged.

**Preceding result: the ORIGINAL normalized plaquette reflected form has sharp Cauchy--Schwarz and norm-null descent.**
[`form_reflected`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L53)
identifies the form with the literal `E(theta(p)*q)`, for every rational
`0<w<1` and odd slab. It is symmetric, rationally bilinear, nonnegative
on the diagonal and normalized at the unit.
[`form_cauchySchwarz`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L185)
proves `B(p,q)^2 <= B(p,p)*B(q,q)`, and
[`form_radical_zero`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L213)
proves that norm-null expressions pair to zero.
[`formCauchy`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectedForm.lean#L106)
retains the explicit original expectation modulus.

The proof uses
[`expectation_reflection_invariant`](lean/YMGap/Continuum/BF4ExactSlabPolynomialReflectionInvariance.lean#L135)
for the actual full action with any supported polynomial, and
[`finiteGNSData`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteFiniteGNS.lean#L84)
for actual finite-cutoff plaquette expressions. Finite Cauchy--Schwarz
passes through the original numerator limits; normalization divides every
pairing by the SAME positive partition function. No auxiliary-law identity
or additional analytic premise is used.

Three new modules: 41 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
Bounds and moduli depend on the nome, slab and expressions. This is still
the **plaquette-generated subalgebra**, not all gauge observables. Its
null quotient and completion carrier are now supplied above; the completed
inner product, Hilbert-space laws and observable action, compatible slabs,
transfer, stationary vacuum, uniform physical gap and continuum Clay
target remain open. The older boundary-code completion is not silently
identified with this form.

**Preceding result: reflected positivity for the ORIGINAL normalized plaquette functional.**
[`expectation_reflection_nonnegative`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L196)
proves `E(theta(p)*p)>=0` for every finite sum, product and rational multiple
of lower-half plaquette characters, at every rational `0<w<1` and odd slab.
The reflection is the literal oriented link reflection.
[`reflected_numerator_eq_squareValue`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L178)
pins the ORIGINAL full-action numerator to an explicit finite square
expansion at each cutoff. The original numerator limit and SAME positive
partition function then give the normalized inequality.
[`expectation_reflection_eq_upper`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L201)
also pins every mixed reflected pair, and
[`expectation_reflected_unit`](lean/YMGap/Continuum/BF4ExactSlabPlaquetteReflectionPositivity.lean#L212)
proves the distinguished unit has reflected value one.

Two new modules: 44 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
This is the **plaquette-generated subalgebra**: completeness among all gauge
observables is not proved. The mixed-form laws are supplied by the newer
result above. Physical completion, observable action, compatible slabs,
transfer and stationary vacuum remain to be connected; the strict uniform
physical gap and continuum Clay target remain open.

**Preceding result: positive normalized polynomial expectations for the ORIGINAL slab action.**
[`BF4ExactSlabPolynomialExpectation.expectation`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L46)
constructs `E(p)=N(p)/Z` for every rational `0<w<1` and odd slab, on the
original shared link coordinates. The signed numerator has a computed
cutoff modulus; normalization uses the same original action limit `Z`.
[`expectation_one`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L48)
proves `E(1)=1`, and
[`expectation_square_nonnegative`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L82)
proves positivity on every supported ordinary polynomial square. Linearity,
quaternion-Haar carrier invariance and exact recovery `E(p)*Z=N(p)` are proved.
[`expectationCauchy`](lean/YMGap/Continuum/BF4ExactSlabPolynomialExpectation.lean#L133)
provides a modulus for the actual normalized real approximants, with an
explicit bound depending on the nome, finite slab and polynomial.

Three new modules: 49 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
Ordinary-square positivity is **not** reflection positivity. The new result
above supplies the latter on the concrete plaquette-generated subalgebra;
its physical completion/observable action, transfer, stationary vacuum,
strict physical gap, volume/spacing passage and continuum QFT remain open.

**Preceding result: the original completed slab pairing is normalized, with its FULL heat unit of norm one.**
[`BF4ExactSlabNormalizedCompletedPairing.completedHeatUnit_norm_one`](lean/YMGap/Continuum/BF4ExactSlabNormalizedCompletedPairing.lean#L86)
proves this on the unchanged completed carrier, for every rational `0<w<1`
and every odd slab. The normalized form is exactly `B(x,y)/Z`, where `Z`
is the ORIGINAL interacting action limit. No square root, substitute vector,
or auxiliary positive law is used.

[`action_mul_reciprocal`](lean/YMGap/Continuum/BF4ExactSlabOriginalActionReciprocal.lean#L125)
constructs and cancels the reciprocal of that same `Z`. Its rational samples,
positive lower/upper bounds and modulus are explicit. The completed pairing
retains positivity, symmetry, additivity, Cauchy–Schwarz and exactly the same
zero pairings; multiplying by `Z` recovers the original form.
[`normalizedDense_approximation`](lean/YMGap/Continuum/BF4ExactSlabNormalizedCompletedPairing.lean#L166)
supplies a computed rescaling of the original dense-approximation modulus.

Three new modules: 50 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.
The normalization constants depend on the nome and finite slab.

**Next: physical observable realization, compatible slabs and geometric transfer.**
Norm one does not establish a stationary physical vacuum. These physical
identifications, the strict gap on its complement, volume/spacing control,
continuum QFT and the all-group Clay target remain open. The existing raw
completion is unchanged; this milestone proves the normalized pairing and
its quantitative comparison, not a new physical reconstruction package.

**Preceding result: the ORIGINAL action limit is strictly positive, and its completed full heat unit is non-null.**
[`BF4ExactSlabOriginalActionStrictFloor.fullActionLimit_ge_floor`](lean/YMGap/Continuum/BF4ExactSlabOriginalActionStrictFloor.lean#L61)
proves `Z(w,slab) >= c(w)^F > 0` for every rational `0<w<1` and every odd
slab, on the existing interacting Haar action limit. The bound and all
approximation cutoffs are explicit. `fullActionFloorCertificate` constructs
the existing finite certificate without a positive-floor premise; its
finite margin is `c(w)^F/4`.

[`completedHeatUnit_ne_zero`](lean/YMGap/Continuum/BF4ExactSlabOriginalActionStrictFloor.lean#L94)
then proves the ACTUAL completed full heat unit is not the zero vector,
using the previously proved norm/action identity on the same slab carrier.
This is not the earlier norm-one boundary CODE or the auxiliary positive law.

The last limit step is now proved: a computed finite label band controls
the `(1-W)` coefficient deficit, the original character tail pays the
remaining error, and a shared-link product telescope gives an explicit
Haar comparison. No pointwise-to-Haar principle or link independence is used.
Four new modules: 41 focused axiom gates within `{propext, Quot.sound}`,
no new proof holes, final error/warning free. No full-tree build/audit was run.

**Boundary of the action-floor milestone.** Normalization of the completed
pairing is now proved above; physical vacuum stationarity is not. Compatible slabs,
physical observable realization, geometric time transfer, a strict bound on
its vacuum complement, volume/spacing control, continuum QFT and the
all-group Clay target remain open. The floor depends on `w` and the finite
face count `F`; it is not a uniform spectral-gap estimate.

The dated milestones below preserve their historical verification scope.
Their former action-floor/non-nullness and scalar-normalization residues are superseded above;
the remaining physical and continuum obligations are not.

**Preceding result: the Jacobi approximants are the weighted ORIGINAL heat polynomials.**
[`BF4ExactSlabJacobiWeightedHeatPin.face_coeffEqv`](lean/YMGap/Continuum/BF4ExactSlabJacobiWeightedHeatPin.lean)
proves coefficient equality with the existing original `faceHeatTerm`s,
carrying the actual finite weights `W(w*w,N,r+1)`. `product_haar_insertion`
preserves every shared-link product with ANY insertion polynomial present.
`productFloor_le_weightedHaar` therefore gives `c(w)^F` below the integral
of those weighted original terms, at `0<w<1` and `N>=1`.

The proof uses constructive finite-grid polynomial uniqueness followed by
coefficient-preserving substitution. It does not assume that agreement of
scalar evaluations implies equality of Haar integrals. The original label
shift, heat coefficients, and inverse-nome/half normalization are retained.

**Boundary of the coefficient-identification milestone.** The finite weights
are not one. The required finite-band/tail/product comparison and original
action-limit floor are now proved above. Physical vacuum/transfer/gap and
continuum/Clay remain open. Three new modules in this preceding milestone:
31 focused gates within `{propext, Quot.sound}`, no new holes, final
error/warning free. No full-tree build or audit was run.

**Preceding result: a strict shared-link Haar floor for finite Jacobi approximants.**
[`BF4ExactSlabJacobiHaarFloor.productFloor_le_haar`](lean/YMGap/Continuum/BF4ExactSlabJacobiHaarFloor.lean)
proves that the ORIGINAL normalized quaternion Haar integral of the
finite Jacobi face-product is at least `c(w)^F > 0`, at every rational
`0<w<1`, every finite slab and every truncation `N>=1`. All overlapping
link variables and actual ordered plaquette words are retained. The floor
depends on the nome `w` and face count `F`; it is NOT coupling- or
volume-uniform, nor a spectral-gap bound.

The algebraic core is short: the actual unit holonomy gives the four-square
identity `2(1+a)=(1+a)^2+b^2+c^2+d^2` under every Haar insertion. The finite
Jacobi factors and their derivative have nonnegative coefficients in `1+a`.
The square-certificate compiler preserves products with shared variables;
retaining each constant coefficient supplies the integrated floor. No
general pointwise-to-Haar order principle or independence is assumed.

**Boundary of the preceding finite Haar result.** They are not the original
unweighted heat cutoffs. The coefficient-level pin to weighted character
polynomials and quantified Haar-limit passage are now proved above, as are
the original action-limit floor and non-null full unit. Compatible physical
slabs, stationary vacuum/transfer, strict physical gap and continuum/QFT/
all-group target remain open. Five new modules in this preceding milestone:
51 focused axiom gates within `{propext, Quot.sound}`, no new holes, final
error/warning free. No full-tree build or audit was run.

**Preceding result: an explicit strictly positive original heat floor.**
[`SU2PointwiseHeatStrictFloor.pointwiseHeatCReal_geRat_floor`](lean/YMGap/Continuum/SU2PointwiseHeatStrictFloor.lean)
proves `K_q(x) >= c(q) > 0`, for every rational `0<q<1` and `x` in
`[-1,1]`, endpoints included. With a computed prefix length `L(q)`,
`c(q) = (product_{j=1..L(q)} (1-q^j))^2 / 16`.
The proof uses a finite positive Euler prefix, a geometric tail budget,
and the proved differentiated Jacobi identity. No positive limit is assumed.

`finiteCutoff q` additionally gives an explicit label count beyond which
every ORIGINAL character prefix is at least `b(q)=c(q)/2`.
[`BF4ExactSlabHeatPointwiseFloor.eval_faceHeatPolynomial_eqv`](lean/YMGap/Continuum/BF4ExactSlabHeatPointwiseFloor.lean)
pins those prefixes to the original shared-link face polynomials, including
their exact `K+1` convention. Its product theorem gives `b(q)^F` for `F`
faces at a common rational environment, with each scalar box hypothesis
explicit. Neither the heat floor nor the product floor is coupling- or
volume-uniform. Four new modules: 30 focused axiom gates within
`{propext, Quot.sound}`, no new holes, final error/warning free.

**Boundary of the preceding pointwise result.** Pointwise
positivity is not silently promoted to a Haar-integral lower bound: the
existing algebraic Haar positivity theorem applies to polynomial squares.
The new square-certified Jacobi approximation above supplies a finite
integrated bound; its original-action limit identification is still open.
The original interacting-action floor and non-null full unit remain open,
as do physical slab compatibility, stationary vacuum/transfer, strict
physical gap, continuum/QFT and the all-group Clay target. No full-tree
build or audit was run; the refuted auxiliary-law identity remains unused.

**Preceding analytic result: differentiated JTP and original SU(2) heat nonnegativity.**
[`JacobiDifferentiatedIdentityOnBox.diffJTP`](lean/YMGap/Continuum/JacobiDifferentiatedIdentityOnBox.lean)
proves the existing, unchanged obligation `dSeriesCReal = (1/2)*Theta*S`
for every rational `0<q<1` and `-1<=x<=1`, including both endpoints.
Its `pointwiseHeatCReal_geRat_zero` then proves nonnegativity of the
ORIGINAL completed SU(2) heat series through the existing nome/offset bridge.
No same-function hypothesis, off-box totalizer, or limit-interchange premise
is supplied.

The proof identifies the actual finite product derivative with twice the
weighted heat partials, then bounds the entire derivative error by
`C_d(q) q^(2N+1)`, with a computed cutoff. All q-dependence is explicit;
uniformity is only over x in the stated interval. Four new proof modules:
36 focused axiom gates within `{propext, Quot.sound}`, no new holes.

**Remaining: a strictly positive original-action floor.** Nonnegativity alone
does not establish a non-null full unit, stationary physical vacuum, strict
spectral gap, controlled continuum limit, or the Clay theorem. Those remain
open; the refuted auxiliary-law identity above is not used.

**Preceding analytic result: the original theta product equals its series on `[-1,1]`.**
[`JacobiTripleProductOnBox.thetaProduct_eq_fullThetaSeries`](lean/YMGap/Continuum/JacobiTripleProductOnBox.lean)
proves the undifferentiated Jacobi triple product for every rational `0<q<1`
and rational `-1<=x<=1`, using the EXISTING product and series `CReal`s.
The normalization is explicit: full theta is `1 + 2 * chebTConvPt`, not
the nonconstant half-series alone. No same-limit premise is assumed.

The key estimate in
[`FiniteJacobiSeriesComparison.Ppart_sub_bareTheta_le`](lean/YMGap/Continuum/FiniteJacobiSeriesComparison.lean)
bounds the whole finite-polynomial error by `C(q) q^(2N+1)`, with
`C(q) = (2/(1-q*q)) (1+2/(1-q))` and a computed tolerance-to-cutoff map.
Gaussian absorption of the coefficient deficit avoids a separate finite-band
split. The estimate is uniform in `x` on the stated interval, NOT in `q`.
Two focused checks passed: 22 gates inside `{propext, Quot.sound}`, no new
holes. Differentiated JTP and heat nonnegativity are now proved above.
Strict original-action positivity, physical vacuum/transfer/gap, and
continuum/Clay remain open; no full-tree audit was run.

**Preceding analytic result: explicit convergence of the finite Jacobi weights.**
[`FiniteJacobiWeightBounds.centeredWeight_eq_segments`](lean/YMGap/Continuum/FiniteJacobiWeightBounds.lean)
rewrites the ORIGINAL normalized coefficient as two finite Euler products.
The coefficients lie in `[0,1]`, and for `j<=N` their deficit from one is at
most `2 Q^(N-j+1)/(1-Q)`, where `0<Q<1`.
[`FiniteJacobiWeightConvergence.centeredWeight_abs_close`](lean/YMGap/Continuum/FiniteJacobiWeightConvergence.lean)
provides a computed cutoff uniform over each specified finite band `j<=J`.
The base and band are explicit; no infinite-product denominator is assumed.
Three focused checks passed: 25 gates inside `{propext, Quot.sound}`, no new
holes. The whole-polynomial comparison and both on-box identities are now
proved above. These coefficient estimates are not a coupling-uniform physical
gap or an original-action positive floor.

**Preceding analytic result: the finite symmetric Jacobi identity is proved.**
[`FiniteJacobiIdentity.Ppart_eq_finiteJacobi`](lean/YMGap/Continuum/FiniteJacobiIdentity.lean)
identifies the ORIGINAL full theta product with its Euler-normalized finite
Gaussian/Chebyshev series, for every finite cutoff, rational `0<q<1`, and
rational `x`. The proof combines two q-Pascal orientations with the Chebyshev
recurrence, including the center's factor of two and both finite endpoints.
It uses the actual q-binomial weights, not bare theta coefficients.
Four focused checks passed: 31 gates inside `{propext, Quot.sound}`, no new
holes. Coefficient convergence, whole-polynomial comparison and the
undifferentiated and differentiated on-box identities are now proved above.
They supply heat nonnegativity, but not the positive original-action floor below.

**Latest original-action result: a retained channel bounds the full interacting action.**
[`BF4ExactSlabAllExtentRetainedVacuumChannel.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentRetainedVacuumChannel.lean)
proves `Z_K >= lowerActionValue_K^2` at every finite cutoff, odd slab and
`w >= 0`. An explicit path retains the actual trivial-representation interface
channel, whose weight is one; other nonnegative square channels are discarded.
The lower-half Haar integral keeps its full spatial interactions and shared links.

[`BF4ExactSlabAllExtentLowerActionFloor.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentLowerActionFloor.lean)
uses the lower-product tail modulus: if one tail-certified anchor has absolute
integral at least `b + epsilon`, with `b > 0`, then the full original action
limit is at least `b^2`. Either sign of that lower amplitude is allowed.
This constructs the existing full-action certificate and proves the actual
completed full unit nonzero, given those finite lower-half data.

**The required family of lower-half margins remains open.** No universal
positivity, normalization, stationary physical vacuum, strict gap or
continuum/Clay result is claimed. Three focused monitored checks passed:
35 axiom gates within `{propext, Quot.sound}`, no new sorry. No large
certificate computation or full-tree build/audit/guard was run.

**Preceding result: a finite exact criterion certifies non-nullness of the ORIGINAL full unit.**
[`BF4ExactSlabAllExtentActionFloorCertificate.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentActionFloorCertificate.lean)
supplies a proof-producing finite check: `epsilon > 0`, `b > 0`, a cutoff
beyond the original tail modulus, and `b + epsilon <= Z_K` for the ORIGINAL
interacting Haar integral. Accepted data give a positive floor for the same
action limit, with an explicit eventual approximation index. Conversely, a
supplied positive limit floor produces finite data with a computed cutoff and
quarter-floor budget; the criterion adds no analytic assumption.
[`BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitCertifiedNonzero.lean)
uses the norm/action identity to prove that a successful certificate makes
the ACTUAL completed full unit nonzero.

**Successful certificates for the full coupling/slab family are not yet
constructed.** A failed check does not prove zero. This closes the finite-floor
to non-nullness implication, not unconditional positivity, normalization or
physical vacuum identification. Next is a lower estimate for the original
finite integral at a tail-certified cutoff. Physical slab compatibility,
time/transfer, strict gap and continuum/Clay remain open. Two focused monitored
checks passed: 17 axiom gates within `{propext, Quot.sound}`, no new sorry.
No large certificate computation or full-tree build/audit/guard was run.

**Preceding result: the completed full unit's squared norm is the ORIGINAL action integral.**
[`BF4ExactSlabAllExtentActionLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentActionLimit.lean)
constructs the full interacting action-integral limit with an explicit Cauchy
modulus, for every rational `0<w<1` and odd slab. Its nonnegativity follows
from the original reflection-positive quadratic, not a decoupled model.
[`BF4ExactSlabAllExtentHeatUnitActionComparison.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitActionComparison.lean)
bounds the discrepancy between the code norm's computed interface cutoff
and the equal-cutoff action integral. The original boundary product bounds
rescale an explicit interface-remainder modulus.
[`BF4ExactSlabAllExtentHeatUnitNormAction.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitNormAction.lean)
then proves `completedHeatUnit_norm_action` by constructive limit uniqueness.

The normalization question is now pinned to this SAME action integral.
A strictly positive lower bound is still open; nonnegativity alone does not
give non-nullness. Physical unit/vacuum identification, compatible slabs,
time/transfer, strict gap and continuum/Clay remain open. All moduli retain
`w` and slab dependence. Three focused monitored checks passed: 29 axiom
gates within `{propext, Quot.sound}`, no new sorry or analytic premise.
No full-tree build/audit/guard was run.

**Preceding result: the growing full heat unit is GNS-Cauchy in the ORIGINAL slab space.**
[`BF4ExactSlabAllExtentHeatUnitCauchy.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitCauchy.lean)
constructs the actual all-label sequence, its explicit squared-distance
modulus, and its class in each original slab completion, for rational
`0<w<1`. The convergence bound retains explicit thresholds for both the
boundary cutoff and the supplied limit representative's index.

The proof combines cutoff-independent original face bounds with the
shared-variable telescoping polynomial in
[`PolynomialProductRemainder.lean`](lean/YMGap/Continuum/PolynomialProductRemainder.lean).
[`BF4ExactSlabAllExtentHeatProductTail.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatProductTail.lean)
computes the full-product remainder modulus.
[`BF4ExactSlabAllExtentHeatUnitIncrement.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnitIncrement.lean)
pins the actual code difference's original GNS norm to the two boundary
remainders and the original interface. If its coefficient bound is `B`,
make the upper remainder at most `1` and the lower at most `epsilon/(B+1)`.
This directly controls the squared norm, without a square root or assumed
independence of plaquettes.

This constructs a **full-unit completion class**, not a stationary physical
vacuum. Its non-nullness/normalization, physical interpretation and
compatibility between slabs still require proofs. Physical time/transfer,
strict gap, volume/spacing/QFT and all-group Clay remain open; the modulus
depends on `w` and the slab. Five focused monitored checks passed: 50 axiom
gates within `{propext, Quot.sound}`, no new sorry or analytic premise.
No full-tree build/audit/guard was run.

**Preceding result: the full heat-unit pairing and explicit original plaquette tails.**
[`BF4ExactSlabAllExtentHeatUnit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentHeatUnit.lean)
resums the all-label boundary coefficients into the ORIGINAL heat products.
Its completed pairing retains three separate cutoffs: left boundary, interface
and right boundary. At equal finite cutoffs, the quadratic is exactly the
full original slab action integral. This identifies the growing sequence;
fixed-anchor stabilization does not establish its convergence.

[`SU2HeatCharacterPolynomialMajorant.lean`](lean/YMGap/Continuum/SU2HeatCharacterPolynomialMajorant.lean)
bounds the actual character polynomial's coefficient sum by
`(2*L1(p)+1)^s`, retaining the exact dimension/Casimir heat coefficient.
[`SU2HeatCharacterPolynomialTail.lean`](lean/YMGap/Continuum/SU2HeatCharacterPolynomialTail.lean)
supplies a starting label and tolerance modulus for every rational `0<w<1`.
Both depend explicitly on `w` and the polynomial; its eventual factor `1/2`
is a representation-tail estimate, **not a spectral-gap rate**.
[`BF4ExactSlabAllExtentFaceHeatTail.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentFaceHeatTail.lean)
applies this to each original plaquette: a later heat prefix literally equals
the earlier prefix plus a computed remainder with small coefficient norm and
Haar integral. No pointwise-to-Haar limit bridge is assumed.

Subsequent discharge above: full-product remainders, the moving-anchor GNS
Cauchy modulus and completed full unit. Non-nullness, compatible slabs,
physical transfer and stationary vacuum, strict gap, volume/spacing/QFT and
all-group Clay remain open. Four focused monitored checks passed: 49 axiom
gates within `{propext, Quot.sound}`, no new sorry or analytic premise.
No full-tree build/audit/guard was run.

**Preceding result: a non-null normalized code and exact centered pairings at every odd extent.**
[`BF4ExactSlabAllExtentVacuumNormalization.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentVacuumNormalization.lean)
proves that the constant insertion has exposed degree zero. The full original
interface therefore stabilizes at cutoff zero and has Haar value one. This
gives the trivial-representation boundary code norm one at every odd extent
and cutoff, retaining the original heat weights.

[`BF4ExactSlabAllExtentVacuumCodeGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentVacuumCodeGNS.lean)
proves this code is non-null in the completed space. Centering by its own
rational mean stays inside the finite-boundary carrier. The completed centered
pairing equals the original finite bilinear minus the product of its two
original code means, beyond one explicit common cutoff stage.

This is a **code-relative covariance**, not yet a physical-time connected
correlator: the code is not identified with the all-label heat-dressed unit
or a stationary physical vacuum. Slab compatibility, physical unit/vacuum and
time evolution, strict gap, volume/spacing/QFT and all-group Clay remain open.
Two focused monitored checks passed: 27 axiom gates within
`{propext, Quot.sound}`, no new sorry or analytic premise. No full-tree audit.

**Preceding result: one original-law cutoff-limit completion at every odd slab extent.**
[`BF4ExactSlabAllExtentAnchoredCutoffLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentAnchoredCutoffLimit.lean)
proves exact stabilization of the FULL original signed bilinear on fixed
finite boundary observables. The same zero extension retains both boundary
polynomials, and the computed maximum of the anchor and interface degree
bound supplies the cutoff modulus and rational `CReal` limit.

[`BF4ExactSlabAllExtentBilinearGram.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentBilinearGram.lean)
proves the full mixed channel-product identity and symmetry for w >= 0,
retaining both observables and all original interactions. Combined with
positivity and common finite cutoff stages, this constructs every form law in
[`BF4ExactSlabAllExtentCutoffLimitForm.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentCutoffLimitForm.lean).
[`BF4ExactSlabAllExtentCutoffLimitGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentCutoffLimitGNS.lean)
then constructs a completion for each slab: all its finite cutoff anchors
embed into the same carrier, with inner products equal to the original
finite/limit pairings. Specified Cauchy representatives and the outer
convergence rate remain data; no quotient representatives are chosen.

Subsequent discharge above: all-extent code normalization/non-nullness and
centered pairing pins. Next: compatibility between these slabs, then physical
time/transfer and a stationary vacuum.
A family of completed slab spaces is not yet one physical positive-time
realization. Its strict gap, volume/spacing limits, QFT axioms and all-group
Clay target remain open. No slab-uniform modulus or beta/spacing-uniform
spectral rate is claimed. Seven focused monitored checks passed: 58 axiom
gates within `{propext, Quot.sound}`, final error/warning free. No new sorry,
analytic premise, raised proof limit or numerical oracle; no full-tree audit.

**Preceding result: exact cutoff removal for the ORIGINAL interface at every odd extent.**
[`BF4ExactSlabAllExtentExposedLinkDegree.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentExposedLinkDegree.lean)
proves structurally that each crossing face has an exposed lower spatial link
absent from every other crossing face. Their full character product has
degree zero in that link, regardless of its other spins.
[`SU2QuaternionFourBlockExposure.lean`](lean/YMGap/Continuum/SU2QuaternionFourBlockExposure.lean)
constructs four explicit coordinate swaps; the original ordered character,
every insertion and the full Haar carrier are retained by
[`BF4ExactSlabAllExtentSelectedFaceSelection.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentSelectedFaceSelection.lean).
No slab-size scan or independent replacement kernel is used.

[`BF4ExactSlabAllExtentInterfaceCutoffLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentInterfaceCutoffLimit.lean)
proves `interfacePairing_stable`: with a fixed supported polynomial P, all
original crossing-face heat factors can vary together and the pairing is
EXACTLY unchanged above the computed `interfaceBound half P`.
`interfacePairingLimit` returns the rational `CReal` limit;
`interfacePairingLimit_exact` supplies its exact cutoff modulus.
The statement holds at every finite odd extent and every rational w.
The bound depends on P and the slab, and can inherit parameter dependence
through P. This is not a beta/spacing-uniform spectral estimate.

Subsequent discharge above: larger-slab fixed-boundary recoding and the
common cutoff-limit form/completion. Compatibility and physical positive-time
realization remain open. Physical time/transfer,
stationary vacuum, strict completed gap, volume/spacing/QFT and all-group
Clay remain open. Seven focused monitored checks passed: 57 axiom gates
within `{propext, Quot.sound}`, final error/warning free. No new sorry,
analytic premise, proof-limit increase or numerical oracle; no full-tree audit.

**Preceding result: ORIGINAL signed-law reflection positivity at every odd slab extent.**
[`BF4ExactSlabAllExtentPlaquetteReflection.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentPlaquetteReflection.lean)
proves literal time-link conjugation and the oriented plaquette-reflection
identity for every extent and spin. A general four-quaternion cyclic-inverse
scalar identity replaces the old extent-one face scan; no quaternion factors
are commuted and no unit-norm assumption is needed for this identity.
[`BF4ExactSlabAllExtentObservableReflection.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentObservableReflection.lean)
then proves `lowerObservable_reflection`: the original upper observable is
the literal reflection of the original lower observable, retaining every
heat weight and signed coefficient on the same padded carrier.

[`BF4ExactSlabAllExtentReflectionPositivity.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentReflectionPositivity.lean)
proves the assembled lower observable is lower-local and joins these facts
with the original spatial-Gram Haar identity. `originalQuadraticExpansion`
constructs the actual finite square channels; `exact_quadratic_eq_squareValue`
identifies the ORIGINAL `exactCorrectedSlabReflectedKernel` quadratic with
their weighted sum of rational squares. `exact_quadratic_nonnegative` proves
it nonnegative for every odd extent, every finite K, every w >= 0 and
arbitrary signed boundary coefficients. Shared link variables are retained.
This is reflection positivity, not a strict spectral estimate.

Subsequent progress above supplies the interface cutoff limit, larger-slab
boundary recoding and common cutoff-limit completion. Slab compatibility still
precedes the physical positive-time carrier and geometric transfer; physical vacuum stationarity,
a strict completed gap, volume/spacing limits, QFT and all-group Clay remain open.
Four focused monitored checks passed: 10 + 11 + 4 + 7 = 32 axiom gates
within `{propext, Quot.sound}`, final error/warning free. These include the
locality module's existing gates and its new all-extent character consumer.
No full-tree audit was run; no new sorry, analytic premise or proof-limit increase.

**Preceding result: the COMPLETE original signed bilinear has its spatial-Gram Haar form at every odd extent.**
[`BF4ExactSlabAllExtentWeightedFactorization.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentWeightedFactorization.lean)
keeps the existing signed dual term and factors its complete heat-weighted
network into lower, fixed and upper pieces. Face indexing and partition
associativity are proved structurally, without an extent-specific scan.
[`BF4ExactSlabAllExtentObservableHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentObservableHaarForm.lean)
moves all signed boundary sums under the same Haar integral and resums the
actual central label carrier into the product of face heat polynomials.

[`BF4ExactSlabAllExtentTemporalImages.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentTemporalImages.lean)
pins the complete observable's image to the independent temporal assignment.
[`BF4ExactSlabAllExtentTemporalHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentTemporalHaarForm.lean)
checks all polynomial support before using Haar invariance.
`exact_bilinear_eq_spatialGramHaar` proves, for every odd extent, finite K,
rational w and signed boundary coefficients,
`B(left,right) = Haar(L_left * H_Gram * U_right)`, where B is the ORIGINAL
`exactCorrectedSlabReflectedKernel` bilinear and both boundary polynomials
are unchanged. No replacement law or positivity premise is used.

The subsequent result above proves `U_right = theta(L_right)` and assembled
lower-half locality at arbitrary extent, closing original-law reflection
positivity for every odd slab. Slab compatibility and physical time remain open.
Four focused monitored checks passed: 16 + 12 + 13 + 11 = 52 gates within
`{propext, Quot.sound}`, no errors or warnings. No full-tree audit was run.

**Preceding result: positive temporal-gauge crossing interfaces on every odd slab.**
[`BF4ExactSlabLocalSquareExpansion.lean`](lean/YMGap/Continuum/BF4ExactSlabLocalSquareExpansion.lean)
stores actual finite reflected-square channels, their polynomial equality,
carrier support, lower-half locality and nonnegative weights. Products keep
shared variables. `haar_eq_squareValue` identifies the original Haar value
with the explicitly computed sum of squared channel integrals.

[`BF4ExactSlabAllExtentSpatialGramPositivity.lean`](lean/YMGap/Continuum/BF4ExactSlabAllExtentSpatialGramPositivity.lean)
constructs these expansions from the actual central crossing-face list,
spatial-link representation columns and heat coefficients at every odd
extent and finite cutoff. `temporalInterface_haar_gram` identifies the
complete temporal-assigned crossing interface with its Gram product under
every insertion. `temporalInterface_eq_squareValue` and
`temporalInterface_nonnegative` apply to any supported lower-half polynomial,
without discarding its spatial interactions. `original_quadratic_pin`
recovers the previously proved ORIGINAL signed quadratic at extent one.

The COMPLETE original-law/observable change-of-variables pin, literal
upper/lower reflection and locality at arbitrary extent are now proved above.
Compatibility, geometric time, stationarity and a gap remain separate.
Two focused monitored checks passed: 12 + 15 = 27 axiom gates within
`{propext, Quot.sound}`, no errors or warnings. No full-tree audit was run.

**Preceding result: ONE completed original cutoff-limit carrier for all finite anchor observables.**
[`BF4ExactSlabFiniteBoundaryObservable.lean`](lean/YMGap/Continuum/BF4ExactSlabFiniteBoundaryObservable.lean)
stores each coefficient function with an explicit finite cutoff witness.
Addition takes the maximum of two witnesses. Every original finite-anchor
coefficient function has a specified image in this common carrier.
[`BF4ExactSlabCutoffLimitForm.lean`](lean/YMGap/Continuum/BF4ExactSlabCutoffLimitForm.lean)
proves the pairing independent of cutoff witnesses and transports
bilinearity, symmetry and positivity from the ORIGINAL finite forms at
explicit common stages. `cutoffLimitGNSData` contains all finite anchors,
with no fixed representation cutoff parameter.

[`BF4ExactSlabCutoffLimitGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabCutoffLimitGNS.lean)
constructs its null-quotient completion. `cutoffLimitEmbed_anchored_pairing`
pins every original finite observable's completed inner product to its
previously proved anchored cutoff limit; `cutoffLimitEmbed_finite_pairing`
pins it to every sufficiently late original finite form. Completeness uses
explicit representative families and moduli, without choosing arbitrary
quotient representatives. The single vacuum-code vector agrees with the
original vacuum delta on every finite carrier, has norm one, and is non-null
in the common completion. Physical stationarity is not asserted.

**Next:** extend cutoff-limit control beyond extent one and prove larger-slab
compatibility, then positive-time realization, a physical transfer and a
strict gap on its own completed vacuum complement. This completion's scope
is the extent-one boundary-coefficient observable family, not the canonical
continuum positive-time root. Finite-cutoff positivity now holds on every
odd slab; volume/spacing limits, QFT axioms and all-group Clay remain open.
Three focused monitored checks passed: 36 axiom gates within
`{propext, Quot.sound}`, no new sorry, analytic premise or proof-limit increase.
No full-tree audit was run.

**Preceding result: the ORIGINAL fixed-observable slab bilinear has an exact cutoff limit.**
[`BF4ExactSlabBoundaryCutoffRecoding.lean`](lean/YMGap/Continuum/BF4ExactSlabBoundaryCutoffRecoding.lean)
keeps both heat-dressed boundary polynomials unchanged at every larger
cutoff, using a finite Boolean label test. Only the original interface varies.
[`BF4ExactSlabSelectedFaceDegreeSelection.lean`](lean/YMGap/Continuum/BF4ExactSlabSelectedFaceDegreeSelection.lean)
proves selected-face annihilation with the other twenty-three characters
retained at arbitrary spins. Their degree in the selected exposed link is
zero, so only the fixed observable determines the selection bound.

[`BF4ExactSlabInterfaceCutoffSelection.lean`](lean/YMGap/Continuum/BF4ExactSlabInterfaceCutoffSelection.lean)
takes the explicit maximum of the twenty-four degree bounds and kills every
above-bound term, retaining all original heat coefficients.
[`BF4ExactSlabAnchoredCutoffLimit.lean`](lean/YMGap/Continuum/BF4ExactSlabAnchoredCutoffLimit.lean)
then proves `interfacePairing_stable` by exact filtering of the original
enumeration. `exactCutoffPairing_stable` and `exactCutoffPairingLimit_exact`
pin the ORIGINAL signed bilinear to its computed rational CReal limit at
every cutoff beyond `exactCutoffPairingModulus`.
`exactCutoffPairingValue_nonnegative` proves the quadratic limit nonnegative
for w >= 0. Scope: extent one and each fixed finite boundary observable.

The common completed cutoff-limit carrier is now constructed above.
Geometric physical time/transfer and a strict gap on its own vacuum
complement remain open. Finite-cutoff positivity now holds on every odd slab;
volume/spacing limits, QFT axioms and the all-group Clay target remain open.
The four modules have 50 clean axiom gates within `{propext, Quot.sound}`
from focused monitored checks; no new sorry, analytic premise or proof-limit
increase. No full-tree audit was run.

**Preceding result: exact degree selection for a single original heat insertion.**
[`SU2QuaternionHarmonicDegreeSelection.lean`](lean/YMGap/Continuum/SU2QuaternionHarmonicDegreeSelection.lean)
proves that a head-homogeneous harmonic of degree n has zero partial Haar
pairing with every lower-degree polynomial, retaining all tail coefficients.
The proof combines the existing Gaussian integration-by-parts/Euler identity,
induction on the multiplier's degree and the explicit sphere radial factor.
[`SU2QuaternionHeadDegreeDifferential.lean`](lean/YMGap/Continuum/SU2QuaternionHeadDegreeDifferential.lean)
provides computable degree-lowering derivative representatives, proved
coefficientwise equal to the original derivatives.

[`SU2QuaternionExposedHeatCutoffSelection.lean`](lean/YMGap/Continuum/SU2QuaternionExposedHeatCutoffSelection.lean)
applies this to the ACTUAL all-spin four-link character on the original
116-link Haar carrier. `exposedCharacter_haar_zero` kills every spin above
the explicit `headDegreeBound P`. `exposedHeatPairing_stable` proves the
actual heat-packet pairing is exactly unchanged for every larger K, with
P fixed, at every rational w and all sixteen orientations.
`exposedHeatPairingLimit` is its explicitly evaluated rational value in CReal;
`exposedHeatPairingLimit_exact` supplies the stabilization pin.

At that checkpoint, boundary recoding and joint interface stabilization
remained open. They are now proved above. A common completed limit carrier,
physical time/transfer, its strict completed gap and continuum/Clay remain open.
Three focused monitored checks passed: 25 axiom gates within
`{propext, Quot.sound}`, no new sorry or analytic premise. No full-tree audit.

**Preceding result: reflection positivity and a completed carrier for the ORIGINAL signed form.**
[`BF4ExactSlabAllCutoffReflectionPositivity.lean`](lean/YMGap/Continuum/BF4ExactSlabAllCutoffReflectionPositivity.lean)
proves `exact_quadratic_eq_squareSum` and `exact_quadratic_nonnegative`:
`Q(c) = sum_j a_j (Haar P_j)^2 >= 0`, at extent one, every cutoff K,
`w >= 0`, and arbitrary signed boundary coefficients. The actual channels
are lower-local; product Haar factors across disjoint quaternion blocks by
its explicit monomial moments, without an independence axiom. This closes
the finite-slab positivity step for the same signed law.

[`BF4ExactSlabFiniteCutoffGNS.lean`](lean/YMGap/Continuum/BF4ExactSlabFiniteCutoffGNS.lean)
then constructs `exactGNSData` with its bilinear field definitionally equal
to the original reflected kernel form, and `exactCompletion` for each K.
`exactEmbed_pairing` pins the completed dense inner product to that form.
The vacuum-code vector has norm one and is non-null, including after
completion. Limits use the existing explicit-modulus representative-family
API; no representatives of arbitrary quotient-valued sequences are selected
by choice. This does not assert vacuum stationarity or a transfer operator.

**Next:** a cutoff-compatible carrier and geometric physical time/transfer
for this exact law, followed by a strict bound on that same completed vacuum
complement. Arbitrary-volume positivity, thermodynamic/continuum control,
QFT axioms and the all-group Clay target remain open.

Six focused monitored checks passed: 57 axiom gates within
`{propext, Quot.sound}`, no new sorry or analytic premise. This is not a
full-tree build or audit.

**Preceding result: the SAME signed quadratic has an explicit global reflected-square expansion.**
[`BF4ExactSlabReflectedSquareHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabReflectedSquareHaarForm.lean)
proves `Q(c) = Haar(sum_j a_j theta(P_j) P_j)` for the ORIGINAL extent-one
signed slab form, every cutoff K, rational heat parameter w and signed
boundary coefficient function c. The finite tree stores all weights and
channels as computable data; its weights are nonnegative when `w >= 0`.

The proof uses literal spatial-link reflection of the actual representation
columns, then expands products into all cross-terms on the SAME carrier.
[`BF4ExactSlabReflectedSquareGluing.lean`](lean/YMGap/Continuum/BF4ExactSlabReflectedSquareGluing.lean)
retains shared links, original heat coefficients and the full signed
observable. Explicit 116-link support licenses the final Haar identity.
No independent-face assumption, numerical oracle or positivity premise is used.

The subsequent result above proves lower-half locality, reflected Haar
factorization and extent-one slab positivity. The square expansion alone
was not a positivity theorem. Physical time/transfer, the exact-law
completed gap and continuum/Clay remain open.

**Preceding result: the SAME signed quadratic has a spatial reflected-Gram interface.**
[`BF4ExactSlabTemporalGaugeHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeHaarForm.lean)
proves `Q(c) = Haar(F_c * H_spatialGram * theta(F_c))` for the ORIGINAL
extent-one signed slab form, at every spin cutoff, rational heat parameter
and signed boundary coefficient function. The lower observable and its
literal reflection are unchanged. Each interface factor is now a heat sum
of Gram kernels of an original spatial link and its actual reflected mate;
the fixed-time links have been removed from those arguments.

[`BF4ExactSlabTemporalGaugeObservableImages.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeObservableImages.lean)
extends the full-chain link/word pin through the actual character recurrences,
heat products and signed observable sums. Its target evaluates the independently
defined common assignment, not the chain itself. All heat coefficients,
physical face IDs and reflected labels are retained.
[`SU2QuaternionTranslationPolynomialImages.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationPolynomialImages.lean)
provides the coefficient-sensitive algebra and supported Haar bridge.

This closed the same-observable temporal change of variables. The algebraic
global square expansion, lower-half locality, Haar factorization and
extent-one slab reflection positivity are now proved above.

**Preceding result: the full upper-link image and original plaquette words.**
[`BF4ExactSlabTemporalGaugeUpperCoordinates.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeUpperCoordinates.lean)
proves that the WHOLE original chain sends every upper link to
`g_start^-1 U g_end`. The target link's two endpoint shears produce that word;
every other link batch preserves it because its selected coordinate is
different and all endpoint gauges are fixed. Absent endpoints remain the
existing identity fallback. Together with the lower/fixed theorem, this
identifies the common assignment on EVERY actual physical link, at arbitrary
extent and half-plane. `temporalLedger_plaquette_word` then identifies the
image of every ORIGINAL oriented plaquette holonomy with the previously
defined common temporal face word.

[`SU2QuaternionTranslationWordComposition.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationWordComposition.lean)
supplies coefficient-sensitive chain composition, ordered multiplication,
conjugation and constant preservation. Explicit common padding covers empty
chains; no Haar integration or sphere relation is used to erase a discrepancy.
The full observable identity and global reflected-square gluing are now
proved above, as are lower-half factorization and extent-one positivity.

**Preceding result: literal temporal ledger and its full fixed-coordinate frame.**
[`BF4ExactSlabTemporalGaugeLedger.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeLedger.lean)
generates the actual upper-link shear chain at every slab extent: left-inverse
by the starting fixed-time link, then right-direct by the ending fixed-time
link. An absent endpoint contributes no step, matching the existing identity
fallback without adding variables. Index bounds and distinctness are proved
structurally. The chain preserves the SAME full product-Haar integral for
every supported polynomial, with no degree bound or scan hypothesis.

[`BF4ExactSlabTemporalGaugeFixedCoordinates.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeFixedCoordinates.lean)
identifies the WHOLE chain with the common assignment on every actual lower
or fixed link. Every emitted multiplier is a fixed-time link, and the chain
leaves these coordinates unchanged. The coefficient version uses explicit
common padding and covers empty ledgers. The new theorem above completes the
upper-link image.

**Preceding result: all four shear images, with full coefficient equality.**
[`SU2QuaternionCoordinateConjugation.lean`](lean/YMGap/Continuum/SU2QuaternionCoordinateConjugation.lean)
identifies the original coordinate-sign substitution with quaternion
conjugation on precisely its named block. It fixes all other blocks and
preserves ordered products. The conjugate--translate--conjugate construction
in [`SU2QuaternionInverseTranslationCoordinates.lean`](lean/YMGap/Continuum/SU2QuaternionInverseTranslationCoordinates.lean)
then proves the actual coordinate image of every left/right, direct/inverse
shear, at arbitrary valid indices. Every non-selected link, including the
multiplier, is unchanged.

[`SU2QuaternionTranslationCoordinateCoefficients.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationCoordinateCoefficients.lean)
upgrades those prefix identities to full coefficient-probe equality against
the correctly padded original quaternion product. This is the equality
consumed by the existing word/product composition theorems, without finite
coordinate scans. The full-chain link and plaquette-word identification is
now supplied by the latest result above.

**Preceding result: structural direct selected-link substitution.**
[`SU2QuaternionHeadSubstitutionPrefix.lean`](lean/YMGap/Continuum/SU2QuaternionHeadSubstitutionPrefix.lean)
proves that the actual head substitution replaces its four variables by the
supplied quaternion and fixes every tail variable, respecting finite-coordinate
prefix equivalence even across different trailing-zero padding.
[`SU2QuaternionSelectedTranslationCoordinates.lean`](lean/YMGap/Continuum/SU2QuaternionSelectedTranslationCoordinates.lean)
then proves the actual direct left/right shear's ordered product image for
arbitrary carrier size and selected/multiplier indices. Every other coordinate
is unchanged. Arbitrary subsequent direct/inverse shear chains preserve these
prefix identities. No enumerated coordinate certificate is assumed.

**Preceding result: temporal gauge cancellation on the literal slab faces.**
[`SU2QuaternionHaarGaugeCancellation.lean`](lean/YMGap/Continuum/SU2QuaternionHaarGaugeCancellation.lean)
proves ordered vertex-gauge cancellation under every polynomial Haar
insertion. Hamilton factors are not commuted. In a crossing word
`A B C^-1 D^-1`, substituting `C := D^-1 C B` cancels both fixed-time links
and leaves `A C^-1`.

[`BF4ExactSlabTemporalGaugeFaces.lean`](lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeFaces.lean)
uses ONE vertex field from the actual fixed-time link coordinates, acting
only on upper links. Lower faces are unchanged, upper characters are
preserved at every spin, and crossing faces reduce to their actual reflected
spatial-link Gram kernel at every odd slab extent. All spectator insertions
remain available, including overlapping face factors.

**Next:** combine the literal spatial reflected-Gram channels into the SAME
slab form's global square decomposition. The full observable change of
variables is proved; slab positivity is not. Physical time,
the completed physical gap and continuum/Clay construction remain open.

The three new modules passed focused monitored one-worker 20 GiB checks: 53
printed gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: all-degree Haar translation, without polynomial scans.**
[`SU2QuaternionTranslationHaarMoments.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationHaarMoments.lean)
converts the closed Gaussian formula to the ORIGINAL exact sphere moments,
retaining every tail coefficient. Even degrees use an explicit positive
radial denominator; odd degrees vanish before tail integration.

[`SU2QuaternionAllDegreeHaarTranslation.lean`](lean/YMGap/Continuum/SU2QuaternionAllDegreeHaarTranslation.lean)
then proves that the original selected left/right substitutions preserve
the full product-Haar value for every supported polynomial. The support and
distinct-block guards remain; the executable scan premise is gone.
[`SU2QuaternionAllDegreeHaarTranslationChain.lean`](lean/YMGap/Continuum/SU2QuaternionAllDegreeHaarTranslationChain.lean)
includes inverse multipliers and arbitrary finite chains. Its concrete
consumer proves Haar preservation for the existing 139-step BF4 tree-gauge
ledger at every polynomial degree.

The common temporal assignment's face algebra is now proved above. Its
identification with these Haar-preserving shears and the SAME slab form's
reflected-square gluing remain open, as do slab positivity, physical time,
the completed physical gap and continuum/Clay construction.

Four new modules passed focused monitored one-worker 20 GiB checks: 22
printed gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: closed all-degree Gaussian moments for the actual translations.**
[`SU2QuaternionTranslationGaussianMoments.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationGaussianMoments.lean)
proves `translatedHeadMonomial_gaussian_closed` for the ORIGINAL left/right
quaternion translation polynomials, at every exponent quadruple. Their
partial Gaussian integral is the existing exact `gaussianMoment4` coefficient
times the retained radius to half the total degree. Equality retains every
tail coefficient; no unit-radius or moment-equality premise is assumed.

The proof pulls head-independent factors through the partial integral,
compresses equal-label contractions to their exact count, and inducts by
removing two coordinate factors. Unmatched labels vanish without division.
Constructive count/length lemmas replace generic erase lemmas whose axiom
dependencies fail this project's gate.

Sphere/radial conversion and unconditional selected Haar translation are now
proved above. Shared-link reflected-square gluing, slab positivity, physical
time, the completed physical gap and continuum/Clay construction remain open.

Three new modules passed focused monitored one-worker 20 GiB checks: 17
printed gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: an all-degree recurrence for the actual quaternion translations.**
[`SU2QuaternionHeadGaussianIBP.lean`](lean/YMGap/Continuum/SU2QuaternionHeadGaussianIBP.lean)
proves polynomial-valued Gaussian integration by parts while retaining
every tail coefficient: `E[u_i P] = E[partial_i P]`, for arbitrary degree.
Its Euler/gradient identity yields the corresponding directional-derivative
formula for head-linear harmonic polynomials.

[`SU2QuaternionTranslationGaussianStein.lean`](lean/YMGap/Continuum/SU2QuaternionTranslationGaussianStein.lean)
applies that theorem to the ORIGINAL products `a*u` and `u*a`. Their
gradient Gram matrix is the retained radius `|a|^2` times the identity.
`translatedWord_gaussian_recursion` therefore gives the exact Wick
contraction recurrence at every word length. `translatedHeadMonomial_eq_word`
pins it coefficientwise to the existing four-exponent translation API.
The induction is unbounded; only the small four-coordinate algebra uses
finite kernel certificates. No larger table of moment checks is required
by this recurrence.

The closed Gaussian and Haar moments and unconditional selected translation
are now proved above. Shared-link reflected-square gluing remains open.
This is not slab reflection positivity or a mass-gap estimate.

Both new modules passed focused monitored one-worker 20 GiB checks: 22
printed axiom gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: the original slab quadratic uses its literal path channels.**
[`BF4ExactSlabPlaquettePathGram.lean`](lean/YMGap/Continuum/BF4ExactSlabPlaquettePathGram.lean)
proves the ordered plaquette identity `a b c^-1 d^-1 = (a b)(d c)^-1`
coefficientwise. Both actual paths have Haar-unit radius, so the all-spin
character Gram identity applies under every insertion on the original link
carrier. This works at every slab extent and spin. On a crossing face, the
paths are lower-then-fixed and fixed-then-upper: shared time links remain.

[`BF4ExactSlabInterfacePathGram.lean`](lean/YMGap/Continuum/BF4ExactSlabInterfacePathGram.lean)
retains the original `coeffW` heat weights and composes the local identities
across all 24 interface faces. `exact_quadratic_eq_pathGramHaar` identifies
the ORIGINAL signed quadratic with this path-channel product between the
same lower observable and its literal reflection, at extent one for every
rational heat parameter and cutoff. No independent-link model is substituted.

**Next:** integrate the shared time links into a global reflected-square
decomposition. This equality does not yet prove slab reflection positivity.
The selected Haar-translation lemmas still require an explicit polynomial
check; their cached moment certificate covers degree five, not all spins.
The all-degree Gaussian recurrence above is now proved, but its conversion
to an unconditional Haar-translation theorem remains open. Physical
time/transfer, the completed physical gap, continuum QFT and all-group Clay
remain open; no canonical frontier atom was closed.

Both new modules passed focused monitored one-worker 20 GiB checks: 23
printed axiom gates within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full build/audit.

**Retained result: actual all-spin character kernels have explicit Gram channels.**
[`SU2QuaternionSymmetricPowerKernelGram.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerKernelGram.lean)
proves that the ORIGINAL polynomial trace of `Sym^n D(conj(p)*q)` is a sum
of Hermitian pairings of the actual representation columns. The weights are
the explicit positive rationals `1 / C(n,k)`. The proof retains every
coefficient, so it is valid before evaluation or Haar integration; it needs
no diagonalization, eigenvector choice or square-root normalization.

[`SU2QuaternionPolynomialGramPositivity.lean`](lean/YMGap/Continuum/SU2QuaternionPolynomialGramPositivity.lean)
proves the finite quadratic is the corresponding weighted sum of Hermitian
squares for arbitrary complex polynomial coefficients. The existing Haar
square-positivity theorem then gives `characterKernelQuadratic_haar_nonneg`
for the ORIGINAL BF4 character kernel. Its explicit conditions are Haar-unit
radii for the input words and finite-coordinate support for their column
syntheses, all on the same Haar carrier. Pairwise product radii are derived,
not supplied as another premise.

The path-pair realization and same-law heat-product consumer above now pin
these kernels to the crossing geometry. Shared-link reflected-square gluing
is still open; the local positivity theorem alone does not supply it.

Four new modules passed focused monitored one-worker 20 GiB checks: 70
printed axiom gates, all within `{propext, Quot.sound}`, no errors/warnings.
No new sorry, analytic premise, rate estimate or raised proof limit; no
full build/audit. These combinatorial basis weights are not a mass-gap bound.

**Retained result: the actual trace is the original character under Haar.**
[`BF4ExactSlabSymmetricPowerHaarTrace.lean`](lean/YMGap/Continuum/BF4ExactSlabSymmetricPowerHaarTrace.lean)
proves `slabPlaquette_trace_haar_character` for every slab extent and spin.
The real trace component equals the ORIGINAL plaquette character under
every polynomial insertion in the same product-Haar integral; the imaginary
component vanishes there. The ordered link word and its signs are unchanged.

The proof has two inputs. First,
[`SU2QuaternionSymmetricPowerHaarTrace.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerHaarTrace.lean)
identifies the literal matrix trace coefficientwise with the solid-zonal
polynomial of its actual radius, at every degree. Second, quaternion norm
multiplicativity and the existing Haar sphere relation prove that the
ORIGINAL slab plaquette has Haar-unit radius. These inputs discharge the
radius premise and permit the existing solid-zonal character theorem to
apply under arbitrary spectator insertions. Pointwise equality is never
silently passed through integration.

**Next:** positive reflected channels of the literal interface heat kernels
AND their link-local gluing. The new identity is not positivity of the
reflected slab form. The physical time/transfer pin, completed physical gap,
volume/spacing control, continuum QFT and all-group Clay target remain open.

All four new modules passed focused monitored one-worker 20 GiB checks:
52 printed axiom gates, all within `{propext, Quot.sound}`, no errors/warnings.
No new sorry, analytic premise, numerical oracle, rate or raised proof limit;
no full build/audit. The original signed-Haar law remains distinct from the
positive multiplicity-product model.

**Retained result: the actual all-degree trace is the original character.**
[`SU2QuaternionSymmetricPowerTrace.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerTrace.lean)
proves `trace(Sym^n D(q)) = U_n(q.r)` for every degree and every rational
unit quaternion, with zero imaginary part. The trace is the sum of the
actual action's diagonal entries. A two-row coefficient identity, summed
along the diagonal, gives the trace recurrence; the actual quaternion norm
supplies its determinant-one relation. No eigenvalue choice or
diagonalization is needed.

[`SU2QuaternionSymmetricPowerPolynomial.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerPolynomial.lean)
constructs every literal polynomial matrix entry and proves that evaluation
recovers the same action. Its diagonal sum evaluates to the ORIGINAL BF4
`characterPolynomial` whenever the evaluated quaternion has unit norm.
All raw spectator coefficients remain in the constructed polynomials.

These two modules establish evaluation identities. The new modules above
supply the separate coefficient-probe and sphere-ideal proofs needed for
Haar use. Local character Gram channels are now proved above. Their physical
interface realization, link-local gluing, the physical operator gap and
continuum passage remain open.

Both new modules passed focused monitored one-worker 20 GiB checks: 33 printed
axiom gates, all within `{propext, Quot.sound}`, no errors/warnings. No new
sorry, analytic premise, numerical oracle, or raised proof limit; no full audit.

**Retained algebraic component: actual symmetric-power representations.**
[`SU2QuaternionTensorPowerAction.lean`](lean/YMGap/Continuum/SU2QuaternionTensorPowerAction.lean)
lifts the existing Hamilton-quaternion fundamental matrix to every finite
tensor degree. Composition, identity, inverse and the adjoint identity are
proved; rational unit quaternions preserve the explicitly positive Hermitian
form. The full tensor power is not presented as an irreducible character.

[`SU2QuaternionSymmetricPowerAction.lean`](lean/YMGap/Continuum/SU2QuaternionSymmetricPowerAction.lean)
proves that this action preserves symmetric tensors and reconstructs every
such tensor from its `n+1` explicit complex coefficients. The resulting
`symmetricAction` is complex-linear, obeys actual quaternion multiplication,
and preserves its inherited Hermitian form. These are structural proofs for
every degree, with no large assignment enumeration or binomial square roots.

The trace identification is now proved at evaluation and arbitrary-insertion
Haar levels above. Resolution and gluing of the literal interface kernels
remain open. The representation is over rational unit quaternions; it does
not itself supply compact-group completion. Neither slab reflection positivity
nor a physical spectral gap is claimed. The original signed-Haar law is unchanged.

Both new modules passed focused monitored one-worker 20 GiB checks: 42 printed
axiom gates, all within `{propext, Quot.sound}`, no final errors/warnings.
No new sorry, analytic premise, rate or raised proof limit; no full audit.
The dependency target also completed. Its first invocation inherited an old
32 GiB repository default; the target was then repeated with an explicit
20 GiB override. The new-module checks used 20 GiB throughout.

**Retained direct-route result: the original form uses the literal reflected
observable.**
[`BF4ExactSlabReflectedObservableHaarForm.lean`](lean/YMGap/Continuum/BF4ExactSlabReflectedObservableHaarForm.lean)
proves `Q(c) = Haar(F_c * (H * theta(F_c)))` for the ORIGINAL signed slab
quadratic. Here `F_c` is the heat-dressed lower observable, `H` is the product
of the 24 actual face heat polynomials, and `theta` permutes the physical
link blocks and inverts the time links. The bilinear version also allows
different arbitrary signed coefficients on the two sides.

`lowerObservable_reflection_insert` proves the upper/lower reflection pin
with every spectator polynomial supported on the same 116 links retained.
The proof transports each all-spin plaquette word and its heat coefficient,
then the whole lower face list, then the observable sum. Scope: every
rational w and every cutoff K, extent one. It does not assume positivity.

**Next:** a positive reflected-channel resolution of the actual interface
heat kernels and its composition on the literal link geometry. The displayed
Haar identity is not itself a positivity theorem. Exact-law physical time,
the completed gap and volume/spacing/continuum control remain open.

Verification: the new module passed seven axiom gates. The two small API
additions in each dependency were checked too: 15 gates in the reflection
module and 11 in the factorization module. All three focused monitored
one-worker 20 GiB checks passed without final errors/warnings, within
`{propext, Quot.sound}`. No new proof hole, analytic premise, numerical oracle
or raised proof limit; no full build/audit.

**Retained direct-route result: the interface sum is an exact local heat
product.**
[`BF4ExactSlabInterfaceHeatProduct.lean`](lean/YMGap/Continuum/BF4ExactSlabInterfaceHeatProduct.lean)
proves finite distributivity over the existing bounded label enumeration.
`interfaceHeatInsertion_eq_product` identifies the original global
interface insertion with the product of its 24 face heat polynomials,
each retaining the actual plaquette holonomy and `coeffW w spin` weights.
The proof works symbolically at every cutoff; it does not enumerate the
`(K+1)^24` global boundary states.

`observableIntegrand_eq_product` retains arbitrary signed lower and upper
observables before integration. `exact_bilinear_eq_productHaar` and
`exact_quadratic_eq_productHaar` then give the ORIGINAL signed forms with
this exact local heat product. Scope: every rational w, every spin cutoff,
extent one. There is no new rate or positivity claim.

The next substantive step is a positive reflected-channel resolution of
these local face kernels and its composition on the actual slab geometry.
Neither positive heat coefficients alone nor the finite product identity
asserts reflection positivity. Physical time, the completed exact-law gap,
volume/spacing control, continuum QFT and the all-group target remain open.

The new module passed all 10 printed axiom gates; the small fold API addition
in its factorization dependency was also checked (9 gates in that module).
Both focused monitored one-worker 20 GiB checks passed without errors or
warnings, within `{propext, Quot.sound}`. No new proof hole, analytic premise,
rate constant, numerical oracle or raised proof limit; no full build/audit.

**Retained direct-route result: every signed boundary form is a literal
action-side Haar integral.**
[`BF4ExactSlabWeightedFaceFactorization.lean`](lean/YMGap/Continuum/BF4ExactSlabWeightedFaceFactorization.lean)
proves coefficient-probe equality between the original heat-weighted
72-face network and its lower/interface/reflected-upper polynomial
product, retaining all 116 link coordinates. The equality survives every
additional polynomial insertion. All original heat coefficients and
signed Haar contractions are retained.

[`BF4ExactSlabObservableHaarForm.exact_bilinear_eq_haar`](lean/YMGap/Continuum/BF4ExactSlabObservableHaarForm.lean)
then sums arbitrary signed boundary coefficients into the lower and upper
polynomials. The ORIGINAL exact slab bilinear form is precisely
`Haar(lowerObservable * (interfaceHeatInsertion * upperObservable))`.
`exact_quadratic_eq_haar` specializes to the same observable on both sides.
This holds for every representation cutoff and every rational heat
coordinate, at extent one. It is algebraic, not a coupling-uniform estimate.

This is a proved connection within the signed-Haar law, not an identity
with the positive conditional model. Reflection positivity of the displayed
integral, a physical time operator and its completed gap still require
proof. The next algebraic step is to resolve the literal interface heat
insertion into reflection-positive channels while keeping these observable
and link-coordinate identifications.

Both new modules passed focused monitored one-worker 20 GiB checks, with
all 15 printed axiom gates within `{propext, Quot.sound}` and no final
errors or warnings. No new proof hole, analytic premise, rate constant,
or raised proof limit; no full build/audit/guard run.

**Retained obstruction: the discrepancy survives cutoff removal and completion.**
The literal six-face cube row supplies the explicit floor
`delta(w) = (coeffW w 1)^6 / (1 + (coeffW w 1)^6) > 0` for every `w>0`.
The signed-Haar vacuum-delta quadratic is exactly `1`, while the positive
normalized value is at most `1-delta(w)` for EVERY representation cutoff
`K>=1`. The new
[`BF4ExactPhysicalCutoffLimitSeparation.lean`](lean/YMGap/Continuum/BF4ExactPhysicalCutoffLimitSeparation.lean)
passes this bound to the original normalized `CReal` limit for `0<w<1`;
[`BF4PhysicalCubeExactActionFence.lean`](lean/YMGap/Continuum/BF4PhysicalCubeExactActionFence.lean)
pins it to the literal root's squared norm in the existing reflected
completion at `w=1/400`. That root cylinder is not the stationary vacuum.
The floor is cutoff-independent but explicitly coupling-dependent.

The physical frontier requires an exact-law construction or a separately
proved nonidentity observable/norm comparison, with physical time pinned
to that same law. No such replacement follows from the conditional gap or
from this obstruction. Volume, spacing, continuum QFT and all-group
passage remain open. Neither cutoff removal nor completion repairs the
literal identity.

Both new modules passed focused monitored one-worker 20 GiB checks, with
all 17 printed axiom gates within `{propext, Quot.sound}`. The untrusted
exact-rational pilot checked 404 algebraic implications; Lean separately
proves the physical bound and the displayed anchor constant. No new proof
hole, analytic premise, or raised proof limit; no full build/audit/guard run.

**Retained conditional result: decay and uniqueness for the same operator.**
At `w=1/400`, extent one, the completed reflected conditional operator
has strict norm contraction, correlation decay, and vacuum isolation.
For every completed `x` orthogonal to the constructed stationary vacuum,
Lean now proves

```text
||T^n x||_E^2 <= (q*q)^n ||x||_E^2
(1-q) ||x||_E^2 <= ||x||_E^2 - <T x,x>_E,   1-q > 0.
```

Completed Cauchy--Schwarz gives squared-correlation decay, including a
direct bound on the existing `centeredCubeCorrelator` with its exact
conditional-moment identity. A fixed vector in the vacuum complement must
be zero; two fixed vectors with the same vacuum pairing coincide. Thus the
constructed positive-norm vacuum is uniquely stationary at its own vacuum
pairing. This does not assume a unit vacuum or construct an arbitrary-real
scalar decomposition of every vector.

The proof applies the marginal gap at `P x`, obtaining
`M(Px,P^2 x) <= q M(Px,Px) <= q^2 M(Px,x)`, then uses the original reflected
pairing and the already explicit approximation rates. No operator or norm
is replaced. See
[`BF4PhysicalCubeCompletedReflectedDecay.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedDecay.lean)
and [`BF4PhysicalCubeVacuumIsolation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeVacuumIsolation.lean).
Both focused monitored checks passed all 15 printed axiom gates within
`{propext, Quot.sound}`. No new proof hole or analytic premise; no full
build/audit/guard run.

**Input: the constructed rate survives both completions.**
`BF4PhysicalCubeCompletedMarginalGap.cofinalSectorGap` supplies the existing
sector-only limit interface on the explicit schedule `max(request,K0(w))`.
For every fixed `0<w<=1/2`, the resulting completed marginal form gap and
conditional-iterate norm decay use the original `q(w)`.

At `w=1/400`, extent one, positivity gives
`||P x||_M^2 <= q(w) <P x,x>_M`. The exact comparison identities identify
these quantities with the reflected transfer form and reflected norm.
`BF4PhysicalCubeCompletedReflectedGap.completed_reflected_form_bound`
therefore proves

```text
<T x,x>_E <= q <x,x>_E,   0 < q < 1,
for EVERY x in the completed reflected vacuum complement.
```

There is no supplied gap, vector-dependent prefactor, or rate loss. The
argument uses the actual vacuum sector, never the reducible full carrier;
it does not pretend the marginal and reflected norms are equal.
See [`BF4PhysicalCubeCompletedMarginalGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedMarginalGap.lean)
and [`BF4PhysicalCubeCompletedReflectedGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedGap.lean).
Both focused monitored checks passed all 13 printed axiom gates within
`{propext, Quot.sound}`. No new analytic premise or proof hole was added;
the full build/audit/guard was not run.

**Input: a constructed cutoff-uniform strict centered form bound.**
At extent one, for every fixed `0<w<=1/2`, Lean constructs a rational
`q(w)` and an explicit onset `K0(w)` such that

```text
0 < q(w) < 1
|P_K(f)| <= q(w) * N_K(f)
    for EVERY K >= K0(w) and EVERY stationary-mean-zero f.
```

`P_K` is the original physical matrix quadratic and `N_K` its original
stationary squared norm. For the fixed head B=1404, the existing persistent
edge floor F(w) and loop-free path scale S(w) give the computed constant
`C(w)=S(w)/F(w)`. The new proof controls the head by the original full
energy; summing costs only the stationary mass <=1. The previous tail
absorption then gives `N_K(f)<=(1+3*C(w))*E_K(f)`, and exact rational
algebra produces `q(w)=(1+6*C(w))/(2+6*C(w))`.

The rate and onset **depend on w**. This is not a coupling-, volume-, or
lattice-spacing-uniform physical gap. It supplies the completed result
above. Exact action/geometric time, the continuum vacuum and QFT,
thermodynamic/continuum passage and Clay remain open.
See [`BF4PhysicalCubeAnchoredHeadBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeAnchoredHeadBound.lean)
and [`BF4PhysicalCubeCutoffUniformGap.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCutoffUniformGap.lean).
Both focused monitored checks passed all 20 printed axiom gates. The exact
untrusted path/algebra pilot passed 1,089 rooted bounds and four rate identities;
no numerical BF4 spectral oracle was used.

**Input: a fixed-head, root-anchored energy inequality.**
At extent one, for every `0<w<=1/2`, every spin cutoff `K>=1404`, and
every coefficient `f` of zero stationary mean, Lean proves

```text
N_K(f) <= E_K(f) + 3 * N_K(head_1404(f - f(vacuum)))
```

Here `N_K` is the original stationary squared norm and `E_K` is the
original directed physical Dirichlet energy, exactly twice `N_K-P_K`.
The proof establishes an **uncentered** tail rate `1/4`, absorbs the
mixed block by Gram positivity, and subtracts the root value without
changing the energy. Neither unit sector mass nor a strict head rate is
assumed. The head cutoff stays fixed while K grows.

The previously missing fixed-head constant is now supplied by the result
above. This absorption theorem alone does not supply it. See
[`BF4PhysicalCubeTailAbsorption.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTailAbsorption.lean).
The focused monitored Lean check passed all 12 printed axiom gates;
the exact untrusted algebra pilot passed 29,141 positive-block checks.

**Input: the actual centered new-tail form is uniformly small.**
For any positive rational epsilon, take the explicit old cutoff
`B=1400+epsilon.den`. At extent one, for every `0<w<=1/2` and every later
cutoff K>=B, Lean proves

```text
exactCenteredNewTailTrace(B,K) <= epsilon
centeredGram_K(tail,tail) <= epsilon * stationaryNormSquared_K(tail)
```

The second bound holds for **every** literal new-tail coefficient vector,
not just a probe. The proof injects each radius-M shell into `(M+1)^6`
six-label codes and partitions the original conditional diagonal sum
exactly by radius. Genuinely new indices have radius greater than B,
so the Gaussian radial estimate below bounds the existing old/new-block
trace. Its centered stationary subtraction only decreases that trace.

This discharges the trace input of the existing head--tail compiler.
That earlier compiler still gives rate `q+epsilon` from a sufficient
centered head rate q. The newer anchored route above now proves a strict
full rate without needing that comparison.
Exact action/geometric time, vacuum uniqueness and
volume/spacing/continuum passage also remain open. See
[`BF4PhysicalCubeHighLabelTrace.lean`](lean/YMGap/Continuum/BF4PhysicalCubeHighLabelTrace.lean)
and [`BF4PhysicalCubeNewTailTraceBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeNewTailTraceBound.lean).
Both focused monitored checks passed, all 18 gates within
`{propext, Quot.sound}`; no new sorry or full-tree audit.

**Input: Gaussian suppression of actual high-label self-return.**
At extent one, every member of the original vacuum sector whose largest
cube label is M>=1400 satisfies, for every admitting cutoff and `0<w<=1/2`,

```text
P_K(source,source) <= 4096*(M+1)^6*w^floor(M^2/72)
```

The theorem concerns the existing `centralPhysicalConditionalKernel`;
cube support and parity are derived from canonical sector membership.
The proof combines the complete boundary comparison below with an exact
six-dimensional heat factorization and the quadratic Casimir decrease.

The degree-12 radial envelope
`R_w(M)=4096*(M+1)^12*w^floor(M^2/72)` also has a proved successor ratio at
most 1/2 beyond 1400. Every finite tail starting at N>=1400 is at most
`2*R_w(N)`. The explicit threshold `N(epsilon)=1401+epsilon.den` makes
every such tail at most epsilon, uniformly for `0<=w<=1/2`.
The six-label counting/trace connection is now proved above. Sufficient
head control remains open; scalar summability or a small tail alone is not
an all-vector spectral gap. See
[`BF4PhysicalCubeGaussianReturn.lean`](lean/YMGap/Continuum/BF4PhysicalCubeGaussianReturn.lean).
All 21 gates passed in its focused monitored check; the reused heat-product
module was also checked. No new sorry or full-tree audit.

**Input: full boundary summation and an actual diagonal/row
comparison.** At extent one, for every representation cutoff and explicitly
for `0 <= w <= 1/2`, Lean proves

```text
boundaryOverlap(source,target) <= 4096 * boundaryHeat(difference(source))
```

The proof factors an upper estimate over the original 24-coordinate
enumeration: twelve active heat tails each cost at most 2, and twelve
inactive labels are forced zero. Combining this with the balanced physical
move below gives, for every bounded common-parity cube source and K>=2,

```text
H(balanced(source)) * P_K(source,source) <= 4096 * H(source)
```

Here H is the actual half-state heat product, and P_K is the original
normalized reflected joint divided by its own stationary marginal; the
common partition cancels exactly. This is not a replacement dynamics or a
state-uniform transition floor. The Gaussian return bound and radial
summability are now proved above; the actual trace connection and sufficient
centered head--tail control or weighted norm coverage remain open. Neither an all-vector
strict rate nor a geometric-time identification follows yet. See
[`BF4PhysicalCubeBoundarySumBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBoundarySumBound.lean).
The focused monitored check passed all 13 axiom gates within
`{propext, Quot.sound}`. No full-tree audit was run.

**Input: an all-state balanced physical move with quadratic Casimir
descent.** For a cube-supported common-parity state, let M be its largest
label. On each cube face replace s by
`2*(floor(2*floor(s/2)/3)+ceil(M/12))`. This computed target preserves every
minimal source difference-boundary channel, belongs to the actual vacuum
component, fits every original cutoff `K>=2`, and has a proved positive
entry in the original physical kernel. Its excess radius above 11 contracts
by `5/6`. Writing C for the sum of the six `c4(s)=s*(s+2)` values
(four times the SU(2) Casimir), Lean proves

```text
72*C(target) + M^2 <= 72*C(source)                 when M >= 1400
864*C(target) <= 863*C(source)                    when M >= 1400
```

The proof uses a sum-of-squares reserve at a maximal label to pay the
rounding and common offset. These are **label-energy rates, not operator
or mass-gap rates**. The boundary-sum and diagonal/row comparison is now
proved above; the resulting weighted norm or centered head--tail estimates
remain open. See
[`BF4PhysicalCubeBalancedDescent.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBalancedDescent.lean)
and [`BF4PhysicalCubeBalancedCasimir.lean`](lean/YMGap/Continuum/BF4PhysicalCubeBalancedCasimir.lean).
Both modules passed focused monitored checks; all 46 printed axiom gates
are within `{propext, Quot.sound}`. No full-tree audit was run.

**Retained route correction:** a **cutoff-uniform direct inward-mate transition
floor is impossible** at each fixed `0 < w <= 1/2`, including `w=1/400`.
In six-face coordinates, take

```text
source       (2k+14, 0, 0, 0, 0, 0)
inward mate  (2k+13, 1, 1, 1, 1, 1)
competitor   (2k+12, 2, 2, 2, 2, 2)
```

Both targets have the same complete boundary mask against the source.
Their SU(2) dimension/Casimir comparison gives, for every `K >= 2k+14`,
`P_K(source,mate) <= w^(4k+2)` for the **original normalized physical
conditional kernel**. The sources belong to the actual vacuum component;
an explicit cofinal tolerance modulus proves the no-floor theorem. See
[`BF4PhysicalCubeInwardMateCompetitor.lean`](lean/YMGap/Continuum/BF4PhysicalCubeInwardMateCompetitor.lean)
and [`BF4PhysicalCubeInwardMateNoUniformFloor.lean`](lean/YMGap/Continuum/BF4PhysicalCubeInwardMateNoUniformFloor.lean).
This does **not** refute a full-operator gap or the proved averaged traffic
bounds. The analytic frontier remains weighted norm coverage/Poincare,
without assuming a uniform probability for the single selected mate edge.
Both modules passed targeted monitored checks; all 28 printed axiom gates
are within `{propext, Quot.sound}`. No full-tree audit was run.

**Previous positive result:** the constructed excitation has a **two-sided strict
relative response** for the SAME completed physical transfer:

```text
l * ||d||_E^2 <= <T d,d>_E <= q * ||d||_E^2,  l > 0, q < 1
```

The new full-space estimate is
`<x,test>_E^2 <= <T x,x>_E * ||test||_marginal^2` for every completed
reflected vector x and every finite cube test. It uses the original marginal
norm on the right, not the weaker reflected norm. Dense physical
Cauchy--Schwarz and the same-object pairing limits prove it without a gap
assumption. Dense tests then show that zero response forces x=0, so the
completed transfer kills no nonzero vector. These are not bounds away from
zero uniformly over vectors, nor bounds away from the vacuum eigenvalue one.

For `d = T root - root`, let delta be the existing positive probe-pairing
floor, C the computed marginal squared-norm ceiling of that probe, U the
existing squared-norm ceiling for d, and eta its proved positive deficit.
The displayed rates are explicit rational data:
`l = delta^2/(C*U)` and `q = 1 - eta/U`. They are proved for **this one
excitation**, not for every centered vector. See
[`BF4PhysicalCubeMixedTestBound.lean`](lean/YMGap/Continuum/BF4PhysicalCubeMixedTestBound.lean)
and [`BF4PhysicalCubeExcitationResponse.lean`](lean/YMGap/Continuum/BF4PhysicalCubeExcitationResponse.lean).
All 25 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is fixed `w=1/400`, extent one. A common dense q<1,
a unit-normalized canonical geometric-time probe, vacuum uniqueness, and
volume/spacing/continuum control remain open.

**Completion bridge:** the **common dense form bound and the bound on the entire
completed reflected vacuum complement are equivalent, with exactly the same
rate `q`**. The dense side uses the original centered physical presentations;
the completed side is not restricted to the older marginal-sector image.
The proof passes both the norm and transfer pairings through the constructed
approximants, using explicit moduli and no choice of quotient representatives.
See `dense_form_bound_iff_completed` in
[`BF4PhysicalCubeDenseFormClosure.lean`](lean/YMGap/Continuum/BF4PhysicalCubeDenseFormClosure.lean),
with represented pairing continuity in
[`GNSRepresentedApproximation.lean`](lean/YMGap/Continuum/GNSRepresentedApproximation.lean).
All 17 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is fixed `w=1/400`, extent one. **No common `q < 1` is
constructed:** that dense analytic estimate, geometric-time identification,
and the volume/spacing/continuum passage remain open.

**Previous result:** a **strict, quantitatively nonzero excitation in the actual
completed vacuum complement**. Define `d = T root - root`; stationarity gives
`<Omega,d>_E = 0` exactly. If `delta = twoStepFloor` is the physical positive
pairing floor below, and `P,R` are computed squared-norm ceilings for the
fixed probe and root representatives, Lean proves

```text
alpha = delta^2 / P > 0
eta   = alpha^2 / (2R) > 0
alpha <= <d,d>_E <= 2R
<T d,d>_E + eta <= <d,d>_E
```

The short argument is quantitative Cauchy--Schwarz, self-adjointness and
`||T x - x||_E^2 <= 2 * (<x,x>_E - <T x,x>_E)` on the full completed
carrier. See
[`BF4PhysicalCubeDissipation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeDissipation.lean)
and [`BF4PhysicalCubeStrictExcitation.lean`](lean/YMGap/Continuum/BF4PhysicalCubeStrictExcitation.lean).
All 31 printed axiom gates passed in targeted monitored checks; no full-tree
audit was run. Scope is still fixed `w=1/400`, extent one. This is **one
vector's strict deficit**, not a uniform relative bound for every vector,
a normalized positive-response probe for the canonical geometric-time root,
vacuum uniqueness, or a continuum gap.

**Physical input:** the **actual completed physical transfer is not the
identity**. A three-state argument witnesses the movement:

```text
single-face twice-spin-two probe -> fundamental cube -> root
           positive edge floors at every cutoff K >= 2
direct probe--root entry = 0, by incompatible SU(2) triangles

<root, probe>_E = 0
<T root, probe>_E >= twoStepFloor > 0
therefore T root != root
```

The positive floor is an explicit product of heat weights and the actual
normalization floor, at fixed `w=1/400` and extent one. The proof retains
one source term in the marginal pairing of the two conditional images,
with independent action and pairing cutoffs, and passes through both
existing completion limits. The exact same-object moment identity then
gives the displayed reflected pairing. No new dynamics is introduced.
See [`BF4PhysicalCubeTransferNonidentity.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTransferNonidentity.lean),
with its physical inputs in
[`BF4PhysicalCubeThreeStatePath.lean`](lean/YMGap/Continuum/BF4PhysicalCubeThreeStatePath.lean)
and [`BF4PhysicalCubeTwoStepPositivePairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeTwoStepPositivePairing.lean).
All 42 printed axiom gates passed in targeted checks; no full-tree audit
was run. Nonidentity is not a strict vacuum-complement bound, uniqueness
of the stationary vacuum, or geometric-time identification.

**Connected density result:** the actual centered physical images now approximate every
represented vector in the **whole completed reflected vacuum complement**,
with an explicit rate. This is at fixed `w=1/400` and extent one. The target
need not come from the old marginal-sector image: its only vector property
is orthogonality to the constructed stationary sector vacuum.

The proof combines the centering estimate below with Cauchy--Schwarz. Let
`U` and `R` be computed norm ceilings for the fixed vacuum and root, and set
`K = 2 * (1 + U*R/(64/65)^2)`. For any finite approximant `p` to `x`:

```text
||centered(p) - x||_E^2 <= K * ||p - x||_E^2
input tolerance = epsilon / K
output rate     = supplied Cauchy modulus(input tolerance)
```

[`BF4PhysicalCubeCenteredDensity.centeredDensity`](lean/YMGap/Continuum/BF4PhysicalCubeCenteredDensity.lean)
returns the presentations, modulus and error proof as data. Each approximant
also has its existing explicit centered Cauchy representative. There is no
choice of representatives from arbitrary quotient points. The generic
[`ScaledGNSCompletionEstimates.lean`](lean/YMGap/Continuum/ScaledGNSCompletionEstimates.lean)
preserves the actual normalized pairing and squared-distance modulus.
Both modules passed targeted checks and all 39 printed axiom gates; no full
repository build/audit was run. This is density, not a strict spectral gap.

**Connected centering estimate:** centering has a proved, base-independent error bound in
the **actual reflected norm**. For any finite sector presentation `p`, let
`r` be the root cylinder, `C(p)` its existing limiting correction, and `Omega`
the constructed stationary sector vacuum. The new full-space pairing identity
gives

```text
<centered(p), y> = <p, y> - C(p) <r, y>     for every completed y
||centered(p) - p||^2 = C(p)^2 ||r||^2
(64/65)^2 ||centered(p) - p||^2 <= <Omega,p>^2 ||r||^2
```

The denominator is the same physical root weight for every presentation
base. Thus this estimate has no coefficient-count or growing-cutoff factor.
It remains at fixed `w=1/400` and extent one. See
[`BF4PhysicalCubeCenteringPairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteringPairing.lean)
and [`BF4PhysicalCubeCenteringControl.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteringControl.lean).
The new density witness above supplies the explicit approximation assembly.

**Connected nonzero-vector result:** an explicitly centered single-face spin-two observable
has positive norm in the **actual reflected completion**. Its difference
boundary has zero root amplitude but positive probe amplitude, so one term
of the physical Gram sum-of-squares supplies a lower bound unchanged by
every rational root correction. The existing centered Cauchy sequence
passes that bound to the same completed vector. The witnessing rational is
`(64/65) * channelFloor(1/400) > 0`, where `channelFloor(w)` is an explicit
heat-weight product, not a coupling-uniform constant. This also proves
positivity of its connected conditional covariance at shifted index one
(reflected index zero). See
[`BF4PhysicalCubeSeparatedChannel.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSeparatedChannel.lean)
and [`BF4PhysicalCubeCenteredPositiveNorm.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCenteredPositiveNorm.lean).
A positive norm is not a strict transfer bound or a nonidentity theorem.

**Connected centering result:** the constructed sector vacuum's pairing equals the
original physical stationary mean on the **entire completed marginal
sector**. This identifies the existing moving rationally centered cylinders
with vectors in the new reflected vacuum complement. Their correlators are
proved equal to literal connected covariances under the original physical
law, using the same observable and conditional action, with the exact
one-insertion shift. See
[`BF4PhysicalCubeSectorCenteredRealization.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorCenteredRealization.lean).
This uses a rational head correction, not orthogonal projection along the
sector vacuum. Density now has the representative-supplied witness above;
the positive reflected norm is a separate physical-channel argument, not an
inference from a marginal lower bound.

**Connected vacuum result:** a stationary vector in the actual completed cube sector
is now constructed, with squared norm at least `64/65`. This is at fixed
`w=1/400` and extent one, not uniformly in the coupling. Finite component
indicators are zero/one observables with a common envelope; the original
physical tail modulus makes their prefixes Cauchy. Their global image is
exactly the cutoff-independent sector event, and finite stationarity passes
to the same completed transfer. The positive zero-labelled contribution and
partition ceiling supply the explicit norm floor. Self-adjointness then
makes this vector's orthogonal complement invariant, with the same positive
contractive operator. See
[`BF4PhysicalCubeSectorVacuum.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorVacuum.lean)
and [`BF4PhysicalCubeSectorVacuumNorm.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorVacuumNorm.lean).
This stationary vector is neither asserted to have unit norm nor proved to
be the unique fixed direction; a norm floor is not a spectral gap.

**Connected transfer result:** the actual transfer is proved positive, self-adjoint,
rational-linear and contractive on the **entire raw and reflected cube
completions**, at fixed `w=1/400` and extent one. Joint continuity of the
pairing passes the dense squared-distance bound to all vectors with constant
exactly `1`, without a normalization loss. Nondegeneracy and self-adjointness
give the vector-level linearity laws.

The same full-space map now **intertwines the entire existing completed
marginal sector**. The proof tests against dense cube vectors and moves the
transfer across the pairing; no new recoding producer or analytic premise is
assumed. All its natural-power moments on sector images equal the original
physical conditional moments, with the exact extra insertion from the
reflected form. See
[`BF4PhysicalCubeCompletedTransferLaws.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedTransferLaws.lean).

**Boundary of this earlier transfer construction:** constant `1` gives
nonexpansiveness, not a strict gap. The head/tail estimate and same-rate
completion theorem reported above now supply strictness on the reflected
vacuum complement. The nonzero root cylinder is not the stationary sector
event; its movement under the transfer is proved above. Identifying
conditional iterations with geometric Euclidean time and controlling
volume and spacing limits remain open. A Cauchy diagonal modulus is not
a physical decay rate.

**Connected completed-pairing result:** the comparison preserves the actual physical pairing
for **every vector in the completed marginal sector**, not only finite
presentations. The proof slows the existing shared sampler to pay the finite
cube admission cutoff and normalization modulus. Its admissibility is
preserved, so it still constructs the same physical conditional operator.
The two aligned finite forms are eventually equal and have the constructed
completed pairings as limits.

Consequently the mapped sector action is positive, self-adjoint and
E-contractive; its iteration moments equal the original physical moments
with exactly one extra operator insertion. See
[`BF4PhysicalCubeSectorCompletedPairing.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorCompletedPairing.lean).
That earlier `mappedTransfer` has the completed marginal sector as its domain;
the new `cubeTransfer` above acts on the whole reflected completion. Its full
rational-linear operator laws and marginal-sector intertwining are now proved,
as is the positive-norm stationary sector vector above. Geometric time and
a strict gap remain open. The result is at fixed `w=1/400`
and extent one; no continuum or coupling-uniform claim follows.

**Connected comparison result:** the existing completed marginal root sector maps to
the reflected cube completion at `w=1/400`, extent one. The map preserves
each finite presentation's literal observable and contracts squared distance
by the proved `E <= B` estimate; its representative Cauchy modulus is unchanged.
Conversely, every finite signed cube vector has a computed marginal-sector
preimage. A common spin cutoff, faithful state-code lookup and finite summation
produce it, including negative coefficients and repeated states. The preimage
has the same observable values on every state, and its reflected image is
exactly the original cube vector. See
[`BF4PhysicalCubeSectorComparison.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorComparison.lean)
and [`BF4PhysicalCubeSectorDensePreimage.lean`](lean/YMGap/Continuum/BF4PhysicalCubeSectorDensePreimage.lean).

The physical pairing pin now holds on the whole completed source as described
above. The completed transfer map with actual dense agreement and whole-source
intertwining are now proved. A dense preimage is not an inverse between
these two completed spaces.

**Connected completion result:** the literal cube-cylinder image has its reflected-norm
completion at the fixed anchor `w=1/400` and extent one. Two constructed maps
are inverses between this completion and the existing raw cube completion.
They keep the same finite-span sequences; the forward Cauchy modulus is
unchanged and the inverse uses the supplied modulus at `(64/65)*epsilon`.
The full completed pairing is proved to be the limit of the same dense
physical reflected pairings. See
[`BF4PhysicalCubeReflectedCompletion.lean`](lean/YMGap/Continuum/BF4PhysicalCubeReflectedCompletion.lean).

An elementary two-triangle argument also removes an unnecessary obstruction:
the two existing Cauchy moduli compute a null modulus directly, without choice.
The older claim that the legacy completion could not support this inverse
has been corrected.

**Connected dense realization:** the all-spin cube form is identified with the actual
completed physical pairing on its literal observable image. For arbitrary
finite signed lists `u,v`, the map `J` uses the existing exact state cylinders,
and the kernel-checked equality is
`E(Ju,Jv) = lambda * rawCubeForm(u,v)`.
At the fixed anchor `w=1/400`, its squared norm lies between `64/65` and `1`
times the raw reflected squared norm. The map neither creates nor removes
zero-norm vectors for these two reflected forms. See
[`BF4PhysicalCubeCompletedReflectedRealization.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletedReflectedRealization.lean).

**Connected operator result:** after the spin cutoff is removed, the actual conditional
operator `P` is self-adjoint and satisfies `0 <= <Px,x> <= <x,x>` on every
vector of the existing marginal-norm completion. The proof aligns both
insertions at the same finite cutoff using the existing adaptive sampler.

The constructive-real cubic identity now proves that this **same `P`** is
positive, self-adjoint and contractive for `E(x,y)=<x,Py>`. The same stationary
vacuum has E-norm one; its pairings, and the exact one-insertion-shifted
moments, are preserved. These are unconditional fixed-nome, finite-volume
results for `0<w<1`, using the constructed source-tail moduli. See
[`BF4PhysicalCutoffReflectedFormLaws.lean`](lean/YMGap/Continuum/BF4PhysicalCutoffReflectedFormLaws.lean).

The new completed root-sector map agrees with the conditional operator on
dense inputs; full intertwining remains open, as do geometric time and a strict gap. The construction
does not assume marginal completeness implies E-completeness; its scope is
the explicit-representative Cauchy quotient and the existing raw completion's
representative-family completeness.
No identification of the entire reducible carrier with the cube sector is
asserted; the vacuum-labelled root cylinder is not the constant stationary vacuum.

**Connected normalization result:** the all-spin raw cube form has its actual physical
cutoff-limit normalization. A single constructed `CReal` factor `lambda`
satisfies `normalized kernel = lambda * raw kernel`; its approximations are
exactly the reciprocals of the original finite partitions. The same identity
holds for every finite signed term list, including repeated states, after a
computed common cutoff. All limit constructions carry explicit moduli.

At the fixed anchor `w=1/400` and extent one, the checked partition ceiling
gives `64/65 <= lambda <= 1`, hence the corresponding two-sided comparison
of raw and normalized reflected squared norms. This is not a strict transfer
bound and is not a comparison with the marginal norm. See
[`BF4PhysicalCubeNormalizedKernelLimit.lean`](lean/YMGap/Continuum/BF4PhysicalCubeNormalizedKernelLimit.lean).

**Connected finite-transfer result:** the actual finite BF4 conditional operator acts on the
completion of its own reflected joint form, with a unit fixed stationary
vacuum. The proof uses the elementary identity
`P - P^3 = (I-P)P(I-P) + 2 P(I-P)P`: a positive contraction for the marginal
form `D` also contracts `E(a,b) = D(a,Pb)`. The latter is exactly the original
partition-normalized OS joint form; cancellation of the positive partition
also proves contraction of the full raw OS quadratic.

The canonical comparison `J` keeps the same Cauchy representatives and moduli,
decreases norms, intertwines the two completed actions, and preserves vacuum
orthogonality. Its exact moment identity is
`<Jx, P_E^n Jy>_E = <x, P_D^(n+1) y>_D`. This holds at each finite cutoff;
it neither asserts an inverse for `J` nor identifies macro iterations with
geometric time. See
[`BF4PhysicalJointFormTransfer.lean`](lean/YMGap/Continuum/BF4PhysicalJointFormTransfer.lean).

**Connected all-spin result:** the cube-sector raw reflected form has a
constructive GNS completion. Its states are exactly the union of the finite
canonical vacuum components for positive `w`; each state has a computed
admission cutoff. Explicit finite lists retain arbitrary signed rational
coefficients and repeated states. Their complete form is the original physical
boundary Gram at a computed common cutoff, not an assumed positive model.

The completed basis inner products equal the same raw physical kernel entries
at every cutoff beyond their saturation threshold. The vacuum-labelled root
has squared norm at least one and remains nonzero after completion. Finite
approximations and diagonal-limit representatives carry explicit moduli.
Completeness uses representative families with a supplied outer Cauchy modulus;
it does not select representatives from arbitrary quotient-valued sequences.
See [`BF4PhysicalCubeCompletion.lean`](lean/YMGap/Continuum/BF4PhysicalCubeCompletion.lean).

The kernel underlying this construction, at slab extent one, has an exact
heat-weight/Boolean-overlap formula. For each half, its 48 production
links reduce to twelve SU(2) triangle tests and twelve boundary-zero tests;
the fixed part contributes eight corner triangles. The original weights and
boundary enumeration are retained, with no auxiliary multiplicity left.

If both endpoint label bounds are `R`, the raw kernel entry stops changing
exactly at every cutoff `K >= 2R`. A computed cutoff gives each pair an explicit
stable rational entry. Every finite quadratic form of this single stable
kernel is realized by the original physical OS Gram at a computed common
cutoff and is nonnegative for `w >= 0`.

The repository already constructs a cutoff-removed conditional transfer on
the **marginal-norm completion**, using explicit stationary-source-tail data;
see
[`BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer.lean`](lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer.lean).
It fixes that completion's stationary vacuum and preserves vacuum orthogonality.
The remaining operator bridge is to the **reflected cube completion** above,
not a missing conditional-transfer construction everywhere. The common
normalization identifies forms, and the new one-step laws control the existing
conditional action in E. They do not yet identify the two reflected carriers
or geometric time. A transfer-fixed vacuum on the raw cube completion,
a uniform strict gap,
thermodynamic/spacing limits and continuum reconstruction remain open. The
nonzero raw vacuum-labelled root alone does not prove vacuum isolation.

**Exact sector:** at slab extent one, every positive rational weight parameter
`w` and every spin cutoff `K >= 1`, the canonical vacuum sector is **exactly**
the bounded six-face cube labellings with common parity. The constructive
inward-mate orbit stays in that sector and reaches vacuum within `K + 1`
genuine positive OS moves.

The key construction puts `|a-b|` on the boundary face between cube labels
`a` and `b`. All source, mate and fixed-link multiplicities are exactly one;
the complete production summand becomes an explicit positive heat-coefficient
product below the original OS kernel. Together with the earlier singleton
pins and parity constraints, this proves both directions of the classification.
The sector sets are nested in `K` and unchanged by positive `w`; their weights
are not. Every mate-invariant observable on the sector is constant.

The edge weights depend explicitly on the state and `w`. Successful-source
traffic coverage and a cutoff-independent norm-to-move estimate remain open;
positive connectivity does not establish either. Sector-set nesting alone
also does not establish norm or operator compatibility across cutoffs; the
new raw-entry saturation theorem supplies a separate, strictly weaker result.

The preceding quantitative result remains: the normalized sector OS flow carries at
least `448/5525` total traffic. Exact source-block Fubini connects it to the
proved `7/85` raw sector-demand fraction. Together with the same-object sector
energy embedding, this gives the positive central-face-parity Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost)` on the exact vacuum component.
These estimates are uniform in spin cutoff `K >= 1` at fixed coupling `1/400`
and slab extent one.
The missing reverse estimate must control every centered sector norm by move
energy with a positive cutoff-independent floor.

The latest checked path is already on that actual OS object.  Every successful
six-face inward-mate source gives a supported two-edge path in the normalized
symmetric OS joint kernel.  Its selected source traffic has total mass at
least `41/425`; exact production-target fibers have congestion bounded by
`globalInwardMateTransportCost`; and all complete sources that forget to the
same first OS edge now inject into distinct literal boundary--intertwiner
summands of that edge.  Consequently their **aggregate** first-edge traffic is
at most the actual OS joint capacity, without a volume- or cutoff-cardinality
loss.  The second edge is now complete too: exact production-target classes
partition all selected source traffic, those classes partition again by their
actual second OS edge, and the resulting loads sum exactly to the original
traffic.  Each second-edge load is bounded by
`globalInwardMateTransportCost` times its OS capacity.

For one concrete observable the answer is now positive.  The parity of
central lower face zero is reversed by every selected inward mate, and because
the intermediate parity is also Boolean, exactly one of the two path edges
changes it.  Lean proves without a triangle-inequality loss that the two
selected parity-gradient energies sum to the selected traffic and are
therefore at least `41/425`.  The complete first-edge energy is now embedded
in the full physical OS Dirichlet form: exact first-edge fibers make the
parity gradient constant, their aggregate traffic is bounded by the matching
OS capacity, and distinct realized edges inject into the Cartesian half-state
square.  The second-edge energy is now embedded as well.  Its exact
production-target and OS-edge partitions contribute no loss; only the already
proved `globalInwardMateTransportCost` congestion factor remains.  The active
contraction is now complete: the explicit cutoff-independent positive floor

```text
(41/425) / (1 + globalInwardMateTransportCost)
```

is bounded by the full physical OS Dirichlet energy of central-face parity at
every cutoff `K >= 1`.  Lean now centers that same Boolean observable with its
exact stationary mean, proves that deleting zero-marginal rows and columns
does not change its Dirichlet energy, and applies the exact
Dirichlet/transfer identity.  The centered vector has a strictly positive
physical norm and obeys the explicit one-observable form estimate

```text
|<f,Tf>| <= q <f,f>,
q = 1 - (1/2) * (41/425) / (1 + globalInwardMateTransportCost),
0 <= q < 1.
```

This is a real cutoff-uniform strict channel of the actual finite physical
transfer, but it is not an all-vector Poincare inequality.  For arbitrary
observables, the selected source-to-target oscillation is at most
`2 * (1 + globalInwardMateTransportCost)` times the actual physical OS
Dirichlet energy.  The proposed Type-level full-carrier coverage input is now
proved impossible.  The XOR parity of central-cube faces `0` and `39` is
unchanged by every simultaneous six-face inward mate, but after exact
stationary centering it has strictly positive physical norm already at cutoff
one (vacuum value zero, proved transverse-face value one).  Its selected
endpoint energy is exactly zero.  Hence
`GlobalInwardMateUniformEndpointCoverage` has no inhabitant.

This obstruction cleanly repoints the proof.  The full positive-row carrier
is already known to be reducible at cutoff two.  Lean now proves the first
sector bridge: a positive raw OS edge cannot leave the exact finite vacuum
component, so whenever an inward-mate source endpoint is in that component,
its common hub and mate endpoint are there too.  A finite-support Boolean
classifier now filters the global source enumeration exactly to those paths;
the resulting Type-level list is duplicate-free and its membership theorem is
an iff, not an assumed selector.  Restricting the partition-normalized traffic
to this list preserves nonnegativity and both proved OS edge-capacity bounds,
including the second-edge congestion factor. The global `41/425` demand floor
does not follow merely by restriction; the new sector bound is `7/85`.
The branch decomposition has now been localized
at the right level: over the exact finite list of full physical fields whose
lower restriction is in the vacuum component, all-target mass plus
first-stretched mass equals the genuine BF4 physical mass exactly.  The
bad-target support argument now needs no equality of boundary labels: the raw
OS kernel sums over those labels, so each field supplies its own positive
boundary summand.  A target preserving the reflected upper state therefore
has a two-edge path from the source lower state.  A target preserving the
lower state stays in the sector directly.  The resulting exact decomposition is
`sector physical mass = successful mass + one-sided bad mass + two-sided bad mass`.
The two-sided residual changes both half-states and is contained in the older
boundary-or-upper crossing list; no strict positive mass reduction is claimed.
The weighted localization is now proved too: every nonnegative function of the
actual lowered target passes through the inverse-fiber and target/root/size
sums, preserving the factor `384/425`.  Taking the exact sector indicator
bounds all internal bad mass by `384/425` of sector physical mass.  Exact
branch conservation then proves
`(41/425) * sector mass <= successful mass + escaping bad mass`.
The escaping mass counts only sources in the sector whose lowered targets
leave it.  Every such source is proved two-sided; two-sided targets that
remain inside the sector are already covered by the contraction.
That escaping mass is now absorbed. The physical degree-thirteen face
majorant has successive ratio at most `2/15625` at the anchor, hence its
all-cutoff one-face sum is at most `15625/15623`. Exact finite Fubini and
the corrected slab's embedding in the 96-face ambient corner box give
`Z <= (15625/15623)^96 <= 65/64`. Since the weight-one vacuum lies in the
sector, outside physical mass is at most `1/64`. Applying the same weighted
contraction to the complementary target event gives
`escaping bad mass <= (6/425) * sector mass`. Subtracting this from the
previous demand bound proves
`successful mass >= (7/85) * sector mass > 0`.
This is a fixed-volume, fixed-coupling result, not uniformity in beta or
lattice spacing.

The sector Dirichlet embedding is now proved without recounting any fibers.
Zero extension of a sector observable adds no physical energy: the exact
component has no crossing OS kernel entries, and zero-marginal rows vanish.
The full half-state energy of this extension equals the already-defined
canonical indexed sector energy. On every restricted path, the extension
agrees with the original observable at all three vertices. Thus the first
edge, second edge, and endpoint estimates restrict with their original
factors `1`, `globalInwardMateTransportCost`, and
`2(1 + globalInwardMateTransportCost)`.

The exact normalization handoff is now proved as well. The sector test is
constant within each fixed-physical source block, so filtering commutes with
the complete-source Fubini sum. The existing production source weights agree
termwise with the raw source weights, yielding
`sector total traffic = successful sector mass / Z`. Thus the traffic is at
least `7/85` times the partition-normalized sector-event mass and, using
`sector mass >= 1` and `Z <= 65/64`, at least `448/5525` absolutely.
The Boolean parity identity says its two path-edge energies sum exactly to
this traffic, giving the sector Dirichlet floor
`(448/5525)/(1 + globalInwardMateTransportCost) > 0`, without a factor-two
triangle-inequality loss. No source list, physical kernel, or normalization
has been changed.

The geometric test now has a checked answer at cutoff two. In
[`BF4PhysicalVacuumSectorInwardMateOrbits.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateOrbits.lean),
`targetLower_eq_mate_sourceLower` identifies the literal source endpoint map;
`cubeInwardOrbit_even_eq_parityCore` proves its all-cutoff parity reduction;
`cubeInwardOrbit_rootTime_eq_zero` gives an explicit vacuum-hitting time for
cube-supported common-parity states. On the canonical cutoff-two sector at
coupling `1/2`, `canonicalCutoffTwo_mate_invariant_constant` proves every
potential-mate invariant is constant. This is a geometric statement, not a
new weighted OS estimate at the anchor coupling.

The all-cutoff physical support implication is now proved in
[`BF4PhysicalHalfCubeSupport.lean`](lean/YMGap/Continuum/BF4PhysicalHalfCubeSupport.lean)
and
[`BF4PhysicalVacuumSectorCubeContainment.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorCubeContainment.lean).
`sharedBoundaryOfKernelNeZero` returns a witnessing nonzero boundary as data.
`vacuumSector_cubeSupportedCommonParity` propagates the singleton pins and
relative parities along the actual canonical component.
`vacuumSector_inwardOrbit_reaches_zero` applies the existing orbit formula to
every sector state; `vacuumSector_cubePairParity_zero` eliminates the
pair-parity obstruction there for every cutoff. These are fixed-geometry
support statements for arbitrary nonnegative `w`, not uniform spectral bounds.

Next: establish physical support and successful-source traffic on the required
potential moves, then prove quantitative norm-to-move coverage at arbitrary
cutoff. The converse inclusion of the entire common-parity cube family in
the canonical sector is not proved here. The orbit formula alone does not
establish weighted coverage or congestion bounds.
The Poincare compiler's algebra remains useful: a correctly formulated
sector-local coverage theorem with floor `kappa > 0` produces the rate shape

```text
q_all = 4(1 + globalInwardMateTransportCost)
        / (4(1 + globalInwardMateTransportCost) + kappa) < 1
```

uniformly for every cutoff `K >= 1`.  No such sector-local uniform coverage
theorem is presently claimed.

See
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSFirstEdgeLoad.lean).
The two-level second-edge partition is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSSecondEdgeLoad.lean).
The exact Boolean observable identity is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityDemand.lean).
The checked first-edge Dirichlet embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFirstEdgeEnergy.lean).
The checked two-level second-edge embedding is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParitySecondEdgeEnergy.lean).
The resulting explicit positive Dirichlet floor is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityCoercivity.lean).
The stationary centering, positive-norm certificate, exact transfer identity,
and strict one-observable form rate are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap.lean).
The arbitrary-observable two-edge estimate and exact all-vector coverage
frontier are in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy.lean).
The conditional coverage-to-uniform-Poincare contraction is in
[`BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler.lean).
The exact XOR counterexample refuting its full-carrier coverage input is in
[`BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateEndpointCoverageObstruction.lean).
Positive raw-edge closure of the exact vacuum component and its application to
both inward-mate path edges are in
[`BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction.lean).
The exact finite-support classifier and duplicate-free sector-local source list
are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.lean).
The restricted partition-normalized traffic and its inherited first- and
second-edge capacity bounds are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalOSFlow.lean).
The exact physical-field sector event and its localized good-plus-bad branch
conservation identity are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.lean).
The stronger support theorem, allowing arbitrary boundary changes whenever
either half-state is preserved, is in
[`BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget.lean).
The exact three-way mass identity and residual containment are in
[`BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.lean).
The contraction against any nonnegative physical target function is in
[`BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateTargetWeightedContraction.lean).
Its sector specialization and exact escaping-mass demand bound are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemandResidual.lean).
The sharp physical partition ceiling is in
[`BF4PhysicalAnchorPartitionCeiling.lean`](lean/YMGap/Continuum/BF4PhysicalAnchorPartitionCeiling.lean).
The complementary-event comparison, leakage absorption, and positive `7/85`
sector demand are in
[`BF4PhysicalVacuumSectorInwardMateSectorDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorDemand.lean).
The exact zero-extension identity for the canonical indexed sector is in
[`BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorZeroExtensionDirichlet.lean).
The three unconditional restricted observable-energy comparisons are in
[`BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorObservableEnergy.lean).
The exact raw-to-normalized traffic identity, positive traffic floor, and
sector-parity Dirichlet consequence are in
[`BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateSectorNormalizedDemand.lean).

The current verified frontier joins a multiplicity-exact finite enumeration
of the root-first SU(2) cube source to a fixed-target contraction for every
certified first-stretched strand source.  Lean compiles the complete two-root
component union into three finite words:

- one connected rooted `Z^4` animal word in a carrier of size `625^n`;
- one exact physical strand-multiplicity word in a carrier of size `4^n`;
- one complete auxiliary-drop row word in a carrier of size at most `4096^n`.

At fixed root, peel size `n`, and lowered presented target, those words
reconstruct the source physical field and raw auxiliary assignment.  Thus any
explicit duplicate-free fixed-target source family has at most
`10240000^n` members.  Combining that injectivity with the exact per-source
anchor payment `anchorFaceCoefficient^n = (1/32000000)^n` gives the checked
finite-fiber estimate

```text
source fiber weight <= (8/25)^n * target weight.
```

See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode.lean),
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber.lean),
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight.lean).

The classifier domain is now also a literal duplicate-free heterogeneous
product over the twelve cube incidences.  SU(2) fusion-path permutation
invariance proves that every root-first local fiber has the same cardinality
as its production-order fiber.  Hence the complete function-valued source
enumeration, and its injective target-or-first-stretched image, have exactly
`cubeInwardMateSourceBoundaryProduct K physical` members.

The target and first-stretched branches are now extracted as separate
duplicate-free lists whose lengths add back to the exact production
cube-boundary multiplicity.  The off-cube completion no longer starts from a
full background that would later discard twelve cube coordinates.  Instead,
it explicitly filters the complete slab-link list to the complement of the
twelve cube links, enumerates only those production fibers, and combines them
piecewise with the certified root-first cube data.  Cube and off-cube lookup
laws prove that every coordinate comes from exactly its intended source.

The remaining immediate bridge is to enumerate the Cartesian product of the
first-stretched list and this off-cube list injectively, partition the result
by common lowered target, root, and peel size, and sum those fibers.  The
Cartesian family itself is now explicit, duplicate-free, and has exact length

```text
first-stretched cube count * off-cube production multiplicity.
```

Every member canonically compiles to a complete presented source and its raw
auxiliary payload.  That compiler is now proved injective on the enumerated
family: equality on cube coordinates recovers the certified classifier input,
while equality off the cube reconstructs the complement assignment.  The
resulting physical/raw source list remains duplicate-free.  The active edge is
now to attach each member's deterministic lowered target, root, and peel size,
then partition this list into the fixed fibers consumed by the existing
`(8/25)^n` contraction theorem.  That attachment is now explicit and
duplicate-free: every entry retains its upstream source as an injective key,
projects the existing flat inverse record, and has peel size at least two.
Reapplying the older defensive cube override is also proved to leave the raw
complete source unchanged.  The live edge is the actual dependent target/root/
size partition and its fixed-fiber witness compiler.  The lossless decidable
partition key is now proved: it records the root, size, lowered physical word,
every local face-order word, and every local lowered-auxiliary word.  Equal
keys reconstruct literal equality of the lowered physical function and
heterogeneous equality of the dependent presented assignment.  The live edge
was therefore the realized representative fibers and their
`PresentedAdaptiveRemovalWitness` compiler.  That compiler is now checked as
well: each realized fiber is duplicate-free, has size at most
`10240000^n`, and its complete anchor weight is at most `(8/25)^n` times
the representative's lowered-target weight.  The live edge is the exact
representative-fiber Fubini sum followed by contraction of the resulting
distinct lowered-target weights against the pure mate product.  The exact
Fubini step is now checked and the full first-stretched source weight is
bounded by the strict-rate-weighted sum of its realized lowered targets.  The
live mathematical edge is the target-side congestion/injection that contracts
this distinct target sum against the pure mate product.
The theorem does **not** yet give a physical transfer minorization, a
posterior-variance fraction, an OS transfer gap, or a continuum result.

Earlier in the same causal chain, the Casimir/heat payment for an inward mate
at the physical nome `w = 1/2` established that a parity-uniform six-face cube
has a non-vacuum even source heat product at most `64` times its inward mate's
heat product, while an odd source is at most `1/4096` times its inward mate.

These are
`sixHeatProduct_evenInwardMate_le_sixtyFour` and
`sixHeatProduct_oddInwardMate_le_oneOver4096` in
[`BF4PhysicalVacuumSectorInwardMateHeatBound.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateHeatBound.lean).

The local SU(2) fusion debt is now also exact and kernel-checked. Lowering two
positive incident labels preserves their Clebsch--Gordan ladder except for
its stretched top channel. At the production link-multiplicity level, every
source path is bounded by the inward-mate path count plus one explicit
stretched-channel continuation. See
[`BF4PhysicalVacuumSectorInwardMateFusionSupport.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionSupport.lean).

The local comparison now also transports across arbitrary physical incident
spin orderings, provided the two geometric permutation witnesses are supplied.
This is
`explicitValenceMultiplicity_physical_inwardMate_of_permutations` in
[`BF4PhysicalVacuumSectorInwardMateFusionReordering.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateFusionReordering.lean).
The generic finite-box incidence step is now closed as well:
`incidentPhysicalSpinsTwoFacePermutations` constructively moves any two
distinct incident plaquette IDs to the front of the source and mate words with
one shared residual word, and
`incidentPhysicalSpinsTwoFaceInwardMateLeAddStretched` immediately feeds
those witnesses into the production multiplicity inequality. See
[`BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateIncidentOrder.lean).

The cube-specific geometry is now closed too.  The twelve-entry production
table is compiled into exact corrected-slab numerical incidence: at every
cube-boundary link the two recorded selected face IDs occur, are distinct, and
exhaust the selected six-face support.  Thus the global six-face mate restricts
to the proved local two-face mate, yielding the actual corrected-slab
multiplicity bound with one explicit stretched continuation.  See
[`BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeIncidence.lean).

Those twelve local certificates now form one explicit global debt profile.
Lean proves that every link outside the cube boundary is unchanged and that
the boundary products obey
`product(source) <= product(mate + stretchedDebt)`.  See
[`BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile.lean).
This deliberately does not absorb the debts independently.

That finite product is now expanded exactly over Boolean words aligned with
the twelve attached links.  The all-target word is the pure mate product; all
nonempty stretched words sum to the named
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtExpansion.lean).

Every summand in that remainder now has a canonical constructive root.  Lean
computes the first stretched choice, proves its index lies in the attached
twelve-link incidence list, returns the corresponding geometric incidence as
data, and proves the root bit is `true`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot.lean).

The natural-number remainder is no longer opaque cardinality either.  Each
stretched local factor is the length of a literal accepted SU(2) auxiliary
fiber; Boolean words choose target or stretched fibers link by link; and the
flattened finite carrier has length exactly
`cubeInwardMateNonemptyStretchedRemainder`.  See
[`BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber.lean).

The raw expansion has now been sharpened at its mathematical source.  The
SU(2) ladder proof shows that if either changed face label is zero, every
source channel survives and the additive debt is exactly zero.  The active
remainder therefore retains a stretched fiber only when both incident cube
faces are positive; it again has an exact finite-carrier cardinality theorem.
See
[`BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveStretchedDebt.lean).

Every member of that active carrier now retains its assignment-membership
certificate, its first active position, the actual auxiliary labelling stored
there, and proofs that both incident physical face labels are positive.  Thus
the root required by the strand compiler is Type-level data rather than a
propositionally extracted witness.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness.lean).
The two positive root faces are now also realized as distinct literal
slot-zero strand-copy vertices on their common recorded link; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.lean).
For the stretched SU(2) vertex itself, the canonical resolution is now exact:
no strand joins the two input legs, while their strands occupy two disjoint
segments of the summed internal leg.  See
[`SU2StretchedTrivalentStrandContinuation.lean`](lean/YMGap/Continuum/SU2StretchedTrivalentStrandContinuation.lean).
The cube-root specialization now sends both literal face copies through those
canonical mates to distinct summed-channel ports and certifies the stored
auxiliary on the exact collapsed word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandContinuation.lean).
The resulting collapsed auxiliary can now be lifted constructively back across
the stretched vertex.  For every source word of length at most six,
`stretchedFusionWitnessLift_mem` inserts the forced first channel, shifts the
remaining internal coordinates, and proves that the resulting auxiliary is
accepted on the ordered source word; see
[`SU2StretchedFusionWitnessLift.lean`](lean/YMGap/Continuum/SU2StretchedFusionWitnessLift.lean).
That compiler is now specialized to every active cube-root carrier:
`rootSourceAuxiliary_mem_orderedSourceSpins` provides the literal accepted
source auxiliary, and `rootProductionSpins_perm_orderedSourceSpins` retains
the exact permutation from the physical production order; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootSourceWitness.lean).
The corresponding root-first order of literal plaquette IDs is now retained
as data as well.  It is duplicate-free, permutes the production incidence
list, and maps exactly to the accepted ordered spin word; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFaceOrder.lean).
The canonical ordered-chain termination and fixed-point-free terminal mate now
work for any such certified face presentation.  The generic compiler reindexes
every terminal to a literal incident plaquette and proves its mate lies on a
different face; see
[`CompactDualSlabOrderedLinkPhysicalStrandPairing.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkPhysicalStrandPairing.lean).
The one-element physical half-edge fiber now gives a constructive terminal at
any specified face position and strand slot.  At the active cube root this
produces two literal slot-zero terminals whose occurrences are exactly the two
previously named positive root copies; see
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootOrderedTerminals.lean).
Those selected terminals are now identified as full dependent ports at the
first canonical trivalent vertex, not merely by face ID.  The first channel is
proved to carry exactly the SU(2) stretched spin sum; its strand counts are
`ab = 0`, `bc = right`, and `ca = left`.  Consequently the two selected local
mates both land on the third leg but in distinct slots (`right` and `0`).  See
[`CanonicalLinkFirstVertexPorts.lean`](lean/YMGap/Continuum/CanonicalLinkFirstVertexPorts.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootFirstVertex.lean).
The outgoing channel is now constructively classified as physical at valence
three or genuinely internal at valence four through six.  Both root strands
are fed to the exact stop-or-same-slot-advance compiler; their complete paths
to physical endpoints are retained as data, and those endpoints are proved
distinct.  See
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootChannelBranch.lean).
Those endpoint terminals are now reindexed to the presentation-independent
global `(faceId, slot)` carrier.  Each root copy is proved to be the exact
source of a global strand edge, and the two retained path endpoints remain
distinct as literal global copies.  See
[`CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean`](lean/YMGap/Continuum/CompactDualSlabOrderedLinkGlobalFaceStrandEdge.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootGlobalEdges.lean).
The global edge compiler now also accepts a different certified face order and
fusion witness at each link.  It enumerates every local physical terminal,
forgets every endpoint to the common global carrier, and concatenates the
result into one heterogeneous edge list.  Replacing the root entry of any
explicit complete background assignment by the actual root-first witness puts
both retained root edges literally in that list.  See
[`CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFusionGlobalFaceStrandEdges.lean).
An ordinary accepted source assignment now embeds canonically into this
presented interface.  More generally, a rooted component of any heterogeneous
presented graph pulls back to exact partner closure at each ordered link.  For
the active debt root, Lean constructs the two rooted components generated by
the left and right stretched-channel strands and takes their Boolean union.
That union contains both literal root copies and is closed across every edge,
without asserting that the two components coincide.  See
[`CompactDualSlabPresentedFaceStrandSeedComponent.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandSeedComponent.lean)
and
[`BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateActiveDebtRootPresentedComponents.lean).
That ordered partner closure now compiles all the way through the existing
Kirchhoff strand-removal theorem.  At every link, the canonical edge drop is
proved equal to the global selected-copy count on the literal face occupying
that ordered position.  Consequently the two-root union constructs one common
lowered physical field and a complete accepted heterogeneous auxiliary
assignment over it; both distinct root-face labels decrease strictly.  See
[`CompactDualSlabPresentedFaceStrandComponentDrop.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDrop.lean).

The source-side local decomposition is now witness-faithful rather than only
an inequality of natural-number dimensions.  For any root-first ordered word
through valence six, Lean reads the actual first SU(2) channel of an accepted
source witness.  If it survives the inward mate, the same auxiliary is
accepted in the mate fiber.  Otherwise Lean deletes the unique stretched
first vertex, retains the resulting accepted collapsed witness and both
positive-spin proofs, and proves that reinsertion recovers the source exactly.
The resulting `inwardMateFusionWitnessPartition` is injective.  See
[`SU2InwardMateFusionWitnessPartition.lean`](lean/YMGap/Continuum/SU2InwardMateFusionWitnessPartition.lean).

That abstract partition is now specialized to every literal cube-boundary
link.  One certified face order exposes the two incident cube faces first; its
residual literal faces are proved unchanged by the global six-face mate.  Lean
therefore maps the actual ordered source fiber injectively into either the
actual ordered mated fiber or an accepted collapsed stretched witness, and it
packages every surviving target as a presented mated-link witness.  Exact
recovery still returns the original auxiliary.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition.lean).

The dependent twelve-link product is now constructed too.  A complete source
is a function whose coordinate type is the accepted root-first fiber of that
literal incidence.  Lean classifies all coordinates, recovers all original
auxiliaries pointwise, proves the complete classifier injective, and packages
the original tuple as one accepted presented cube family.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.lean).

That product now has a constructive global dichotomy.  A structural scan either
returns all twelve accepted mated witnesses or the first stretched incidence
with its actual positive two-face debt witness.  Forgetting the branch
reconstructs the complete classified assignment, so the source-to-branch map
remains injective.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched.lean).

The classifier's source-image invariant is now explicit rather than implicit
in its construction.  Every local output retains proof that its exact decoder
is accepted in the source fiber; the dependent product reconstructs a common
presented cube source.  The strengthened first-stretched branch keeps this
entire certified product and proves that its root output is exactly the stored
debt witness.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification.lean).

The certified cube family now extends to a complete slab presentation whenever
an explicit accepted full-slab background for the same physical field is
supplied.  A constructive finite lookup finds the unique recorded incidence
of each cube link, overwrites exactly those twelve entries with the certified
source witnesses, and leaves all off-cube entries unchanged.  See
[`BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation.lean).

At the certified first-stretched incidence, the retained positivity data now
constructs slot-zero terminals on the first two faces of that same root-first
witness.  Their terminal-pair edges have exactly the two literal cube-face
copies as sources, and both edges are proved members of the single completed
presented slab graph.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.lean).

Those two edges now seed a complete accepted peel.  Lean takes the Boolean
union of their constructive rooted components, proves it closed under the
actual partner at every independently presented link, and compiles the common
selection to a lowered physical field plus a complete accepted presented
assignment.  Both root-face labels decrease strictly; no connectivity claim
between the two roots is assumed.  See
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.lean).

That accepted drop now has an exact physical serialization and pointwise
weight payment.  Every endpoint of the heterogeneous presented graph is
proved to lie on a displayed physical face; the selected-copy multiplicities
form a legal repeated-face peel with an exact physical left inverse; and the
certified two-root word has length at least two.  At the production anchor,
the actual completed source entry is bounded by one
`anchorFaceCoefficient` factor for every word letter.  See
[`CompactDualSlabPresentedFaceStrandComponentWeight.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentWeight.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.lean).

The auxiliary drop is now serialized as well.  The lowered target retains each
certified face order, so the finite code pays no extra order coordinate.  Its
physical word plus link-local internal-drop words reconstruct the complete
source `(physical, raw auxiliary)` entry exactly, and every local word has
width at most three independently of cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentDropCode.lean)
and
[`BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean`](lean/YMGap/Continuum/BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.lean).

Zero internal-drop rows can now be erased and recovered exactly.  Every
retained row is charged injectively to a selected physical strand copy and one
of its four boundary links, so there are at most `4 * peelSize` nonzero rows.
More sharply, the complete volume-indexed row table inhabits a link-adaptive
Cartesian carrier: local conservation bounds every entry by the selected
physical mass incident on that link, all widths are at most three, and the
total incident mass is exactly `4 * peelSize`.  Consequently the auxiliary
carrier has size at most `4096^peelSize`, uniformly in slab volume and spin
cutoff.  See
[`CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentSparseDropCode.lean),
[`CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAuxiliaryRowBound.lean),
and
[`CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean`](lean/YMGap/Continuum/CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction.lean).

The physical geometry, multiplicity, and auxiliary inverse are now joined in
one adaptive code.  Its fixed-target injectivity and weighted fiber contraction
are checked, including component overlap without double counting.  What is
still open is the global regrouping: construct the actual finite enumeration
of certified first-stretched routes, partition it by the common lowered target,
root, and peel size, and sum those fibers into a cutoff-independent multiple
of the pure mate product.  The older coarse mixed target/debt Cartesian carrier
still does not itself provide a common accepted source presentation and is not
used as one.  Closing this regrouping would feed a genuine physical
mate-transition floor and then a rooted-subtree Hardy--Poincare or posterior
conditional-variance estimate.

An earlier plan tried to bound the whole new-cutoff self-return trace by a
small constant. Exact exploratory computation found that plan false already
at cutoff four: a single state has self-return about `0.71428`, and six
symmetric copies make the positive trace exceed four. This computation is a
route-selection diagnostic only; no floating-point value enters a theorem.

For the detailed live dependency map, see [`work_plan.md`](work_plan.md).
For the source-based group audit, see
[`audits/AUDIT-GROUP-DEPENDENCE.md`](audits/AUDIT-GROUP-DEPENDENCE.md). That
audit found that the strand machinery is hard-coded to the SU(2)
Clebsch--Gordan rule and that no source dependency bridge currently connects
the component chain to the generic `singleStep` obligation. Accordingly, this
README makes no claim that group dependence is closed.

## Trust and constructivity rules

The Lean development is intentionally stricter than ordinary Lean code:

- no Mathlib dependencies;
- no `Classical.choice`, excluded-middle shortcut, or `native_decide` in
  load-bearing proofs;
- constructive reals carry explicit Cauchy moduli;
- witness-bearing existence claims use data-bearing structures or sigma
  types;
- load-bearing declarations are inspected with `#print axioms`; the permitted
  project gate is `propext` and `Quot.sound` only;
- unproved obligations and conditional interfaces are recorded in
  [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md), rather than being described
  as completed physics.

Python and Rust may perform expensive searches or generate compact exact
certificates. They are **untrusted producers**: Lean must parse the resulting
finite data and independently check every semantic condition and inequality.

Read [`lean/AGENTS.md`](lean/AGENTS.md) before modifying any Lean file.

## Repository guide

| Path | Role |
| --- | --- |
| [`lean/`](lean/) | Lean 4 formalization and constructivity/axiom gates |
| [`lean/YMGap.lean`](lean/YMGap.lean) | Root import aggregator |
| [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md) | Open obligations and milestone evidence |
| [`work_plan.md`](work_plan.md) | Current causal roadmap and status |
| [`docs/outline.md`](docs/outline.md) | Technical specification |
| [`docs/context.md`](docs/context.md) | Mathematical motivation and constructive rationale |
| [`audits/`](audits/) | Read-only source audits of important claim boundaries |
| [`computations/`](computations/) | Untrusted Python/Rust exploration and certificate generation |
| [`tests/`](tests/) | Tests for computational tooling |
| [`formal/`](formal/) | Human-readable LaTeX development |
| [`visualizations/`](visualizations/) | Generated diagrams and exploratory figures |

## Building safely

Lean is pinned by [`lean/lean-toolchain`](lean/lean-toolchain). Builds must use
the monitored launcher; bare `lake build` and bare `lake env lean` bypass the
repository's crash safeguards.

```bash
# Full monitored Lean build
make lean-build

# Narrow target (preferred while developing)
python3 scripts/safe_lean_build.py --jobs 1 -- +YMGap.Continuum.ModuleName:olean

# Check one source and emit only its importable olean (parent directory exists)
python3 scripts/safe_lean_build.py --check lean/YMGap/Continuum/ModuleName.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/ModuleName.olean

# Monitored axiom audit
make lean-audit
```

See [`docs/lean-build-safety.md`](docs/lean-build-safety.md) for memory and
worker limits.

The auxiliary Python tools require Python 3.11 or newer:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -e ".[dev]"
make test
make lint
```

Other common targets are `make figures` and `make paper` (the latter requires
a working LaTeX installation with `latexmk`).

## How to evaluate a claim in this repository

Check all four of the following:

1. the exact theorem statement and its parameter range;
2. its printed axiom dependencies;
3. whether its hypotheses have concrete inhabitants, rather than only a
   conditional compiler;
4. whether the next bridge in [`lean/SORRY_LEDGER.md`](lean/SORRY_LEDGER.md)
   is still open.

A finite-cutoff theorem, a fixed-coupling clustering estimate, or a compiler
of the form “if certificate `C`, then gap” is valuable progress, but none is
by itself a continuum Yang--Mills mass-gap theorem.
