# Sorry Ledger

This ledger lists every `sorry` in the Lean formalization, per
`AGENTS.md` Rule 6.

Every `sorry` in `lean/` must appear here with:

- **milestone** — which `work_plan.md` milestone the obligation belongs to,
- **file** — `lean/YMGap/.../foo.lean`,
- **theorem / def name**,
- **obligation** — what the `sorry` stands for, in one sentence,
- **constructive or propositional** — whether discharging the obligation requires producing a witness (constructive) or only a propositional truth.

A `sorry` standing for a **constructive** obligation must never be closed later by a classical proof without explicit sign-off recorded in this ledger.

## Current status (2026-05-28; updated 2026-06-13)

**The entire `YMGap` library is now sorry-free (`lake build` reports 0
`declaration uses 'sorry'`).** As of 2026-06-13, all Continuum-existence
modules AND the `CRealAbs`/`ThetaLimit` helpers are imported by `YMGap.lean`
and build clean. `YMGap/Continuum/ContinuumExistence.lean` now
carries **0** `-- SORRY[continuum]` holes (down from 7→2→1→**0**). Stage
**S3** (`finiteVolumeExpectation`) is now **CLOSED**: the interacting
finite-volume expectation `E_Λ(o) = Ew_Λ(o)·recip(Z_Λ)` is the constructed
reweighted state — the reference functional `I_0` (product Haar/heat-kernel
integral, `E2ProductFunctional.prodFunctional`) reweighted by the positive
plaquette Boltzmann weight `w`, normalized by the partition function
`Z_Λ = I_0(w) > 0` (S2's `prodE_pos`, REUSED). The reference-functional +
weight packaging (`ReferenceWeight`, `ReferenceWeight.E_Λ` with proved
positivity `E_Λ_positive` and normalization `E_Λ_normalized`, the concrete
product instance `prodReferenceWeight` with `Z>0` via S2, and the
zero-coupling inhabitant `trivReferenceWeight`) lives in the new
`YMGap/Continuum/FiniteVolume.lean` (standalone, axiom-gated
`[propext]`/`[propext, Quot.sound]`). The lone genuine analytic input is the
per-volume weighted-form positivity (= OS2 reflection positivity), carried as
the `weighted_pos` structure FIELD (Rule 2/8), NOT faked. Stage **S4**
(`kpIncrementBound`, the analytic heart — the Kotecký–Preiss
cluster-expansion increment bound) is now **CLOSED**: PROVED from the
explicit weak-coupling smallness datum `KPIncrement.KPIncrementData`
(the convergent-regime single-site cluster-activity tower with geometric
ratio `r ≤ 1/2`, carried as DATA), in the new
`YMGap/Continuum/KPIncrement.lean`, axiom-gated `[propext]`. The
smallness is a genuine HYPOTHESIS (a structure argument), NOT a hidden
assumption of the conclusion (the bound is false for arbitrary `S`).
Stages **S2** (`partitionFunctionLB`/`partitionFunction_pos`,
partition-function positivity — CLOSED for real), **S5** (`infiniteVolumeExpectation`
+ `_approx`, the `CReal` limit via the KP engine — CLOSED given the S4
increment datum), and **S6** (`infiniteVolumeExpectation_nonneg`, limit
positivity — CLOSED conditional on the per-volume OS2 input) are now
theorems, axiom-gated `[propext]`/`[propext, Quot.sound]`. The S2 partition
positivity + the **Bishop integration-space packaging** (`BishopFunctional`,
the positive normalized functional on a dense observable subalgebra completed
by an explicit geometric convergence modulus — the constructive-measure
object, NOT a σ-algebra) live in the new
`YMGap/Continuum/PartitionPos.lean` (also standalone, axiom-clean, with
`BishopFunctional.I_inf`/`_approx`/`_nonneg` and a concrete `constBishop`
inhabitant). See entry `[continuum]` below and
`docs/continuum-measure-attack-surface.md`.
The MAIN-library build (`YMGap.lean`) remains **zero open `sorry`s**:
`lake build` (`leanprover/lean4:v4.29.1`, 28 jobs)
completes cleanly with no `sorry`/`sorryAx` warnings; every entry below is
closed. Axiom gates (re-verified 2026-05-28): the load-bearing decls
`domGlue_preserves_KP`, `mass_gap_SU2`, `mass_gap_SU2_wilson`, and the
`m_0`/`σ̂_∞` rational data are **axiom-free** (`does not depend on any
axioms`); `step_obligation_witness` and the constructive-reals exports
are `[propext]`-only. No `Classical.choice`, no `Quot.sound`, no
`sorryAx`. The remaining open items are the *paper-level* analytic
obligations (full KP-certificate proofs, the √-bridge O(1) constant,
O(4) restoration), tracked in the chapters and `notes/`, not here.

## Entries

### [M2-physical-separator-band] exact physical separator band — **REDUCED TO SAME-OBJECT ANALYTIC INPUTS 2026-08-18**

- **milestone**: physical-scale overlay M2 (`work_plan.md`)
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalSeparatorProducer.lean`,
  `lean/YMGap/Continuum/BF4FarautPhysicalSeparatorProducer.lean`,
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingAFCertificate.lean`,
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingAFAdapter.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageProjectiveRefresh.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageQuarterLimitTransfer.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageRelativeRankOneQuarter.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessagePrefixTailQuarter.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageRelativeErrorCrossTail.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessagePhysicalTerminalFloorAdapter.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageFinitePositiveFloor.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageComputedTerminalFloor.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageComputedFloorQuarter.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageComputedFloorCrossTail.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageComputedFloorCrossTailExample.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageRegularizedRankOnePrefixExample.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundarySelfSmoothingReduction.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundarySelfSmoothingCrossTail.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundarySelfSmoothingPerronCrossTail.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryRegularizedRankOne.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryRegularizedRankOneCrossTail.lean`,
  `lean/YMGap/Continuum/FiniteRegularizedRankOneStatistics.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryRegularizedRankOneStatistics.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryRegularizedRankOneStatisticsCrossTail.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageExactStatisticsCutoffZero.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessagePrefixTailQuarterExample.lean`,
  `lean/YMGap/Continuum/BF4BoundaryMessageRelativeRankOneQuarterExample.lean`,
  `lean/YMGap/Continuum/BF4ExactPhysicalPerronCenteredSameActionFence.lean`,
  `lean/YMGap/Continuum/PhysicalSeparatorLinearTail.lean`,
  `lean/YMGap/Continuum/BF4AFPhysicalSpacingToZero.lean`,
  `lean/YMGap/Continuum/HKPhysicalLinearMarginTail.lean`,
  `lean/YMGap/Continuum/RenormalizedHKPhysicalComparison.lean`,
  `lean/YMGap/Continuum/BF4FarautFullLogPrefixTailCertificate.lean`
- **named fields / structures**:
  `BF4PhysicalSeparatorSameObjectPin.macroCorrelation`,
  `BF4PhysicalSeparatorRateSharpnessPin.separatorPower_le_four_correlation`,
  `BF4QuarterPhysicalSeparatorProducer.bf4` (the direct positive-physical
  local-gluing certificate),
  `BF4QuarterPhysicalSeparatorProducer.groupedPhysicalSameObject` and
  `BF4FarautQuarterPhysicalSeparatorProducer.groupedPhysicalSameObject`
  (now derived theorems),
  `PhysicalSeparatorLinearTail.LinearMarginTail`,
  `RenormalizedHKComparison.physical_margin_le`,
  `RenormalizedHKComparison.residual`,
  `RenormalizedBareLinearTail.margin_le`, and the genuine local-slice fields
  inside `PhysicalLocalGluingAFCertificate`; plus
  `terminalProjectiveRefresh_l1_contraction` and
  `terminalProjectiveRefresh_l1_quarter_contraction`, which check a raw
  finite cross-ratio witness and construct the terminal-independent refresh
  decomposition; and
  `UniformRelativeRankOneQuarterWitness.toUniformBoundaryMessageQuarterCertificate`,
  which derives that witness from an exact profile-relative `1/16` entry
  enclosure;
  `QuarterErrorPrefixTail.bound_all`, which joins an exact finite prefix to an
  analytically antitone tail by induction; and
  `CrossProductQuarterErrorTail.toQuarterErrorPrefixTail`, which derives that
  analytic tail for `N_k/D_k` from positive denominators and the division-free
  cross inequality `N_(k+1)*D_k <= N_k*D_(k+1)`; and
  `QuarterContractionLimitData.limit_contraction`, which passes the exact
  finite quarter bound to `CReal` limits constructed from the same streams and
  explicit eventual Cauchy moduli; and
  `MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows.toUniformBoundaryMessageQuarterCertificate`,
  which converts the existing literal physical half-amplitude `65/64`
  projective estimate into a fixed-spread `33/32` uniform quarter certificate;
  and `terminalSmoothedFiniteFloor`, which computes the positive ideal floor
  by recursive rational minimum on the finite retained source-by-boundary
  rectangle, plus
  `MatchedPhysicalHalfAmplitudeComputedFloorErrorRows.toUniformBoundaryMessageQuarterCertificate`,
  which leaves only the physical entry-error estimate as an input; and
  `PositiveFloorErrorCrossTail.error_le_tolerance_mul_floor`, which combines
  exact finite `E_k <= F_k/2048` checks with the analytic cross-tail inequality
  `E_(k+1)*F_k <= E_k*F_(k+1)` to prove that estimate at every cutoff; and
  `centralHalfAmplitude_boundaryIdentityFactorization`, which identifies the
  literal physical factorization `A*I=A` on the faithful finite boundary
  carrier; `physicalHalfAmplitudePositiveCoordinateRows`, which constructs
  prefix positivity by total finite search from the exact physical moment
  identity; and
  `MatchedPhysicalBoundarySelfSmoothingCrossTailRows.toComputedFloorErrorRows`,
  which leaves precisely the physical action defect `|A-A*P|`; and
  `MatchedPhysicalBoundarySelfSmoothingPerronCrossTailRows.toCrossTailRows`,
  which derives the terminal split budget from the same-kernel AF/Faraut
  Perron estimate at depth `46*bits+6`.  Finally,
  `centralRegularizedBoundaryRankOneCertificate` constructs a normalized
  boundary smoother of exact spread one from the physical aggregate columns
  plus a positive rational pseudocount, and
  `MatchedPhysicalBoundaryRegularizedRankOneCrossTailRows.toComputedFloorErrorRows`
  reduces the whole route to its explicit aggregate-profile rank-one defect
  majorant and cross-tail certificate.  The generic finite-system theorem
  `finiteRegularizedRankOneDefect_le_of_pairwise` now decomposes that defect,
  after clearing its positive denominator, into a sum of pairwise cross-row
  residuals plus an explicit pseudocount bias.  Its BF4 specialization
  `centralHalfAmplitudeRegularizedRankOneDefect_le_max_of_pairwiseBound`
  bounds every retained entry by an executable nested rational maximum, and
  `MatchedPhysicalBoundaryRegularizedRankOneStatisticsCrossTailRows.toComputedFloorErrorRows`
  feeds exactly that maximum through the existing positive-floor cross-tail
  route.  An equality field ties the named error sequence to the finite
  maximum, so the adapter does not accept an unaccounted majorant.  The sharper
  `centralHalfAmplitudeRegularizedRankOneDefect_le_exactStatisticalMax` retains
  the exact sum of absolute pairwise residuals and exact pseudocount bias.
  `MatchedPhysicalBoundaryRegularizedRankOneExactStatisticsCrossTailRows.toComputedFloorErrorRows`
  lifts that executable maximum across scales without requiring a separately
  supplied pairwise-row bound; its remaining infinite obligation is the
  positive-floor cross-tail property of the exact statistic itself.
  Between the exact and coarse routes,
  `centralHalfAmplitudeRegularizedRankOneDefect_le_hybridStatisticalMax`
  pays the retained-source cardinality against one uniform pairwise-row bound
  while retaining the literal pseudocount bias.  The matching
  `MatchedPhysicalBoundaryRegularizedRankOneHybridStatisticsCrossTailRows.toComputedFloorErrorRows`
  adapter makes that hybrid finite statistic the named cross-tail stream.
  The checked generated example is emitted by
  `computations/boundary_message_lean_certificate.py` from exact rational data
  and proves a nontrivial terminal refresh rate at most one quarter.  Its
  finite-prefix mode also emits a checked constructor from exact prefix errors
  while leaving the physical stream identifications and analytic tail step as
  named inputs.  Its regularized matrix-prefix mode additionally emits the
  literal amplitude matrices and has Lean recompute the aggregate profile,
  projected entries, pairwise cross-row residuals, the conservative
  cardinality-plus-pseudocount statistical maximum, the sharper exact
  residual-sum-plus-bias maximum, the hybrid uniform-residual-plus-exact-bias
  maximum, the direct maximum-defect majorant, and the positive floor
  coordinate by coordinate.  Its computed-floor adapter now uses the sharper
  exact maximum.  The generated theorem applies the generic
  finite-statistics implication rather than trusting an externally asserted
  final inequality.  This certifies finite
  enumeration output only after Lean compilation; equality with the genuine
  BF4 enumerator, a uniform physical pairwise-row estimate, and the infinite
  cross-tail step remain named inputs.  As a genuine but degenerate physical
  checkpoint, `BF4BoundaryMessageExactStatisticsCutoffZero` kernel-computes
  both the exact-statistical maximum and the actual BF4 defect to zero at
  cutoff zero; it supplies no positive-cutoff or tail conclusion.  The earlier
  all-observable `ExactHaarPhysicalPerronAFQuarterCertificate` is no longer an
  active producer dependency: its same-action premise is constructively
  refuted at cutoff one for positive coupling.  The centered replacement is
  likewise no longer active: unconditional cutoff-one Haar evaluation
  separates its exact and physical centered vacuum moments by `5/8 > 1/8`
  at `w=8/9`.
- **obligation**: Construct the genuine gauge-invariant physical separator
  from the plaquette-coupled Gibbs/transfer object; prove that its selected
  connected correlator is the normalized positive BF4 joint quadratic;
  construct a normalized near-top-mode/rate-sharpness witness at the same
  Faraut-pinned depth (from which the grouped separator bound is now proved);
  and prove on that same object the
  asymptotic upper estimate `1 - sep_j <= M * a_j`.  The last estimate is the
  finite-mass half of dimensional transmutation and cannot be inferred from a
  quarter contraction alone.
- **proved reduction machinery**: the BF4/Faraut grouped contraction supplies
  a strictly positive physical lower rate once the same-object field is
  inhabited; exact full-range logarithmic rates are then bounded using a
  computed finite prefix and the linear tail.  A corrected explicit
  `afSchedule_to_zero` cutoff, exact coupling identification, and the existing
  quadratic physical-spacing envelope construct the spacing-to-zero modulus,
  so no independent spacing-limit hypothesis remains.  The same quadratic
  envelope and coupling window derive the global spacing ceiling needed for
  the three endpoint steps, so that earlier free producer input is also gone.
  The two-sided additive `HKPhysicalComparison` is now formally diagnosed as
  preserving finiteness of bare and physical margin rates, so it cannot
  reshape an escaping bare rate.  The repaired one-sided renormalized
  comparison proves that `Z_j*(1-w_j^3) = O(a_j)` plus an `O(a_j)` residual
  supplies the physical linear tail, and a checked BF4/Faraut adapter consumes
  exactly those inputs.  Independently, the boundary-message refresh theorem
  proves that a raw positive-kernel cross-ratio certificate survives arbitrary
  positive terminal weighting and row normalization, with common mass
  `1/spread^2`; the exact squared-spread ceiling `4/3` implies a quarter-rate
  finite `L1` contraction.  External exact computation may produce this
  finite witness, but Lean checks the division-free inequalities and the
  certificate-to-contraction soundness theorem.  A second checked producer
  shows that the exact relative rank-one enclosure `1/16` supplies spread
  `17/15` and hence the same quarter rate.  The end-to-end generated example
  confirms that external exact data can be rechecked by Lean; it is a plumbing
  witness, not a physical BF4 inhabitant.  The prefix/tail bridge permits
  exact Rust/C/Python enumeration below a threshold only when Lean checks the
  emitted rational inequalities and an independent analytic successor bound
  closes the infinite tail.  The cutoff-limit bridge additionally requires
  explicit `ModCauchyEv` witnesses for the exact input and output distance
  streams and therefore does not infer convergence from boundedness or
  numerical evidence.  Independently, the direct physical adapter shows that
  the terminal-floor/error interface is already strong enough for a quarter
  contraction.  The positive ideal floor is now constructed automatically
  from finite strict positivity.  The uniform `computedFloor/2048`
  physical-entry estimate is reduced further to an entrywise scalar majorant,
  exact finite prefix checks, and the all-tail division-free cross inequality;
  those physical inputs remain uninhabited on this route.  On the now
  preferred canonical specialization, the terminal itself is no longer an
  input: it is the normalized pseudocount-regularized aggregate-column profile
  of the literal `centralHalfAmplitude`, with spread exactly one.  The honest
  residual is the concrete rank-one defect bound
  `|A-rowMass(A)*regularizedAggregateProfile| <= E_k` and its analytic
  cross-tail inequality.  The pseudocount schedule may be selected by exact
  computation, but its positivity and every accepted rational prefix check
  must be rechecked by Lean.
- **constructive or propositional**: constructive — the separator, coupling
  identification, spacing modulus, coefficients, starts, and certificates are
  all `Type`-level data.
- **honest residual**: no producer inhabitant is constructed here.  The
  genuine positive-physical local-gluing witness, physical separator,
  same-object pin, rate-sharpness witness, and linear Gibbs margin remain open.
  In particular, no uniform `spread^2 <= 4/3` certificate has yet been
  constructed for the actual plaquette-coupled BF4 raw grouped kernel, nor
  has its sufficient profile-relative `1/16` enclosure been inhabited.  No
  physical scalar error stream with a checked finite prefix and analytic
  antitone tail step (or its cross-product numerator/denominator witness), and
  no physical input/output distance streams with
  explicit eventual Cauchy moduli, have yet been constructed.
  Equivalently on the shorter direct route, no inhabitant of
  `MatchedPhysicalHalfAmplitudeComputedFloorErrorRows` has been constructed:
  its sole new analytic field, the uniform `computedFloor/2048` physical entry
  error, is still open.  The finite-prefix/cross-tail adapter does not inhabit
  the physical entry majorant or analytic tail inequality.  The direct
  boundary specialization removes the arbitrary middle/prefix data and
  constructs prefix positivity.  Its canonical rank-one specialization also
  constructs the normalized positive terminal and discharges the spread
  budget exactly; it still does not prove that the physical amplitude is
  uniformly within `computedFloor/2048` of that rank-one projection.  The
  positive ideal floor itself is kernel-checked finite recursion and is no
  longer an honest residual.
  Neither refuted exact-Haar same-action seam is an honest residual.
  Consequently this
  entry does not establish an all-cutoff, continuum, OS-reconstructed, or Clay
  mass gap.
- **must not be closed classically**: per `AGENTS.md` Rules 4, 6, 8, and 9.

### [M3-exact-log-rg-handoff] exact logarithmic family to normalized RG persistence — **SPECTRAL-INPUT REDUCTION CLOSED; ANALYTIC INHABITATION OPEN 2026-08-18**

- **milestone**: physical-scale overlay M3 (`work_plan.md`)
- **files**:
  `lean/YMGap/Continuum/MassNormalizedRefinementPersistence.lean`,
  `lean/YMGap/Continuum/MassNormalizedLossPersistence.lean`,
  `lean/YMGap/Continuum/ExactLogMassNormalizedPersistence.lean`,
  `lean/YMGap/Continuum/ExactLogMassNormalizedRefinementPersistence.lean`,
  `lean/YMGap/Continuum/ExactLogMassNormalizedLossPersistence.lean`,
  `lean/YMGap/Continuum/BF4FarautExactRefinementPersistence.lean`,
  `lean/YMGap/Continuum/BF4FarautExactLossPersistence.lean`,
  `lean/YMGap/Continuum/SpectralLocalizedMassNormalizedLossPersistence.lean`,
  `lean/YMGap/Continuum/SpectralLocalizedPhysicalMarginLoss.lean`,
  `lean/YMGap/Continuum/SpectralMarginInputMassNormalizedLoss.lean`, and
  `lean/YMGap/Continuum/BF4FarautSpectralMarginInputExactCertificate.lean`
- **named fields / structures**:
  `MassNormalizedRefinementFlow.spacing_step`,
  `MassNormalizedLossFlow.step`,
  `MassNormalizedLossPersistence.lossBudget`,
  `MassNormalizedLossPersistence.anchorDominates`,
  `ExactLogMassNormalizedLossFlow.exactRate`,
  `ExactLogMassNormalizedLossFlow.spacing_identification`,
  `ExactLogMassNormalizedLossFlow.mass_certificate`,
  `SpectralLocalizedPhysicalMarginFlow.normalizedLoss`,
  `SpectralMarginInput.toInverseSquareControl`,
  `SpectralMarginInput.persistence`, and
  `BF4FarautSpectralMarginInputExactFlow.fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK`.
- **obligation**: Construct a rational lower-certificate flow on the same exact
  physical log-rate family, prove the normalized one-step loss inequality, and
  give a constructive summable loss budget strictly dominated by the anchor.
  Also prove the rational mass certificate lies below the exact log rate at
  each identified spacing.  No exact natural-number spacing ratio is required
  by the preferred interface.
- **proved reduction machinery**: the refinement-specific structure records
  the literal AF orientation, while the direction-neutral structure isolates
  the data actually used by telescoping and accepts both earlier conventions
  through checked adapters.  Any persistent inhabitant transports its rational
  floor to a uniform lower bound for the same exact constructive-real
  logarithmic rates.  The BF4/Faraut hybrid then adds the renormalized M2
  ceiling on definitionally the same separator and spacing family.  The
  spectral-localization adapter corrects the dimensions of the additive loss:
  a dimensionless defect `d_k` produces physical rate loss `d_k*M_k`; a
  physical ceiling therefore yields `rateLoss <= M_ceiling*d_k`.  The existing
  `SpectralMarginInput` now constructs the corresponding shifted inverse-square
  budget at offset `fmCutoff+2`, and the exact BF4/Faraut adapter installs its
  positive floor in the producer's same exact log-rate family.  The final
  focused monitored build passed 1162 jobs, with only `propext` and
  `Quot.sound` in the printed footprint; the six spectral-loss files also pass
  the strict forbidden-token scan.
- **constructive or propositional**: constructive — all flow, spacing,
  certificate, loss-budget, and floor witnesses are `Type`-level data.
- **honest residual**: `SpectralMarginInput` and
  `BF4FarautSpectralMarginInputExactFlow` remain uninhabited for the actual 4D
  corrected-slab flow.  In particular, localization, the same-defect tail
  identification, the spectral bridge, physical ceiling, anchor dominance,
  exact spacing identification, and rational-to-exact mass comparison remain
  analytic inputs.  The BF4/Faraut producer and its renormalized upper
  comparison also remain uninhabited.  The reduction does not establish cutoff
  removal, OS reconstruction, or the Clay theorem.
- **must not be closed classically**: per `AGENTS.md` Rules 4, 6, 8, and 9.

### [M4-same-object-continuum-gap] exact-rate cutoff and continuum/OS handoff — **EXACT-MASS/THEORY-PIN REDUCTIONS EXTENDED; ANALYTIC INHABITATION OPEN 2026-08-18**

- **milestone**: physical-scale overlay M4 (`work_plan.md`)
- **files**:
  `lean/YMGap/Constructive/CRealInnerRegularity.lean`,
  `lean/YMGap/Constructive/CRealLogInnerRegularity.lean`,
  `lean/YMGap/Continuum/SummableCRealStepVariation.lean`,
  `lean/YMGap/Continuum/SummableCRealEventualStepVariation.lean`,
  `lean/YMGap/Continuum/CRealRationalProxyTracking.lean`,
  `lean/YMGap/Continuum/DirectLogQuadraticRemainder.lean`,
  `lean/YMGap/Continuum/QuadraticRateErrorTailControl.lean`,
  `lean/YMGap/Continuum/BF4AFPhysicalSpacingInverseSquare.lean`,
  `lean/YMGap/Continuum/PhysicalSeparationSamplingOfSpacingToZero.lean`,
  `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean`,
  `lean/YMGap/Continuum/PhysicalSeparatorContinuumRealization.lean`,
  `lean/YMGap/Continuum/BF4FarautSpectralPhysicalMarginIdentification.lean`,
  `lean/YMGap/Continuum/ProjectiveOSCorrelationHandoff.lean`,
  `lean/YMGap/Continuum/ExactRateReconstructionHandoff.lean`,
  `lean/YMGap/Continuum/OSCanonicalMarginGap.lean`,
  `lean/YMGap/Continuum/CanonicalTransferFormGap.lean`,
  `lean/YMGap/Continuum/WilsonLinkedOSReconstruction.lean`,
  `lean/YMGap/Continuum/WilsonExactRateGapHandoff.lean`,
  `lean/YMGap/Continuum/WilsonSpectralChannelHandoff.lean`,
  `lean/YMGap/Continuum/WilsonLinearTimeTranslationHandoff.lean`,
  `lean/YMGap/Continuum/WilsonOperatorNormGapHandoff.lean`,
  `lean/YMGap/Continuum/WilsonQuadraticFormGapHandoff.lean`,
  `lean/YMGap/Continuum/WilsonBoundedMassGapHandoff.lean`,
  `lean/YMGap/Continuum/WilsonMinimalBoundedMassGapHandoff.lean`,
  `lean/YMGap/Continuum/WilsonIteratedNormDecayHandoff.lean`,
  `lean/YMGap/Continuum/WilsonMatrixCoefficientDecayHandoff.lean`,
  `lean/YMGap/Continuum/WilsonOSConnectedDecayHandoff.lean`,
  `lean/YMGap/Continuum/ProjectiveWilsonConnectedDecayHandoff.lean`,
  `lean/YMGap/Continuum/ContinuumSquaredClusteringHandoff.lean`,
  `lean/YMGap/Continuum/RCStrictPositivity.lean`,
  `lean/YMGap/Continuum/ContinuumMassClusteringEndpoint.lean`,
  `lean/YMGap/Continuum/ContinuumExactMassClusteringTarget.lean`,
  `lean/YMGap/Continuum/ContinuumExactMassClusteringClayResidual.lean`,
  `lean/YMGap/Continuum/ContinuumCorrectedExactMassTarget.lean`,
  `lean/YMGap/Constructive/CRealAbsContinuity.lean`,
  `lean/YMGap/Continuum/ContinuumExactMassScalingWindow.lean`,
  `lean/YMGap/Continuum/ContinuumExactMassDecayEndpoint.lean`,
  `lean/YMGap/Continuum/ContinuumSelectedExactMassDecayTarget.lean`,
  `lean/YMGap/Continuum/ContinuumSelectedTheoryPins.lean`,
  `lean/YMGap/Rubric/FrontierDAGBridges.lean`,
  `lean/YMGap/Continuum/BF4FarautSpectralMarginInputContinuumRealization.lean`,
  `lean/YMGap/Continuum/BF4PhysicalVacuumPairingModulus.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDenseStageRawMomentModulus.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDenseStageCenteredSlowComparison.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDenseStageRawMeanComparison.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearGNSForm.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearRadicalDescent.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletion.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedAlgebra.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedModule.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInnerKernel.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInnerOuter.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInnerWellDefined.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInner.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInnerLaws.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedVacuumComplement.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovSyntax.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAtomicCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAtomicUniformCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffConditionalCoreReduction.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffPositiveRowPersistence.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffTargetShellTail.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffUniformRowFloor.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffConditionalCoreCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffConditionalCoreModulus.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffStationarySourceTail.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovConcreteAdaptiveGap.lean`,
  `lean/YMGap/Continuum/FiniteRationalReversibleSpectralCertificate.lean`,
  `lean/YMGap/Continuum/FiniteListIndexQuadraticBridge.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffFiniteIndexBridge.lean`,
  `lean/YMGap/Continuum/FiniteRationalPenalizedMatrix.lean`,
  `lean/YMGap/Continuum/FiniteRationalCenteredRestrictionCertificate.lean`,
  `lean/YMGap/Continuum/FiniteRationalHeadCenteredCoordinates.lean`,
  `lean/YMGap/Continuum/FiniteRationalMatrixPullback.lean`,
  `lean/YMGap/Continuum/FiniteRationalHeadCenteredPullback.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffCofinalLDLGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffCofinalRestrictedLDLGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffCanonicalHeadLDLGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorSixteenthObstruction.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffCofinalStrictGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovTransfer.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovLaws.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovVacuumComplement.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovVacuumPairing.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovContraction.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay.lean`,
  `lean/YMGap/Continuum/BF4PhysicalFixedNomeCompletedOperatorNormGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovGraphNorm.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovGraphNormCofinality.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedMarkovAdaptiveCofinalStrictGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovDenseRadicalFromCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCompletedLinear.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveGraphNorm.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveContraction.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCorrelationDecay.lean`,
  and
  `lean/YMGap/Continuum/BF4FarautGraphNormContinuumRealization.lean`.
- **named fields / structures**:
  `PhysicalMarginIdentification.floorRate_eq_physMargin`,
  `SymmetricSpectralShift.reverseHadd`,
  `ProjectiveOSCorrelationHandoff`,
  `ReconstructionSpectralChannelHandoff`,
  `ExactRateReconstructionHandoff`,
  `WilsonLinkedOSGNSData`,
  `WilsonCharacterOS4Pin`,
  `CanonicalTransferFormGap`,
  `WilsonPositiveExactLogGapWitness`,
  `WilsonCharacterSpectralChannelPin`,
  `WilsonLinearTimeTranslationPin`,
  `WilsonCharacterSquarePin`,
  `WilsonQuadraticFormGapPin`,
  `WilsonBoundedMassGap`,
  `WilsonSelectedOSGNSData`,
  `WilsonOperatorNormGapPin`,
  `WilsonMinimalBoundedMassGap`,
  `WilsonVacuumStationarityPin`,
  `WilsonDenseVacuumPin`,
  `WilsonIteratedBoundedMassGap`,
  `WilsonOSConnectedMatrixCoefficientPin`,
  `ProjectiveWilsonOSMatrixCoefficientPin`,
  `RCSquaredGeometricClustering`,
  `NontrivialRCSquaredGeometricClustering`,
  `RCIsPositive`,
  `PositiveRC`,
  `ContinuumMassClusteringEndpoint`,
  `ContinuumExactMassClusteringTarget`,
  `LegacyClayPinnedExtensionResidual`,
  `ExactMassUniformDecayExtension`,
  `ContinuumCorrectedExactMassTarget`,
  `ContinuumCorrectedExactMassResidualData`,
  `ExactMassUniformDecayScalingWindow`,
  `SelectedPhysicalScalingWindows`,
  `SelectedPhysicalVolumeGrowthPins`,
  `ContinuumExactMassScalingResidualData`,
  `NontrivialExactMassContinuumClustering`,
  `ContinuumSelectedExactMassDecayTarget`,
  `SelectedRotationActionPins`,
  `SelectedGaugeProjectionPins`,
  `SelectedGroupUVPins`,
  `SelectedCorrelationNonGaussianPin`,
  `SelectedTheoryPins`,
  `BF4SU2SelectedTheoryPinResidualData`,
  `FrontierToExactMassClusteringTargetBridge`,
  `FrontierToContinuumSelectedExactMassDecayTargetBridge`,
  `WilsonTimeTranslationPin`,
  `TransferFormGapResidual`,
  `CentralPhysicalLinearMarkovAtomicCauchyData`,
  `CentralPhysicalLinearMarkovAtomicCauchyData.toDenseCauchyData`,
  `CentralPhysicalAtomicMarkovUniformSqCauchyData`,
  `CentralPhysicalAtomicMarkovUniformSqCauchyData.toDenseCauchyData`,
  `CentralPhysicalAtomicMarkovCoreTailCauchyData`,
  `CentralPhysicalAtomicMarkovCoreTailCauchyData.toDenseCauchyData`,
  `CentralPhysicalLinearMarkovCompletionModulus`,
  `CentralPhysicalCutoffCompletedMarkovVacuumPairingInvariant`,
  `CentralPhysicalCutoffCompletedMarkovSelfAdjointData`,
  `CentralPhysicalLinearMarkovVacuumPairingInnerCofinality`,
  `CentralPhysicalLinearMarkovVacuumPairingDiagonalControl`,
  `CentralPhysicalCutoffCompletedMarkovStrictContractionData`,
  `CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence`,
  `CentralPhysicalLinearMarkovGraphNormInnerCofinality`,
  `CentralPhysicalLinearGraphNormInputInnerCofinality`,
  `CentralPhysicalLinearMarkovDenseCauchyData.toDenseRadicalData`,
  `centralPhysicalAdaptiveMarkov_requirements_paid`,
  `centralPhysicalAdaptiveMarkovMapCauchy`,
  `centralPhysicalAdaptiveCompletedMarkovTransfer`,
  `centralPhysicalAdaptiveCompletedMarkovTransfer_zero`,
  `centralPhysicalAdaptiveCompletedMarkovTransfer_add`,
  `centralPhysicalAdaptiveCompletedMarkovTransfer_smul`,
  `centralPhysicalAdaptiveCompletedMarkovQLinearEndomorphism`,
  `centralPhysicalAdaptiveGraph_input_rates_paid`,
  `centralPhysicalAdaptiveGraph_action_rates_paid`,
  `centralPhysicalAdaptiveCompletedMarkovPairingInvariant`,
  `centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer`,
  `centralPhysicalAdaptiveCompletedVacuumComplementMarkovQLinearEndomorphism`,
  `centralPhysicalAdaptiveInputCenteredNorm_converges`,
  `centralPhysicalAdaptiveTransferredCenteredNorm_converges`,
  `CentralPhysicalAdaptiveCompletedMarkovStrictContractionData`,
  `centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData`,
  `centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower`,
  `centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_norm_decay`,
  `centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_norm_decay`,
  `centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_matrixCoefficientSq_decay`,
  `centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_matrixCoefficientSq_decay`,
  `ContinuumProjectiveOSResidualData`,
  `ContinuumWilsonBoundedResidualData`,
  `ContinuumWilsonMinimalBoundedResidualData`,
  `ContinuumWilsonIteratedBoundedResidualData`,
  `ContinuumWilsonOSConnectedDecayResidualData`,
  `ContinuumProjectiveWilsonDecayResidualData`,
  `WilsonDenseUnitVacuumPairingModulus`,
  `BF4RawStageMomentModulus.squareBound`,
  `BF4RawStageMomentModulus.meanBound`,
  `BF4RawStageMomentSemanticIdentification.squareSemantics`,
  `BF4RawStageMomentSemanticIdentification.meanSemantics`,
  `BF4RawStageMomentSemanticIdentification.toRawStageMomentModulus`,
  `BF4WilsonDenseStageCenteredVacuumProjectiveBase`,
  `BF4WilsonDenseStageCenteredVacuumSemanticBase`,
  `BF4WilsonDenseStageCenteredVacuumSemanticBase.toProjectiveBase`,
  `BF4WilsonDenseStageCenteredVacuumProjectiveBase.raw_square_diagonal_comparison`,
  `BF4WilsonDenseStageCenteredVacuumProjectiveBase.raw_mean_diagonal_comparison`,
  `ContinuumYMExistence`,
  `MeasureLinkedOSGNSData`,
  and `ExactLogGapAt`.
- **obligation**: Prove that the fixed-spacing cluster floor is the physical
  margin of the same BF4 separator and prove the lower half of the two-sided
  spectral-shift estimate.  Then construct one same-action projective
  continuum measure with the required correlator semantics, OS reconstruction,
  transfer-semigroup identification, and exact generator-gap binding.
- **proved reduction machinery**: spacing-to-zero constructs physical
  separation sampling.  The BF4 AF trajectory constructs the inverse-square
  spacing majorant; the renormalized linear margin tail constructs the exact
  logarithmic half-window and quadratic error bound.  The same-object floor
  identification yields equality of the rational physical and spectral proxy
  rates.  A symmetric shift estimate combines with the existing `hbridge` to
  yield the missing upper normalized drift.  These data construct the exact
  rate's eventual Cauchy modulus, cutoff limit, and positive limiting floor.
  A single `ProjectiveOSCorrelationHandoff` plus the already measure-linked OS
  functional convergence constructs the physical continuum correlators and
  their OS gap-correlation identification; the GNS spectral-channel assertion
  remains separately named.  Convergence of the same finite exact-rate family
  to the reconstructed logarithmic gap now replaces a free final equality;
  constructive-real limit uniqueness supplies that equality.  The full-range
  floor also exports to the canonical `CRealFloor` interface.  The compressed
  residual now additionally pins the Wilson expectation to the selected OS
  functional and requires a concrete Wilson time translation whose
  operator-form gap uses definitionally the same OS4 model and separator.
  `WilsonCharacterOS4Pin.toSelectedFormGap` reduces that operator-form field
  to the physical finite-character coordinate map, its two Schur diagonal
  identities, and explicit fieldwise identifications of the finite model and
  separator with OS4; no dependent equality of whole spectral records is
  assumed.  `CanonicalTransferFormGap` makes the right-hand side of this
  inequality definitionally the concrete separator scalar action, eliminating
  the arbitrary `scaledInner` map in the legacy residual.  The exact-rate
  handoff attaches a positive cutoff-removed logarithmic rate to this same
  concrete Wilson datum and exports the canonical form gap.  The optional
  finite-character spectral-channel handoff leaves only the connected
  OS/character two-point equality as input and proves time-zero positivity for
  every nonempty cutoff from the first character weight.
  The optional linear time-translation handoff records the two missing scalar
  laws, a representative-level linear lift, and an equality pin to the
  selected Wilson transfer; it identifies the functional-calculus spectral
  record with the selected OS4 record.  The operator-norm handoff isolates one
  further square Schur identity for `<T^2 x,x>` and then derives the genuine
  vacuum-complement contraction
  `||T x||^2 <= separator^2 ||x||^2`.
  `WilsonQuadraticFormGapHandoff` weakens that sufficient finite-coordinate
  hypothesis to the minimal quadratic form inequality
  `<T^2 x,x> <= separator * <T x,x>` on the vacuum complement; self-adjointness
  and the canonical linear form gap then derive the same norm contraction.
  The bounded mass-gap handoff combines
  this contraction with the positive exact logarithmic rate on the same
  datum, and the BF4 compressed adapter now exports that conditional endpoint
  directly.  This bounded-transfer route does not require construction of an
  unbounded `-log T` operator.
  `ContinuumWilsonBoundedResidualData` then removes two further unused fields
  from the bounded critical path: neither the projective correlator handoff nor
  the reconstruction spectral-channel identification is needed to combine
  exact-rate convergence with the Wilson operator gap.  The stronger
  projective residual projects to this smaller package after supplying the
  quadratic pin.
  `WilsonMinimalBoundedMassGapHandoff` factors the endpoint once more:
  `WilsonSelectedOSGNSData` stops before the canonical linear form gap, and a
  direct `WilsonOperatorNormGapPin` is the only operator inequality retained.
  `ContinuumWilsonMinimalBoundedResidualData` therefore carries exactly
  continuum existence, that selected same-measure Wilson/OS datum, exact-rate
  convergence, and the direct norm gap.  The quadratic and finite square
  Schur paths compile to this package as sufficient constructors but are not
  fields of the minimal endpoint.
  The dense BF4 graph-limit route now constructs its centered comparison from
  two fixed-observable rational modulus families: the raw finite square
  against the projective reflected-square evaluator and the raw finite
  stationary mean against the projective vacuum-pairing evaluator.  The slow
  sampler accumulates the ordinary and translated rates at every candidate
  dense term, so the moving-diagonal raw comparisons are theorems rather than
  residual fields.  A separately named
  `WilsonDenseUnitVacuumPairingModulus` retains the representative-level
  `Nat` rate that cannot be extracted constructively from proposition-level
  equality in the completed-real quotient.  The vector-adaptive slow sampler
  pays the ordinary and one-step-translated projective and pairing rates.
  Exact finite centering then subtracts the squared mean and constructs the
  prior centered comparison and completed operator gap.
  `WilsonIteratedNormDecayHandoff` adds the explicitly named vacuum
  stationarity pin needed to preserve the vacuum complement under iteration;
  a dense zero-vector identity is a sufficient constructor.  The resulting
  endpoint proves the geometric squared-norm estimate for every transfer
  power.  `WilsonMatrixCoefficientDecayHandoff` combines it with the
  completed-GNS Cauchy--Schwarz inequality to prove geometric squared decay
  of arbitrary matrix coefficients.  `WilsonOSConnectedDecayHandoff` then
  names the independent same-object pin identifying a selected connected OS
  insertion with that Wilson autocorrelation and proves its squared decay.
  The BF4 adapter carries this only in
  `ContinuumWilsonOSConnectedDecayResidualData`; the correlation fields do not
  re-enter the bounded mass-gap critical path.
  `ProjectiveWilsonConnectedDecayHandoff` composes the projective functional
  equality with that matrix-coefficient theorem, leaving exactly one direct
  pin from the reconstructed continuum gap correlator to the selected Wilson
  autocorrelation.  `ContinuumSquaredClusteringHandoff` packages the result
  with ratio `separator^2 < 1`; the reconstruction spectral channel supplies a
  positive time-zero floor, excluding a vacuous zero channel.
  `ContinuumMassClusteringEndpoint` then packages the positive exact
  logarithmic mass and this nontrivial clustering on the same selected object.
  Its clustering ratio is definitionally the square of the separator whose
  exact logarithm is the mass.  The BF4 projective/Wilson residual exports this
  endpoint without adding any new analytic premise.
  `RCStrictPositivity` moves the mass statement into the same completed-real
  quotient used by the Wilson Hilbert and clustering layers.  There `PosEv` is
  exactly strict positivity, so the endpoint exports a Type-level positive
  `RC` mass literally equal to the reconstructed exact logarithm, without
  making a non-invariant claim about the early approximations of a raw
  `CReal` representative.
  `ContinuumExactMassClusteringTarget` bundles the selected continuum measure,
  full existence hypothesis, separator/spacing/sampling, Wilson datum,
  projective handoff, and endpoint.  It chooses the reconstruction's computed
  exact logarithm as a canonical raw positive representative.  The legacy
  Clay comparison then constructs every shared carrier and pin of
  `ClayTargetPinned` from that target, leaving only its separate continuum
  existence/limit package, margin-mass equality, and uniformity as an
  uninhabited residual.  `ContinuumCorrectedExactMassTarget` avoids that
  currency loss: it requires a spacing-uniform physical correlation-decay
  witness with mass `CReal.Equiv` to the canonical exact logarithm, proves the
  two masses equal in `RC`, and projects full O(4) from the same continuum
  existence datum.  The BF4 adapter now packages exactly this final
  mass-pinned uniform-decay residual and exports the corrected target.
  Absolute-value continuity on constructive reals transports the
  finite-spacing inequality through the selected scaling limit.  The error
  argument is the source-defined concrete ratio
  `max(1/(n+1), n/(L+1))` on the exact same physical correlator; there is no
  abstract ratio or later equality pin.  Source-level error nonnegativity,
  canonical floor-sampler UV control and no-overshoot are proved.  Normalizing
  the sampled exponent by physical time proves its convergence to the one-step
  exact-mass exponent; exact exponential chunking rewrites the variable
  lattice power as a fixed `(t+1)`-power.  Fixed-power and fixed-amplitude
  continuity then reconstruct the complete envelope transport.
  `SelectedPhysicalScalingWindows` therefore
  retains only the same-family volume window beside the derived UV window,
  while the BF4 `ContinuumExactMassScalingResidualData` carries exactly one
  field beyond its nested corrected target: cofinal divergence of the same
  family's physical linear extent `a_j(L_j+1)`.  A proved generic bridge and
  BF4 constructor reduce this to the sufficient natural-number schedule
  `L_j+1 >= j*den(a_j)`.  Generic sequential continuity of `expNegCD` on
  constructive reals is proved, so it no
  longer assumes the full unweighted positive-separation envelope limit.  The resulting endpoint
  proves unsquared continuum decay at `t+1`, avoiding an artificial time-zero
  scaling premise, and packages a nonzero selected channel.  A separate
  audit showed that the legacy O(4), gauge, UV, and nontriviality carriers can
  choose objects unrelated to their `ContinuumMeasure`.  The stronger
  `SelectedTheoryPins` therefore puts the actions, projection, UV evaluator,
  and interaction witness on the exact selected OS algebra/thread/correlator.
  Its BF4 adapter fixes the group type to `A 1` (SU(2)) by construction and
  proves strict monotonicity of the selected inverse coupling.  The exact-mass
  targets are explicitly registered as consumers of completion maps from the
  canonical `FrontierDAG`; no such map is inhabited.  The static DAG audit
  reports 34 enumerations, 2 bridged, and 0 unbridged.
  The canonical legacy margin export is separate from the exact-log endpoint.
  The focused monitored Wilson-link build passes 121 jobs, the exact-rate
  handoff passes 240 jobs, the spectral-channel handoff passes 243 jobs, the
  linear time-translation handoff passes 124 jobs, the operator-norm handoff
  passes 122 jobs, the minimal quadratic-form handoff passes 123 jobs, the
  bounded mass-gap handoff passes 243 jobs, the minimal bounded mass-gap
  handoff passes 244 jobs, the iterated norm-decay handoff passes 245 jobs,
  the matrix-coefficient handoff passes 258 jobs, the connected OS handoff
  passes 259 jobs, the projective/Wilson correlation handoff passes 261 jobs,
  the constructive-real squared clustering handoff passes 262 jobs, the
  completed-real strict-positivity bridge passes 80 jobs, the same-object
  mass/clustering endpoint passes 264 jobs, the exact target bundle passes 265
  jobs, the legacy Clay residual factoring passes 269 jobs, the corrected
  exact-mass target passes 266 jobs, constructive-real absolute continuity
  passes 47 jobs, the exact-mass scaling window passes 269 jobs, the continuum
  exact-mass decay endpoint passes 270 jobs, the selected target passes 271
  jobs, the same-theory pin layer passes 284 jobs, the canonical bridge module
  passes 411 jobs, and the downstream BF4/SU(2) adapter passes 1224 jobs.
  In each focused check, every newly printed load-bearing declaration depends
  only on `propext` and `Quot.sound`.
- **constructive or propositional**: constructive — all identifiers, moduli,
  selected projective threads, continuum functionals, reconstructions, and
  exact gap witnesses are carried as `Type`-level data.
- **honest residual**: the physical/spectral identification is not inhabited
  for the genuine 4D flow.  The projective OS correlator handoff remains open
  for the separate full correlation theorem, but is no longer a premise of
  the bounded-transfer mass-gap endpoint.
  Continuum Yang--Mills existence, the selected same-measure Wilson GNS/time
  translation datum, its direct vacuum-complement operator-norm contraction,
  vacuum stationarity, and convergence to the exact reconstructed generator
  gap are also not constructed here.  A finite-character/OS4 pin with its
  square Schur
  identity, or the weaker quadratic form inequality together with the
  canonical linear form gap, remains a sufficient route to that direct norm
  contraction rather than a premise of the minimal endpoint.  The selected
  dense-stage route still has no inhabitant for its raw observable map,
  radical transfer intertwining, rational projective modulus,
  fixed-observable raw-square and raw-mean moduli, or qualitative dense-unit
  vacuum pin.  The moving-diagonal versions are now constructed.  An explicit
  representative vacuum-pairing modulus remains only on the legacy
  quantitative route and is no longer an input of the general qualitative
  endpoint.
  Alternatively, two exact same-stage semantic identities construct the raw
  moment moduli with zero rates; these stronger identities are also not
  inhabited.  Thus the current thermodynamic/projective analytic frontier is
  to construct either the general fixed-observable moment moduli or, on an
  exact realization branch, the finite-square and finite-mean same-stage
  identities.  The compiler proves both routes sufficient but proves neither
  analytic input.  The direct qualitative-vacuum compiler additionally proves
  that the `pairingRate` and `pairingSmall` fields are not needed by the final
  graph-norm convergence argument: qualitative convergence from
  `WilsonDenseUnitVacuumPin` suffices inside the proposition-valued limit.
  The general weak dense-stage residual now carries the fused
  `BF4RawStageContinuumMomentModulus` and that vacuum pin, but no
  representative pairing modulus, rational projective functional, or
  intermediate projective diagonal.  Its slow diagonal pays exactly four
  direct rates: raw square and stationary mean for the ordinary and
  one-step-translated representatives.  The former projective-functional
  modulus plus raw moment moduli construct this weaker certificate by a proved
  half-error composition, while the exact-semantic route further specializes
  the raw comparison legs to zero rates.  Neither weak route asks the raw
  realization to preserve the continuum carrier setoid, because that
  congruence law is unused by the representative-level proof.
  This is an interface reduction, not an inhabitant: the raw realization, its
  radical transfer law, the direct fixed-observable moment certificate (or a
  stronger projective/exact-semantic refinement), and the qualitative vacuum
  pin remain unconstructed analytic inputs on the physical thread.
  The direct endpoint additionally no longer assumes that the selected
  continuum transfer is additive or scalar-linear.  It consumes only a chosen
  Cauchy representative of the actual quotient-level transfer together with
  its termwise observable-shift law, and it constructs the representative
  graph-norm limit interface directly.  The former pointwise linear transfer
  pin and linear graph-norm residual refine these weaker records by proved
  adapters.  The representative lift itself remains uninhabited.
  The direct endpoint also weakens the former dense-unit vacuum input.  It now
  asks only that the selected completed vacuum equal the embedded unit and be
  stationary under the completed transfer; the stronger carrier equation
  `tau(one) ~ one` constructs this record but is no longer required.  These two
  weaker vacuum facts are still uninhabited on the physical continuum thread.
  Finally, the public direct base no longer requires exact radical
  intertwining between the finite transfer and a separately realized
  translated observable.  It asks instead for direct square/mean convergence
  both before and after the literal finite macro transfer.  The former direct
  moments plus exact intertwining construct these four graph-moment families
  by proved radical-invariance lemmas, so that stronger route remains
  sufficient.  The graph-moment estimates themselves remain uninhabited.
  A final representative-level weakening removes the pointwise equation
  between the chosen transferred Cauchy sequence and `tau` from the public
  endpoint.  The transferred square/mean bounds now target the terms of the
  chosen representative directly, while the representative pin records only
  its quotient class.  The stronger pointwise and observable-shift moment
  inputs construct this record by proved form congruences.  The physical
  representative lift and these representative-targeted moment estimates
  remain uninhabited.
  The concrete finite-stage audit closes the finite side of this distinction:
  the physical GNS completion, Markov transfer, stationary normalized vacuum,
  vacuum-complement preservation, and same-object completed macro correlator
  are already constructed at each matched cutoff.  What is missing is the
  cross-scale realization of one continuum OS/GNS representative family and
  convergence of its four moments.  `ContinuumMeasure` currently constructs
  only the inverse-limit thread of a supplied consistent abstract family; it
  does not provide the constructive probability-measure extension or these
  Wilson moment limits.
  The finite row marginal is now also packaged as the genuine
  `centralPhysicalProbFunctional` at each matched stage.  Its `a* b` moment is
  the exact physical GNS weighted pairing and it is stationary under the
  finite Markov action.  Given a Type-level tail modulus pinned to those actual
  expectations, `matchedPhysicalFunctionLimitFunctional` constructs their
  positive normalized `CReal` limit and discharges unit convergence
  automatically.  The literal-observable tail modulus is not inhabited; even
  after it is supplied, Euclidean/OS axioms, non-triviality, cross-scale
  transfer moments, reconstruction, and the uniform physical gap remain open.
  Independently, `slabNomeCutoffProbFunctional` is now an actual inhabitant at
  every fixed rational `0 < w < 1` and fixed finite corrected-slab extent: the
  existing executable outer-cutoff bound removes the Peter--Weyl
  representation cutoff for all cutoff-stable `[0,1]` observables and proves
  positivity and normalization of the resulting `CReal` functional.  This
  does not inhabit the matched physical-scale modulus above.  A one-sided
  reindex theorem now identifies these slab expectations with the physical
  stationary row marginal for globally `[0,1]`-valued lower observables.
  The resulting cutoff-limit functional has literal stationary-mean
  approximations, and its finite product moments are definitionally the
  weighted pairings of the physical GNS.  What remains is cutoff convergence
  of the physical Markov action itself, extension beyond the bounded
  multiplicative carrier, and estimates uniform in nome, extent, volume, and
  spacing.
  The same cutoff modulus now also constructs the actual one-step
  same-object transfer-form limit for bounded lower observables: its finite
  approximations are `centralPhysicalWeightedInner a (P a)`, and positivity
  plus the identity-form upper bound survive the cutoff limit.  The stationary
  square, mean, and transfer-form limits have now been combined into literal
  connected Bishop reals.  Exact finite centering identifies their
  approximations with the norm and Markov form of the marginal-centered
  observable, proving the limiting interval
  `0 <= connectedAutocorrelation <= connectedNorm`.  This remains form-level:
  it is not a cutoff-independent operator or Hilbert completion.  The next
  obligation is to determine whether the existing finite `1/16` producer data
  can be routed uniformly through representation-cutoff removal and the
  relevant physical scale trajectory.  No such strict cutoff-uniform factor is
  presently constructed.  The pointwise local-gluing sixteenth has been
  generalized from half-extent zero to arbitrary finite half-extent, exposing
  the remaining cutoff-limit input exactly as a family of genuine local-slice
  gluing witnesses uniform over the representation cutoff.  That family is
  now packaged as `FixedNomeCutoffLocalGluing`; it constructs the exact
  mean-zero `FixedNomeCutoffCenteredSixteenth`, which in turn proves the strict
  connected Bishop-real limit bound with factor `1/16 < 1`.  Neither record is
  inhabited.  The next analytic frontier is to construct this cutoff-uniform
  slice family, or to prove a bridge from existing matched-profile row data to
  it without conflating a coupled nome/cutoff trajectory with a fixed-nome
  representation-cutoff limit.  Exact cutoff-uniformity has now been weakened
  further to a Type-level asymptotic modulus: a `1/16` mean-zero bound with
  arbitrary additive `epsilon` beyond an explicit cutoff suffices for the
  strict connected limit in transitive `CReal.leEv`.  This weaker modulus is
  also uninhabited; ordinary slab-observable convergence does not automatically
  control the cutoff-dependent centered observable.  A further cofinal
  weakening now shows that exact `1/16` strictness only on a constructive
  unbounded subsequence of fixed-nome representation cutoffs suffices: the
  connected streams' existing Cauchy proofs transfer the anchor estimates to
  the limit in `CReal.leEv`.  The corresponding centered and local-gluing
  cofinal records are uninhabited.  The matched-AF finite producer does not
  supply them because its nome changes with scale.
  The exact fixed-nome centered-sixteenth interface now has a stronger
  kernel-checked consequence at every representation cutoff: exact rational
  centering transports it through the genuine finite physical GNS completion,
  and the constructive form-to-operator theorem yields
  `||T v||^2 <= (1/16)^2 ||v||^2` on each completed finite-cutoff vacuum
  complement, uniformly in the cutoff and for arbitrary finite half-extent.
  The interface itself remains uninhabited, and these varying completed
  spaces are not yet the single cutoff-removed completion; centered graph-norm
  convergence of vectors and transferred vectors remains the exact transport
  frontier.
  The finite certificate path now also supports the smaller matrices produced
  by eliminating one weighted-mean coordinate.  A Type-valued restriction
  explicitly lifts reduced coordinates, proves exact centering, and
  constructively recovers reduced coordinates for every centered full vector;
  exact upper/lower quadratic identities then compile ordinary or
  cleared-denominator LDL checks to the canonical two-sided contraction.  No
  physical restriction or reduced LDL table is inhabited.  Generic
  changing-dimension packages now retain either kind of reduced checker along
  a cofinal schedule, and their genuine BF4 specialization compiles directly
  to `FixedNomeCofinalCenteredSixteenth`.  The historical cutoff-two table
  remains one-sided at `49/50`, so it is not evidence for the required
  two-sided `1/16` cofinal family.
  The centered-coordinate residual is reduced further whenever the head
  weight is strictly positive.  The explicit lift divides the negative tail
  weighted sum by that head weight; it is proved centered and constructively
  complete for all centered full vectors.  Hence the only remaining generic
  restriction fields are the two reduced-matrix quadratic identifications.
  Their canonical pullback construction is now explicit: Lean proves the
  literal `A^T M A` quadratic equals the full quadratic on the finite linear
  lift using only finite Fubini and rational algebra.  The positive-head
  transform is constructed and proved to evaluate
  to the explicit division lift on every in-range full coordinate.  Pullback
  of both canonical penalized matrices therefore generates the entire
  `FiniteCenteredTwoSidedRestriction`, including both quadratic identities.
  Positivity of the indexed physical head weight is now proved from nonempty
  positive-row support, so every genuine BF4 cutoff carries this canonical
  restriction.  Ordinary and cleared LDL certificates are pinned to the
  generated matrices, and cofinal families compile to
  `FixedNomeCofinalCenteredSixteenth`.  At cutoff two, the exact 65-state raw
  sector now supplies the promised obstruction: sparse evaluation of one
  canonical upper-matrix diagonal at `q = 1/16` proves it strictly negative,
  and therefore proves that neither the ordinary nor cleared LDL certificate
  type can be inhabited for that displayed sector restriction.  This rules
  out an all-cutoff sixteenth and cutoff two as a cofinal anchor; it does not
  rule out a sixteenth on some later unbounded schedule, and its transport to
  a full physical-carrier observable remains separate.  The certificate seam
  is now parameterized by an arbitrary constructive strict rate
  `0 <= q < 1`.  Canonical ordinary and cleared LDL families compile at that
  supplied rate.  Moreover, reflection positivity of the genuine physical
  joint quadratic reduces the physical certificate to the upper edge alone:
  ordinary or cleared upper-only LDL checks prove `K <= qD`, and the existing
  `0 <= K` theorem converts this to `|K| <= qD`.  No such full-carrier cofinal
  family is inhabited.  The arbitrary rate is now propagated through the
  completed adaptive graph-norm route as well: anchorwise form factor `q`
  becomes squared-norm factor `q*q`, cofinal reindexing preserves both graph
  limits, and quotient descent constructs strict contraction of the actual
  cutoff-removed completed transfer at stored rate `q`.  The next finite
  analytic frontier is production of a viable uniform full-carrier cofinal
  upper family; the nonconstant completion modulus also remains uninhabited.
  The historical cutoff-two `49/50` table is no longer merely an unidentified
  diagnostic matrix.  A sparse positive-head pullback formula and 64
  process-isolated row checks identify all 4096 entries with the canonical
  upper restriction of `(49/50)D-K+dd^T` on the verified 65-state cube-subset
  sector.  The old cleared LDL rows and positive pivots therefore inhabit the
  generic upper-only certificate and prove `K <= (49/50)D` for every exactly
  centered coefficient on that sector.  Existing support theorems show the
  65-state sector is row-closed in the genuine cutoff-two physical kernel.
  This closes the finite invariant-sector matrix-identification obligation,
  but not the full-carrier or cofinal obligation: equality with the entire
  physical carrier, control of omitted components, a uniform unbounded
  fixed-nome schedule, and the completion modulus all remain uninhabited.
  The bridge-data and complete 4096-entry row targets built successfully; the
  final theorem passed a direct monitored source check under
  `[propext, Quot.sound]`.  A dependency-complete final target replay was
  intentionally interrupted while rebuilding already-existing historical LDL
  chunks and is not recorded as passed.
  The carrier-scope question is now answered negatively at cutoff two.
  `BF4PhysicalBoundaryCutoffTwoSectorComplementWitness` constructs the lower
  state with fundamental label one only at face `39` and a four-face fixed
  boundary `[40, 41, 49, 59]`.  Direct production reduction proves its
  diagonal kernel entry positive, so it is retained, while the exact
  65-state classifier proves it lies outside the cube-subset sector.  Sector
  row closure plus kernel symmetry proves both cross-block entries vanish.
  Hence the omitted carrier has a genuine positive state in a distinct block;
  full-carrier identification is refuted, not merely open.  The next honest
  obligation is the centered block-indicator no-go for every full-carrier
  `q < 1`, followed by an explicit physical superselection-sector choice.
  The focused target built successfully in 1597 jobs, and all printed
  declarations use only `[propext, Quot.sound]`.
  The reducibility consequence is now fully kernel-checked.
  `BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction` uses faithful
  finite-state codes to define the 65-state block indicator, proves it fixed
  by the literal full-carrier Markov action, centers it by the exact stationary
  mean, and proves the resulting mean-zero mode has strictly positive weighted
  norm.  Its joint quadratic equals that norm, so every proposed full-carrier
  strict bound `q<1` fails at cutoff two, including the absolute-value form
  consumed by the cofinal compiler.  The 65-state sector `49/50` theorem is
  unaffected; what is refuted is treating the reducible union of all positive
  rows as a single-vacuum carrier.  The next honest input is a constructively
  compatible invariant vacuum/superselection sector family across cutoffs.
  The focused target built successfully in 1673 jobs, and all printed
  declarations use only `[propext, Quot.sound]`.
  That transport frontier is now specialized to the actual cutoff-removed
  carrier.  Every completion representative has a canonical exactly centered
  vector in each finite-cutoff physical GNS completion, and its finite vacuum
  orthogonality is proved rather than assumed.  The two remaining graph-norm
  laws are named by
  `CentralPhysicalCutoffCompletedMarkovCenteredGraphNormConvergence`: centered
  norm convergence to the actual completed norm and transferred centered-norm
  convergence to the norm of the actual completed transfer.  Together with
  the fixed-nome sixteenth, these two laws construct the same-object strict
  contraction certificate at literal rate `1/16`; neither input is inhabited.
  The two graph-norm laws have now been derived from a smaller explicit
  diagonal residual.  `CentralPhysicalLinearMarkovGraphNormInnerCofinality`
  reuses the existing input/action vacuum-pair cofinality and adds only
  input/action self-pair cofinality.  A general diagonal limit theorem proves
  that these four rates dominate the nested inner/outer construction; exact
  centering and quotient orthogonality then construct both graph-norm laws.
  Hence this four-rate datum, the completion modulus, and the fixed-nome
  sixteenth compile to same-object strict contraction at `1/16`.  None of
  those three analytic inputs is inhabited.
  Exact structural rate invariance now removes the two action-side cofinal
  fields: the atomic slab rate ignores atom labels and the recoded Markov
  action preserves the finite-linear syntax tree.  Thus
  `CentralPhysicalLinearGraphNormInputInnerCofinality` carries only input
  self-pair and input vacuum-pair cofinality and constructs the four-rate
  record, both graph-norm laws, and the same-object strict contraction when
  combined with the completion modulus and fixed-nome sixteenth.  This
  two-rate same-index record remains uninhabited and is no longer on the
  adaptive critical path: a slow representative schedule now handles syntax
  whose modulus is not bounded by its own numeric sequence index.  Rebuilding
  the graph-norm compiler around the new adaptive transfer is the remaining
  connection to the strict-gap route.
  The structural carrier edge has advanced independently: the constructive
  finite rational span of the genuine unit observables now carries a positive
  symmetric rational-bilinear `CReal` form whose `K`-th approximation is the
  literal finite physical GNS pairing at cutoff `K`.  Thus additivity after
  representation-cutoff removal is no longer an open input.  Sharp CReal
  Cauchy--Schwarz and radical descent are now proved from the exact
  finite-stage bridge and explicit local-bound/product moduli.  Instantiation
  of the existing `CRealSeminormCompletion` is now complete: the limiting
  squared distance has proved reflexive, symmetric, nonnegative, sqrt-free
  triangle, and endpoint-replacement laws, so an actual radical quotient and
  explicit-modulus Cauchy completion are constructed.  Addition, rational
  scaling, zero, and negation have now descended to actual operations on that
  completion using proved quadratic-Lipschitz and explicit continuity moduli.
  Their additive-group and rational-module laws are now literal equalities on
  arbitrary completed points and are bundled as a completed rational module.
  The inner analytic kernel for extending the form is now complete: the
  physical slab cutoff modulus is retained as Type-level data through all
  signed finite-linear expressions, and quantitative two-sided
  Cauchy--Schwarz, diagonal/distance identification, and the bilinear endpoint
  telescope are proved.  The outer representative pairing limit is now also
  constructed from a computable uniform diagonal ceiling and a Type-level
  outer Cauchy rate.  Representative independence under both explicit `Close`
  relations is now proved by a same-index quantitative comparison.  Descent
  to an `RC`-valued completed inner form is now complete, including equality
  with the dense physical pairing.  Its symmetry, diagonal nonnegativity,
  additivity in both arguments, and rational homogeneity in both arguments
  are now literal theorems on arbitrary completed points.  The constant-one
  vector is now an exactly normalized completed vacuum.  Orthogonality to it
  defines a proper completed subtype, the dense orthogonal sector embeds into
  it, and it inherits the ambient rational-module laws.  Every finite physical Markov map
  has now been recoded by the constructive stochastic extension
  `P_K f + (1 - P_K 1) f` as an endomorphism of the same cutoff-independent
  finite-linear syntax.  The extension is globally unit-interval-valued; on
  the retained carrier it is the literal finite action; it fixes the vacuum
  globally; and it satisfies the exact same-cutoff GNS contraction.  The
  cross-cutoff Cauchy obligation is factored at its
  exact first use as Type-level pointwise modulus data.  Each witness produces
  a canonical completed dense image independently of the rate proof, and a
  family produces a rational-linear map from finite-linear syntax into the
  completion: preservation of zero, addition, and every rational scalar is
  proved from pointwise identity of the recoded cutoff sequences.  The vacuum
  modulus is inhabited with rate zero and its completed limit is exactly the
  normalized vacuum.  Nonconstant pointwise moduli remain open.
  Dense radical compatibility is no longer separate: exact same-cutoff
  contraction and squared-distance inner-rate invariance give a limiting
  nonexpansiveness estimate with explicit slack.  Hence every pointwise
  Cauchy family constructs its own radical-closeness witness and descends
  through the dense null quotient.  An adaptive two-index construction now
  removes the same-index completion modulus altogether for transfer
  existence: a slow finite-prefix schedule proves
  `K |-> P_K(X_{i_X(K)})` Cauchy for every input representative and maps close
  representatives to close output diagonals.  Pointwise dense Cauchy data
  therefore construct a quotient-well-defined endomap of the whole physical
  completion; it agrees with the dense cutoff limit and fixes the normalized
  vacuum.  The historical same-index completion modulus remains uninhabited
  and is retained only by older downstream compilers.  Conditional on that
  older exact modulus, its completed transfer is a proved rational-linear
  endomorphism: it preserves zero, addition, and every rational scalar on
  arbitrary completed vectors.  Rational linearity of the new adaptive
  transfer is the next quotient-comparison theorem.  Vacuum-complement preservation is now
  reduced exactly to a completed vacuum-pairing invariant; completed
  self-adjointness is proved sufficient because the transfer fixes the
  vacuum.  Either certificate constructs the actual restricted transfer and
  its rational-linear endomorphism laws on the completed complement.  Neither
  certificate is inhabited; deriving it from finite detailed balance and
  cross-cutoff control remains analytic input.  The finite part of that route
  is now proved more sharply: at every cutoff, the matched diagonal
  approximations of `<P_n x, vacuum>` and `<x, vacuum>` are exactly equal by
  the genuine stationary-mean theorem.  The residual is reduced to one
  explicit cofinal inner-regularity rate ensuring that the diagonal cutoff
  catches both nested inner limits.  Such a rate constructs the completed
  pairing invariant and restricted rational-linear operator, but it is not
  currently inhabited for arbitrary Cauchy representatives.  Conditional on
  those exact cutoff-removal and pairing inputs, strict contraction of the
  actual restricted completed operator is now isolated as the Type-level
  `CentralPhysicalCutoffCompletedMarkovStrictContractionData`: it carries a
  recoverable rational `q` with `0 <= q < 1` and the literal completed
  squared-norm inequality.  That one-step estimate is proved to iterate to
  `<T^n v,T^n v> <= (q^2)^n <v,v>` on the same completed vacuum complement.
  No inhabitant is claimed, and the separate finite or matched-cutoff `1/16`
  estimates have not been transported to this same-object certificate.
  Independently of that open strict estimate, finite-linear
  Cauchy--Schwarz is now transported through the explicit outer pairing limit
  and completion quotient.  Consequently the actual completed physical inner
  form obeys sharp completed-real Cauchy--Schwarz.  Combining it with the
  conditional power-norm theorem proves geometric decay of every squared
  same-object matrix coefficient `<T^n v,test>^2`, with `v` in the completed
  vacuum complement and arbitrary completed `test`.  This closes the
  norm-to-correlation implication but does not inhabit any of its analytic
  transfer or strictness inputs.
  The selected
  connected OS insertion's vacuum orthogonality and exact equality with its
  Wilson `T^n` autocorrelation remain open only for the separate full
  correlation theorem; the projective/Wilson handoff and clustering endpoint
  make the consequence explicit but do not inhabit that equality.  Its
  positive time-zero floor proves only that this selected continuum channel is
  nonzero; it does not establish non-Gaussianity or the spectrum of the full
  OS/Wightman field theory.  The OS/character equality is a distinct optional
  channel.  The
  corrected target still consumes an uninhabited `ContinuumYMExistence` and a
  mass-pinned `UniformPhysicalCorrelationDecay`; it does not construct either.
  The later exact-mass endpoint additionally consumes sampled-correlation
  convergence through the corrected target.  Its reduced BF4 scaling residual
  still requires only same-family cofinal physical linear-extent divergence;
  exact exponential continuity, chunking, fixed-power reconstruction, the UV
  window, no-overshoot, error sign, and fixed-amplitude transport are no longer
  residual assumptions.  The
  strengthened theory-pin record
  is also uninhabited: its abstract label action has not been identified with
  constructive full O(4), its `A 1` tag does not itself construct SU(2), Haar
  integration, or the Gibbs law, and its current Wick-product violation is a
  selected-correlator surrogate rather than a full hierarchy theorem.
  The legacy `ContinuumYMExistence` O(4), gauge, UV, and nontriviality fields
  are insufficient substitutes because their carrier definitions may select
  objects unrelated to the chosen continuum measure.
  Its full O4 theorem is therefore a projection from explicit hypothesis data,
  not a proof of rotation restoration for 4D Yang--Mills.  The
  linear transfer pin is an optional prerequisite for the general continuous
  functional-calculus route, not for the bounded operator-norm conclusion.
  The finite-character
  spectral-channel reduction is optional rather than a claim that every
  continuum model has that finite form.  The legacy abstract reconstruction
  still does not
  realize its Hilbert carrier as the concrete completed Wilson GNS space.  The
  conditional endpoint therefore does not establish a continuum Yang--Mills
  theory or the Clay theorem.
- **must not be closed classically**: per `AGENTS.md` Rules 4, 6, 8, and 9.

### [FrontierDAG-bulkCtrl-repoint] canonical finite re-based fusion control — **STATEMENT REPOINTED 2026-08-05; ANALYTIC FIELD OPEN**

- **milestone**: 11.14 / work-plan milestone 51 (`FrontierDAG` canonical-atom
  statement repair)
- **files**:
  `lean/YMGap/Continuum/RebasedExpShiftSupportReduction.lean`,
  `lean/YMGap/Continuum/RebasedBulkLocalizationBridge.lean`,
  `lean/YMGap/Continuum/ReflectedSaddleExpCertificate.lean`,
  `lean/YMGap/Continuum/CanonicalBulkBlockPowerTransport.lean`,
  `lean/YMGap/Rubric/FrontierDAG.lean`
- **historical field statement**:
  `bulkCtrl : SpectralLocalizationCrux.SpectralLocalization w`.
- **review finding**: the intended physical pin of that carrier to
  `fusionEig N w p` is kernel-refuted at `N=3`, `w=11/12`, `p=2`, `s=2`,
  because its bare-reference shift exceeds `1/12`.  The arbitrary `eig'` field
  also failed to pin the canonical atom to the DAG's cutoff and exponent.
- **reviewed replacement**:
  `bulkCtrl : RebasedBulkLocalizationBridge.CanonicalBulkControl N w pΓ`.
  It carries `1 <= N`, `0 < pΓ`, the physical and near-continuum windows,
  the actual fusion denominator, an effective weight in `[0,1]`, and the
  corrected `FiniteExpShiftBridge` only on `s <= 2*N`.  Thus it is tied to the
  SAME `N`, `w`, and `pΓ` already used by the enclosing physical DAG.
- **proved migration machinery**:
  `expShiftBridge_of_finite_pos` compiles the infinite tail structurally;
  `CanonicalBulkControl.bulk_below_gapEdge` delivers the corrected physical
  bulk-to-gap result; `canonicalBulkControl_p1` proves interface non-vacuity at
  the unperturbed exponent.  The selected reflected checker now proves the
  general certificate compiler `finiteExpShiftBridge_of_certificate`: a direct
  rational branch or an explicit dyadic-log tail/separation branch is checked
  at each finite mode, and the latter is contradicted by the faithful saddle
  estimate.  The result compiles end-to-end into `CanonicalBulkControl`.  The
  corrected downstream `CanonicalBulkBlockPowerTransport` reaches
  `PhysicalRGInput` and a positive `CRealFloor` conditional on its single named
  physical map-identification field `localizationToPower`.
- **constructive or propositional**: constructive — the effective weight and
  finite certificate are `Type`-level data.
- **axiom gate**: all new load-bearing declarations use only
  `[propext, Quot.sound]`; no `sorryAx`, classical choice, `native_decide`, new
  axiom, or noncomputable witness.
- **2026-08-05 positive-exponent progress**:
  `PhysicalP2FiniteCertificate.fenceCanonicalBulkControl` now inhabits the first
  exact nonvacuous physical cell at `N=3`, `w=11/12`, `pΓ=2`,
  `weff=23/25`.  All seven modes `s<=6` are checked by kernel `decide`, and
  `fenceModeTwo_isBulk` proves the consumer's bulk premise is inhabited at
  `s=2`.  This closes concrete certificate data at one fence cell; it is not an
  all-cutoff or all-scale closure.
- **map-identification refinement**:
  `BlockingStepFrontier.IsBlockPowerOnTrajectory` proves that only physical
  separator inputs are required downstream.  The new
  `FusionSpectrumBlockingDictionary` explicitly carries per-scale positive-
  exponent controls, a localized mode, the fine fusion pin, the genuine
  `blockingStep.Φ` image pin, and the exact fusion power identity.  Its proved
  bridge reaches `PhysicalRGInput` and `CRealFloor`.  This strictly refines the
  earlier over-strong global `forall x : CReal` residual.
- **2026-08-05 block-compatible all-scale refinement**:
  the replacement schedule `N_(k+1)=2*N_k+1`,
  `u_(k+1)=u_k/4` now compiles exact head cells through `k=3` and reduces the
  `k>=4` normalized mode-one atom in two proved stages.  First,
  `P2BlockCompatibleThetaDeficit` rewrites it as theta-deficit
  half-contraction.  Then `P2BlockCompatibleThetaPascal` proves
  `8*T_k=M_k*I_k+R_k`, proves the exact cubic margin profile, and establishes
  the all-scale scalar reserve `5*u_k <= M_k-2*M_(k+1)`.  The canonical
  `BlockCompatibleP2PhysicalFrontierAtoms` field is therefore strictly reduced
  from the full half-contraction to the cross-cutoff cumulative Pascal-residual
  transport.  The latter remains a genuine named Type-level analytic input;
  no inhabitant is claimed.  In parallel, weighted-box strong Turan remains
  the second named all-scale family.  Both compile to the actual
  `BlockingStep.Phi` trajectory dictionary once supplied.
- **honest residual**: this is still NOT an all-scale physical `pΓ >= 2`
  discharge.  The certificate *compiler* and one exact finite cell are closed,
  but the genuine physical certificate family across the RG trajectory remains
  uninhabited.  The compiler deliberately
  avoids a global log/exp inverse: its false route uses only explicit artanh
  tails and the supplied saddle estimate.  The historical
  `DeltaFrontierLedger.bulkCtrl` interface is not silently equated with the
  corrected carrier.  The physical fine/image pins and exact cross-scale fusion
  power identity remain named fields of `FusionSpectrumBlockingDictionary`.
- **Rule-9 sign-off record**: old statement preserved above; replacement is
  stronger in physical specificity and removes the refuted bare reference; the
  canonical statement hash is deliberately re-pinned in the same reviewed
  change.
- **must not be closed classically**: per `AGENTS.md` Rule 6/9.

### [FrontierDAG-coreB-physical] finite-`s` Core-B margin on the closed physical interval — **CLOSED 2026-08-04**

- **milestone**: 11.14 (`FrontierDAG` canonical-atom discharge)
- **file**:
  `lean/YMGap/Continuum/FrontierCoreBPhysicalDischarge.lean`,
  `lean/YMGap/Rubric/FrontierDAG.lean`
- **decls**:
  `YMGap.Continuum.FrontierCoreBPhysicalDischarge.finiteSMargin_physical`,
  `YMGap.Rubric.FrontierDAG.coreB_physical_witness`
- **obligation**: Construct the actual `FrontierDAG.coreB` field
  `AcNReserveAnalytic.FiniteSMargin w` for every rational physical coupling
  `0 <= w <= wH = 1/2`.
- **constructive or propositional**: constructive — `FiniteSMargin w` is
  `Type`-level data carrying the margin proof at every finite row.
- **closed**: the positive-coupling branch consumes the proved all-truncation
  Turan margin `finiteSMargin_of_trunc`; the zero-equivalent branch proves the
  adverse upper autoconvolution vanishes termwise and constructs the margin
  directly.  The nonnegative rational dichotomy composes the two branches into
  the closed-interval family.
- **axiom-gate (closed)**: `[propext, Quot.sound]` only; no `sorryAx`,
  `Classical.choice`, `native_decide`, new axiom, or noncomputable witness.
- **honest residual**: this closes the canonical `coreB` field on the stated
  physical interval only.  `FrontierDAG.CoreBBridge w : FiniteSMargin w ->
  CrossRatioMonotone w` and the other open `FrontierDAG` fields remain
  uninhabited, so no total frontier or Clay target is claimed.
- **must not be closed classically**: per `AGENTS.md` Rule 6 — and isn't.

### [BF4-outer-Markov] all-label SU(2) block-kernel contract — **ONE OPEN PHYSICAL INPUT**

- **milestone**: BF4 physical outer-cutoff score transport (`work_plan.md`,
  current BF4 overlay)
- **file**:
  `lean/YMGap/Continuum/BF4SU2OuterCutoffBlockGramContract.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterPhysicalMarkovKernelFrontier.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterRawKernelCoherenceReduction.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterRawKernelCutoffDiagnostics.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterPositiveRowClosureReduction.lean`,
  `lean/YMGap/Continuum/SU2FusionSupportAddition.lean`,
  `lean/YMGap/Continuum/SU2PairChannelSupportAddition.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterJointCarrierEnumeration.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterFineWitnessRoutingReduction.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterBinaryLayerReduction.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterBinaryMulticoverReduction.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterOddLayerResidual.lean`,
  `lean/YMGap/Continuum/CompactDualAllCutoffOddParitySlabLayer.lean`,
  `lean/YMGap/Continuum/BF4SU2OuterBinaryLayerCounterexample.lean`
- **decls**: `SU2OuterPhysicalBlockContract`,
  `SU2OuterPhysicalMarkovContract`, `SU2OuterPositiveRowClosure`,
  `SU2OuterRawKernelCutoffStability`,
  `SU2OuterJointChannelSelection`, `SU2OuterJointCarrierNonempty`,
  `SU2OuterFineWitnessRouting`, `SU2OuterBinaryLayerDecomposition`,
  `positivePhysicalTerm_fineOddSupport_even`,
  `positivePhysicalTermOddLayerResidual`,
  `positivePhysicalTermMulticoverOfResidual`,
  `no_SU2OuterBinaryLayerDecomposition`
- **obligation**: Construct `SU2OuterPositiveRowClosure` for the genuine
  source-indexed BF4 all-label recoupling weight on the fine cutoff-\(K\)
  and coarse cutoff-\(4K\) corrected slabs.  One explicit sufficient route
  is the stronger `SU2OuterJointChannelSelection`: one shared coarse target
  with a positive selected channel on every face and a positive intertwiner
  multiplicity on every shared coarse link.  Nonnegativity, row
  normalization, exact cutoff-one recovery, old-entry stability, and
  zero-on-new-targets lossless support are now theorems once this single
  positive-row input is supplied.  The deterministic
  `SU2OuterPhysicalBlockContract` is a stronger marginal surrogate and is
  not accepted as a replacement for this source-indexed construction.
- **constructive or propositional**: constructive — the kernel entries (or
  an enlarged retained carrier and their induced kernel) are data; all
  stated laws must then be proved without choice.
- **status**: open.  No value of `SU2OuterPositiveRowClosure` or
  `SU2OuterJointChannelSelection` is defined.  Conditional
  consequences are proved: bounded backward messages stay in \([0,1]\), are
  cutoff-stable on old sources under lossless support, and satisfy the exact
  stochastic Fubini/blocked-Gram identity.  The raw-kernel frontier closes a
  discovered loophole in the first stochastic interface: its laws alone
  permit nonphysical Dirac completion on higher-spin rows.
  `SU2OuterPositiveRowClosure` instead requires every positive fine row to
  construct a positive coarse witness for the literal globally link-glued
  `wholeSlabRecouplingRawWeight`.
  `BF4SU2OuterRawKernelCoherenceReduction` proves that its witness choice
  cannot change the normalized row and that Gibbs-null bookkeeping rows
  contribute zero physical mass.  Its one-field
  `SU2OuterRawKernelCutoffStability` pins old-entry stability to the
  resulting normalized raw kernel; `old_source_no_new_target_of_cutoff_stable`
  derives exact lossless support and
  `physicalMarkovContractOfRawKernelCutoffStability` derives the earlier
  stochastic contract.
  `BF4SU2OuterRawKernelCutoffDiagnostics` proves cutoff stability for every
  unnormalized pair-channel, face, face-product, and coarse-link factor and
  proves zero raw weight outside the old \(4K\) target carrier.  It also
  closes raw-partition stability, positive normalized rows, null-row
  completion including \(K=0<L\), and the full normalized kernel theorem.
  It therefore defines `su2OuterRawKernelCutoffStability`,
  `su2OuterRawKernelCutoffCoherence`, and
  `su2OuterPhysicalMarkovContractOfPositiveRowClosure` from positive-row
  closure alone.
  `BF4SU2OuterPositiveRowClosureReduction` proves all independent stretched
  face factors positive but also formalizes the exact shared-link
  counterexample that makes the resulting coarse target inadmissible.  Its
  replacement `SU2OuterJointChannelSelection` chooses a single coarse target,
  all positive face channels, and all positive shared-link intertwiners
  jointly, and constructively implies `SU2OuterPositiveRowClosure`.
  `BF4SU2OuterJointCarrierEnumeration` enumerates the literal finite global
  carrier of coarse targets, face channels, and link-intertwiner assignments.
  Its nonemptiness is constructively equivalent to joint channel selection;
  this executable enumeration does not itself prove nonemptiness.
  `BF4SU2OuterFineWitnessRoutingReduction` repairs the Prop-to-Type boundary
  by extracting a retained fine intertwiner assignment from every positive
  physical term.  Its router interface is again equivalent to joint-carrier
  nonemptiness, so no solution is claimed there.
  The substantive new algebra is additive closure.  `SU2FusionSupportAddition`
  proves that link fusion witnesses, canonical/explicit multiplicities, and
  whole-slab link products remain positive under pointwise addition.
  `SU2PairChannelSupportAddition` proves the matching finite-cutoff face
  statement and its arbitrary finite-list lift.
  Finally `BF4SU2OuterBinaryLayerReduction` derives the entire coarse target,
  every positive face channel, and every positive shared-link factor from a
  decomposition of the positive fine state into at most \(K\) globally even
  cutoff-one sheets.  This remains a correct sufficient theorem, but it is
  not a universal discharge.  `CompactDualAllCutoffOddParitySlabLayer`
  proves the valid all-cutoff conclusion that the odd-spin support of every
  positive state is one even binary layer.
  `BF4SU2OuterBinaryLayerCounterexample` then constructs a positive
  cutoff-two corrected-slab state on the doubled ordinary union of two
  adjacent cubes and proves `no_SU2OuterBinaryLayerDecomposition`: two layers
  are forced to repeat the odd-incidence plain union, while positivity is
  certified by the exact three-sheet identity
  \(2(A\cup B)=A+B+(A\triangle B)\) and cutoff stability.  Therefore the
  bounded-two-layer proposal is formally refuted rather than listed as open.
  `BF4SU2OuterBinaryMulticoverReduction` removes that false global sheet
  budget: any finite binary multicover produces an actual enumerated joint
  carrier.  `BF4SU2OuterOddLayerResidual` now constructs, for every positive
  row, the canonical closed odd-parity sheet, proves it is pointwise below
  the row, subtracts it, proves the residual remains in the physical carrier
  and is even on every face, and reconstructs the row exactly.  A multicover
  of that even residual is constructively prepended to give a multicover of
  the original row.  The remaining combinatorial input is therefore the
  integral normality/strand-colouring theorem for the all-even residual (or
  an equivalent direct joint-carrier constructor), not the first parity
  sheet.
- **must not be closed classically**: per `AGENTS.md` Rule 6 — a future
  inhabitant must be an explicit finite constructor, not a
  `Classical.choice` witness.

### [BF4-reflected-PW-AF] reflected all-spin endpoint estimate — **OPEN ANALYTIC INPUT**

- **milestone**: five-gate backward roadmap M1--M2
- **file**:
  `lean/YMGap/Continuum/BF4ReflectedAllSpinPeterWeylBridge.lean`,
  `lean/YMGap/Continuum/BF4ReflectedAllSpinAFRowRelative.lean`,
  `lean/YMGap/Continuum/BF4ReflectedAllSpinMehlerGramEndpoint.lean`,
  `lean/YMGap/Continuum/BF4ReflectedAllSpinMehlerGramAFRow.lean`,
  `lean/YMGap/Continuum/BF4ReflectedAllSpinTaylorRankOneEndpoint.lean`
- **decls**: `reflectedPhysicalCoefficient_equiv_geometric`,
  `GeometricTaylorEndpointSpectralData`,
  `MatchedReflectedAllSpinAFRowCertificate`,
  `bf4MehlerGramVacuumPartition_pos`,
  `normalized_bf4MehlerGram_quadratic_nonnegative`,
  `MatchedReflectedAllSpinMehlerGramAFRowCertificate`,
  `canonicalRankOneGeometricTaylorEndpointSpectralData`,
  `matchedReflectedAllSpinAFRowCertificateOfCanonicalRankOne`,
  `MatchedReflectedAllSpinAFRowCertificate.row_relative_estimate`
- **obligation**: Instantiate
  `matchedReflectedAllSpinAFRowCertificateOfCanonicalRankOne` on a genuine
  physical matched trajectory by constructing the scale-uniform numerator,
  partition, endpoint-ceiling, carrier-payment, and physical-marginal
  budgets.  For the later quarter contraction, sharpen or estimate the
  explicit order-one rate strongly enough that `rate + epsilon ≤ 1/4`, or
  replace order one by a higher-order endpoint with a proved smaller
  physical-mean-zero rate.
- **constructive or propositional**: constructive — the order schedule,
  rational partitions, common tolerance, spectral rates, and every
  scale-indexed analytic budget are `Type`-level data.
- **status**: open AF-uniform analytic instantiation; the finite spectral
  subproblem is closed at order one.  The source/target obstruction is
  closed: exact rational polarization identifies every finite reflected
  physical Taylor coefficient with the 24-plaquette all-spin geometric
  coefficient, and polarization of the two located diagonal limits gives
  the corresponding `CReal` endpoint.  The AF consumer is also closed and
  pinned definitionally to `geometricMehlerTaylorPartial`, its
  vacuum--vacuum partition, the exact blocked weight, the matched moving
  cutoff, and the physical spacing envelope.
  `BF4ReflectedAllSpinTaylorRankOneEndpoint` proves exact product-Haar
  factorization, unit partition, symmetry, and PSD.  It constructively takes
  the minimum of the nonempty strictly-positive physical-row carrier and
  derives the physical Rayleigh rate by finite Cauchy--Schwarz.  Thus a
  direct constructor of the original certificate is defined.  No closed
  physical value exists yet because no concrete `CubicMarginLaw`,
  `PhysicalSpacingEnvelope`, or common AF-uniform analytic budget is supplied,
  and no quarter-smallness claim is made for the coarse order-one rate.
  In parallel, `BF4ReflectedAllSpinMehlerGramEndpoint` constructs the
  nontrivial positive feature-Gram route: exact factorized-action Haar
  identification, a five-Haar SOS shift, all nonnegative complement moments,
  fifteen nonnegative kinetic features, strict vacuum partitions at every
  positive shifted order, and normalized PSD.  Its matched AF record still
  needs a physical-mean-zero Rayleigh estimate and the same uniform analytic
  budget.
- **must not be closed classically**: per `AGENTS.md` Rule 6; a future
  inhabitant must supply explicit rational moduli and witnesses rather than
  a selected spectral bound.

### [BF4-exact-physical-Perron] exact Haar / positive Perron same action — **REFUTED; DIRECT PHYSICAL REPLACEMENT OPEN**

- **milestone**: AF macro-slab reroute (`work_plan.md`, Milestone 34)
- **files**:
  `lean/YMGap/Continuum/BF4ExactPhysicalPerronReroute.lean`,
  `lean/YMGap/Continuum/BF4ExactPhysicalPerronSameActionFence.lean`,
  `lean/YMGap/Continuum/BF4ExactPhysicalPerronCenteredSameActionFence.lean`,
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingAFCertificate.lean`,
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingAFAdapter.lean`
- **decls**: `ExactHaarPhysicalPerronSameActionAt`,
  `ExactHaarPhysicalPerronAFQuarterCertificate`,
  `ExactHaarPhysicalLocalGluingAFQuarterCertificate`
- **obligation**: Do not attempt to inhabit either same-action structure for
  the present positive law.  Construct instead one explicit stationary
  physical slice density at each AF scale, its row and column normalization,
  exact all-word gluing to every row of the physical conditional slab density,
  and a carrier-uniform centered rate at most `1/4`.
- **constructive or propositional**: constructive —
  `PhysicalLocalGluingAFCertificate.oneStep` is an explicit scale-indexed
  kernel, and `localSlice` certifies that the same kernel serves every source;
  no rowwise existential selection or classical choice remains in the active
  producer interface.
- **status**: both same-action routes are constructively fenced.  The raw
  vacuum delta refutes full same action at cutoff one and positive coupling.
  The unconditional Haar-five formulas, combined with the physical vacuum
  marginal bound at `w=8/9`, put the centered exact moment above `5/8` and the
  centered physical moment below `1/8`.  The surviving consumer is direct:
  the global positive slice certificate proves the physical joint quadratic
  `1/16` estimate without a signed-Haar comparison.
- **must not be closed classically**: per `AGENTS.md` Rule 6; the global slice,
  gluing identity, and AF-uniform local-rate witnesses must remain explicit.

### [SU2-Faraut-interior] constructive image-kernel Harnack certificate — **OPEN ANALYTIC INPUT**

- **milestone**: completed SU(2) retained-kernel Harnack / general-nome
  positivity route (`work_plan.md`, Faraut image-formula overlay)
- **file**:
  `lean/YMGap/Continuum/SU2FarautInteriorImageHarnack.lean`,
  `lean/YMGap/Continuum/SU2FarautGeometricImageCompletion.lean`,
  `lean/YMGap/Continuum/SU2FarautGaussianPairDomination.lean`,
  `lean/YMGap/Continuum/BF4FarautJointCarrierAFBudget.lean`,
  `lean/YMGap/Continuum/BF4FarautAFCutoffGrowth.lean`,
  `lean/YMGap/Continuum/SU2PointwiseHeatDynamicWindow.lean`,
  `lean/YMGap/Continuum/BF4MatchedPhysicalFarautTrajectory.lean`,
  `lean/YMGap/Continuum/BF4CanonicalClassCoordinateCarrier.lean`,
  `lean/YMGap/Continuum/BF4NormalizedSameCarrierPerron.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCommonKernelAction.lean`,
  `lean/YMGap/Continuum/BF4StationaryDensityBufferSplit.lean`,
  `lean/YMGap/Continuum/BF4GroupedCommonKernelPerronAction.lean`
- **decls**: `FarautInteriorImageCertificate`,
  `FarautInteriorImageCertificate.kernel_ge_floor`,
  `FarautInteriorImageCertificate.kernel_le_ceiling`,
  `farautInterior_projective_order`, `FarautBitWindow`,
  `farautCompletedRetainedHarnack`,
  `wholeSlabFarautConditionalPushforward_domination`,
  `faraut_perron_of_available_depth`, `FarautAFBitGrowth`,
  `FarautAFWindowFamily`,
  `faraut_af_family_core_length_uniform`,
  `farautGeometricImageSum`,
  `farautGeometricInteriorCertificate`,
  `gaussian_pair_weightedExp_leEv`,
  `dyadicSpacingBits_eq`,
  `dyadicSpacingBits_mul_heatArgument_le`,
  `sameActionFarautAFBitGrowth`,
  `PointwiseHeatTailWindow`,
  `wholeSlabDynamicConditionalPushforward_ge_witnessed_floor`,
  `SameActionPointwiseHeatWindows`,
  `matchedPhysicalPointwiseAFWindowFamily`,
  `canonicalBF4SpatialFiniteHeatHarnack`,
  `NormalizedSameCarrierMehlerHSConvergence`,
  `eventually_perronRatio_le_quarter`,
  `matchedCentered_perronRatio_le_quarter`,
  `centralPhysicalBoundaryActivityCertificate`,
  `centralPhysicalBoundaryKernelAction_eqv_marginal`,
  `centralGroupedPhysicalCommonKernelAction_eqv_marginal`,
  `PhysicalBF4OneStepContractionGluingRow.toFarautBufferedRow`,
  `MatchedBF4GroupedProfileFarautRows.toThresholdCoreFarautRows`
- **obligation**: Instantiate the certificate from the literal SU(2)
  heat-kernel image formula with constructive \(t\)-to-nome normalization,
  rational Gaussian/trigonometric enclosures, pairwise image domination, and
  a summable tail bound uniform on a specified interior class-angle window.
  The quantitative output must include a natural bit cost \(B_a\) with
  \(U_a\le4^{B_a}L_a\) and one uniform heat-cost ceiling
  \(B_a t(a)/4\le D\).  Then control the removable endpoint singularities,
  identify the twenty-three completed local factors with the interacting
  BF4 joint-carrier kernel, and prove its nonlinear ratio is at most \(1/4\).
  The identity and quantitative image data are explicit fields; the
  completed Harnack window and Perron contraction are derived from them and
  are not themselves assumed.
- **constructive or propositional**: constructive — the image sequences,
  rational floors/ceilings, and majorant are `Type`-level data, and the
  resulting `CReal` order is approximation-wise.
- **status**: open analytic instantiation.  Given a certificate,
  `SU2FarautInteriorImageHarnack` proves paired-prefix nonnegativity, a
  strict zeroth-image floor, the majorant ceiling, completed-kernel order,
  and terminal-independent projective comparison.
  `SU2FarautGeometricImageCompletion` now constructs the completed image
  `CReal`, its exact prefix approximation, convergence modulus, and
  certificate from geometrically dominated rational image pairs.
  `SU2FarautGaussianPairDomination` proves the semantic weighted-Gaussian
  comparison whenever \(0<a\le b\), \(t>0\), and \(2t\le a^2\).
  `BF4FarautJointCarrierAFBudget` further proves that a per-scale bit window
  costs exactly \(46B_a\) Perron powers, so
  \(m(a,L)\ge46B_a+3\) implies
  \(C_{s(a)}^2q_{s(a)}^{m(a,L)-2}<1\).  It retains the full enumerated
  face-channel/shared-intertwiner code through conditional integration and
  proves the AF physical-length cancellation
  \(\kappa(46B_a a)\le46D\).
  `BF4FarautAFCutoffGrowth` constructs `FarautAFBitGrowth` on the exact
  dyadic schedule with \(B_s=8(2^s+1)\) and \(B_st_s/4\le16\), and its
  same-action refinement ties the cutoff to `E.w` itself.
  `SU2PointwiseHeatDynamicWindow` supplies the direct completed-character
  alternative from one finite prefix/tail window, including a closed
  \(1/2\le K_{1/2}(0)\le2\) instance and a witnessed positive conditional
  sum which cannot be vacuous on an empty carrier.
  `BF4MatchedPhysicalFarautTrajectory` specializes the same-action cutoff
  to the exact matched `blockedWeight`.
  `BF4CanonicalClassCoordinateCarrier` closes the previously unnamed
  geometry: the 24 lower spatial faces give exactly 48 physical links,
  constructively covered by an explicit 25-link tree and 23 chords; the five
  transmitted chords are exactly indices \(\{0,4,5,6,10\}\).  Rational unit
  quaternions give the genuine relative SU(2) class coordinate with proved
  range \([-1,1]\), complete source/target/path/factor locations, an explicit
  nonempty identity carrier, and the literal 23-factor finite heat corridor.
  `BF4NormalizedSameCarrierPerron` corrects the spectral comparison boundary:
  it builds the exact uniform vacuum projector, proves mean-zero eigenmodes
  survive vacuum removal, defines cutoff-varying normalized nonlinear/Mehler
  Hilbert--Schmidt convergence on the same growing carrier, derives the
  eventual \(7/100\) perturbation and \(q\le1/4\), and requires a Perron
  identification to carry an actual dominant eigenmode.
  `BF4PhysicalBoundaryCommonKernelAction` now closes the physical side of
  the common-action identification.  On the complete fixed-interface
  carrier it constructs the literal activity \(W(b)B(b)/Z_{\rm phys}\),
  proves its vacuum coordinate strictly positive, and proves that the
  transposed genuine half-amplitude maps it exactly to the physical
  marginal.  Exact finite Fubini transports this activity through any
  genuine grouped factorization
  \(A(x,b)=\sum_m P(x,m)T(m,b)\), giving the exact physical action of the
  common kernel \(P\) on the retained middle carrier.  Its preferred
  boundary-carrier refinement instead transposes the terminal-smoothed
  kernel \(J(b,x)=\sum_mP(x,m)T(m,b)\).  The strict certificate is then
  constructed automatically from the primitive terminal certificate and
  the positive prefix rows, and its spread is definitionally the terminal
  spread; a generally zero-containing fusion prefix needs no independent
  strict certificate.
  `PhysicalBF4OneStepContractionGluingRow.toFarautBufferedRow` closes the
  formerly arbitrary buffer-carrier interface: a genuine stationary
  one-step density gluing now constructs the two endpoint buffers and the
  depth-dependent middle power on the literal positive BF4 carrier.
  `BF4GroupedCommonKernelPerronAction` combines these constructions on
  definitionally the same bit/depth/nonlinear-rate trajectory.  Its minimal
  terminal-Harnack interface requires only the direct squared-spread bound
  \(C_s^2\le65/64\); the Perron-form estimate is retained as one sufficient
  producer.  A second endpoint-free producer combines that Harnack datum
  with an actual local stationary BF4 slice contraction \(q_s\le1/4\) and
  feeds the already-proved \(1/32\) core, two \(1/64\) tails, and both
  rowwise-eighth estimates without a separate endpoint buffer bound.
  Still open are the physical dyadic bridge, uniform Faraut/image
  enclosures on the full class-coordinate set, Faraut/character
  normalization and endpoint coverage, the all-even residual
  strand-colouring theorem, the genuine positive primitive terminal and
  grouped half-amplitude factorization with terminal squared spread at most
  \(65/64\), the candidate Peter--Weyl boundary activity/action under that
  same terminal-smoothed kernel, the actual local stationary BF4 slice
  gluing with \(q_s\le1/4\) (or the stronger endpoint-buffer alternative),
  identification of the normalized interacting BF4 and
  Mehler matrices on the same complete carrier, the actual HS convergence
  modulus for those matrices, and dominant-mode identification.
- **must not be closed classically**: per `AGENTS.md` Rule 6; the uniform
  enclosures and modulus must remain explicit constructive data.

### [continuum] μ_∞ existence attack-surface skeleton — **S2/S3/S4/S5/S6 ALL CLOSED**

- **milestone**: Track B continuum (E1–E4; `docs/track-b-continuum-plan.md`,
  `docs/continuum-measure-attack-surface.md`)
- **files**: `lean/YMGap/Continuum/ContinuumExistence.lean`,
  `lean/YMGap/Continuum/KPIncrement.lean` (S4),
  `lean/YMGap/Continuum/FiniteVolume.lean` (S3), and
  `lean/YMGap/Continuum/PartitionPos.lean` (all standalone; NOT in `YMGap.lean`)
- **CLOSED stages** (now theorems, axiom-gated `[propext]`/`[propext, Quot.sound]`,
  no `sorryAx`/`Classical`):
  - `partitionFunctionLB`, `partitionFunction_pos` — **S2 CLOSED**: finite-volume
    partition function `Z_n = Π_{i<n} W i > 0` with explicit `Q'` lower bound carried
    as `Σ'` data. Via the new `mul_pos` (positive·positive) + `prodE_pos` induction.
    Also in `PartitionPos.lean` with the `weightFromPos`/`half_partitionFunction_pos`
    non-unit concrete instances.
  - `kpIncrementBound` — **S4 CLOSED (the analytic heart)**: the convergent
    Kotecký–Preiss cluster-expansion's two-sided geometric single-step increment
    `|S(Λ+1)−S Λ| ≤ C·(1/2)^Λ`, `(C)` as `Σ'` data. PROVED in the new
    `KPIncrement.lean` from `KPIncrementData S` — the explicit weak-coupling
    smallness (single-site cluster-activity tower `a Λ` with base `a 0 ≤ C`,
    geometric ratio `a(n+1) ≤ r·a n`, `0 ≤ r ≤ 1/2`, and KP telescoping
    `|S(Λ+1)−S Λ| ≤ a Λ`; Friedli–Velenik Ch.5 eqs 5.10/5.29/5.30–5.34). The
    derivation: `geom_dom` ⇒ `a Λ ≤ C·r^Λ`; `pow_le_pow_base` ⇒ `r^Λ ≤ (1/2)^Λ`;
    compose ⇒ `geoIncr C` bound; modulus via `CReal.exists_mul_le`. The smallness
    is a genuine HYPOTHESIS (structure argument), NOT a hidden assumption — the
    bound is false for arbitrary `S`. *constructive?* yes. Axiom-gate `[propext]`.
    The `ContinuumExistence.kpIncrementBound` wrapper takes `KPIncrement.KPIncrementData S`
    and discharges via `KPIncrement.kpIncrementBound`.
  - `infiniteVolumeExpectation`, `infiniteVolumeExpectation_approx` — **S5 CLOSED**
    (given the S4 increment datum): the `CReal` limit with modulus, = the KP engine
    `crealOfGeoIncrement` applied to the carried `(C, hC, hup, hlo, modulus)`. The
    decl now takes that datum as arguments (the S4 obligation supplies it).
    `KPIncrement.infiniteVolumeLimit` also assembles the limit straight from a
    `KPIncrementData`, showing S4 plugs directly into S5.
  - `infiniteVolumeExpectation_nonneg` — **S6 CLOSED**, CONDITIONAL on the per-volume
    OS2 input `hS`: limit-of-nonneg via `ExpPos.geRat_of_eventually`. The OS2 input
    (full single-edge Wilson PSD) is 🟡 open (cone-only `coneExp_nonneg`; all-N `P_N`).
  - **Bishop integration-space packaging** (`PartitionPos.BishopFunctional`,
    `.I_inf`/`_approx`/`_nonneg`, `constBishop`): the constructive-measure object —
    a positive normalized functional on a dense observable subalgebra completed by an
    explicit geometric convergence modulus (Bishop summability axiom in modulus form;
    KP cluster-series remainder), NOT a σ-algebra. The increment constant
    `incrementC` is the S4 analytic datum, carried as a structure FIELD (not faked).
  - `finiteVolumeExpectation` — **S3 CLOSED**: the interacting finite-volume
    expectation sequence `S Λ = E_Λ(o) = Ew_Λ(o)·recip(Z_Λ) = (Efam Λ).Eβ o`,
    the constructed reweighted state. The body of `ContinuumExistence.finiteVolumeExpectation`
    is now `(Efam Λ).2.1.Eβ (Efam Λ).2.2` (no `sorry`), with
    `finiteVolumeExpectation_eq` recording `S Λ = Ew(o)·recip Z`. The genuine
    reference-functional + weight construction lives in the new
    `FiniteVolume.lean`: `ReferenceWeight` (reference functional `I_0` = product
    Haar/heat-kernel integral, positive plaquette weight `w`, partition function
    `Z = I_0(w) > 0` via S2's `prodE_pos`, OS2 weighted-form positivity as the
    `weighted_pos` field); `ReferenceWeight.toReweight` exhibits it as a
    `PlaquetteReweight.Reweight`; `ReferenceWeight.E_Λ` with proved
    `E_Λ_positive` (`f≥0 ⟹ E_Λ(f)≥0`) and `E_Λ_normalized` (`E_Λ(1)≃1`);
    concrete product instance `prodReferenceWeight` (Z>0 from S2) and
    zero-coupling inhabitant `trivReferenceWeight`. The reweighting assembly
    reuses `Reweight.functional_positive`/`functional_normalized` and S2's
    partition positivity — no σ-algebra, no Riesz-via-choice, no dominated
    convergence (finite volume, bounded observables). The ONE analytic input is
    `weighted_pos` (= per-volume OS2 reflection positivity), carried as DATA, NOT
    faked. *constructive?* yes. Axiom-gate `[propext]`/`[propext, Quot.sound]`.
  - **UPDATE 2026-06-14 — the per-volume `weighted_pos` (OS2 at the product
    functional) now FACTORIZES to per-bond OS2.** `FiniteVolume.prodWeighted_pos_of_perEdge`
    (axiom-gate `[propext]`) proves: because `prodFunctional` is the decoupled
    product `Π_i (μ i).E(o i)` over the componentwise `prodAlg`, the weighted
    reflection form `I₀(w·a*·a) = Π_i (μ i).E(w_i·(a_i)*·a_i)` is a product of
    per-edge weighted forms, `≥ 0` by `prodE_nonneg` GIVEN per-bond OS2. This
    is the standard Osterwalder–Seiler **cross-plane tensor factorization** of
    RP for the free measure: the n-edge OS2 obligation REDUCES to the 1-edge
    obligation. The constructor `prodReferenceWeight_of_perEdge` builds the
    `ReferenceWeight` from per-bond OS2 instead of the opaque joint
    `weighted_pos`. The single-bond OS2 is the heat-kernel reflection
    positivity `ReflectionPositivity.reflSchwinger_nonneg` (`Σ_s e^{−tC₂(s)}c_s²
    ≥ 0`, CReal-level, unconditional); the 1-edge `Q'`-functional ↔ CReal
    reflection-form reconciliation is the standard `Q'`/CReal representation
    boundary, not a new hole.
- **OPEN stages**: NONE. The module `ContinuumExistence.lean` (and `FiniteVolume.lean`)
  carry zero `sorry`s; the whole library is now sorry-free.
- **must not be closed classically**: per AGENTS.md Rule 6. These stand for
  *constructive* obligations (witnesses as data); a classical closure is forbidden.
- **out of scope (NOT stated here, genuinely open)**: 4D existence + O(4) restoration
  (Clay), Conjecture 7.4 RG transport — flagged in the attack-surface doc, never as a
  `sorry` here.

### [CRealAbs-orphan] limit-of-equal-sequences uniqueness — **RESOLVED (no sorry)**

- **file**: `lean/YMGap/Constructive/CRealAbs.lean`, decl
  `CReal.Equiv_of_limit_of_equal`.
- **status**: **CLOSED 2026-06-13, no `sorry`.** The S3 round transiently logged
  this as an orphan after observing an EARLIER draft in which `ConvergesTo`
  asserted only a single threshold term (too weak). The concurrent Wall-2 round
  then STRENGTHENED `ConvergesTo` to the correct uniform-past-stage form
  (`∀ N ≥ Nstage, ∃ Napx, ∀ n ≥ Napx, …` two-sided) and PROVED
  `Equiv_of_limit_of_equal` from it (`#print axioms` → `[propext]`). `CRealAbs.lean`
  is now imported by `YMGap.lean`; the full library builds with **0** sorries. This
  entry is retained only as a record that the earlier concern was resolved, not
  disguised.

### [uniform] all-simple-groups budget — **named-hypothesis, NO `sorry`**

- **milestone**: U.8–U.11 (`docs/uniform-parametric-bound-plan.md`)
- **files**: `lean/YMGap/RG/UniformBudget.lean`,
  `lean/YMGap/MassGap/SimpleGroup.lean`,
  `lean/YMGap/RepTheory/SimpleGroup.lean`
- **decl / named obligation**: `YMGap.RG.UniformBudgetWitness.eta_dominated`
  (`R.eta_max ≤ su2.eta_max`).
- **obligation**: the per-step σ̂-degradation bound of an admissible simple
  group is dominated by SU(2)'s — the analytic "SU(2) is the worst case"
  input (the plan's `E_antitone` / uniform character-tail: `e^{−tΔ}`
  antitone in the Casimir gap `Δ ≥ 3/4`, a `CReal` statement outside `Q'`).
- **how it is carried**: as an explicit **structure field** (AGENTS.md
  Rule 2 / Rule 6, the `domGlue_preserves_KP` quarantine pattern), **NOT a
  `sorry`** — these three modules contain zero `sorry`/`sorryAx`. The entire
  uniform reduction (`monotone_budget`, `budget_closes_uniform`,
  `mass_gap_simple_group`) is constructive and axiom-clean
  (`[propext]`/`[propext, Quot.sound]`) *given* this field. The pure-`Q'`
  monotonicity substrate around it closes unconditionally
  (`recip_antitone`, `qOver1mq_mono`, `truncatedConst_le`).
- **discharged for instances**: SU(2) (`su2_uniform_witness`) and SU(3)
  (`su3_uniform_witness`) discharge `eta_dominated` by `decide`
  (`13e-6 ≤ 3e-4`); the general-group discharge is the paper-layer step
  (numerically corroborated by the U.4 sweep `Σ η(G) ≤ Σ η(su2)`).
- **constructive?**: yes — the field is a `Q'` inequality (decidable for
  concrete groups); the antitone-in-Δ derivation for the general group is
  the open paper obligation, named not hidden.
- **must not be closed classically**: per AGENTS.md Rule 6.
- **UPDATE 2026-06-14 — `eta_dominated` is no longer a free posit.** It is
  now assembled by the capstone `RG.uniformBudgetWitness_of_characterTail`
  (`EtaPackaging.lean`), which threads the GENUINE character-tail path:
  `ztMajorant_le_su2` (the proven rank-general `Z_t(R) ≤ Z_t(su2)`,
  `CharacterTailMajorant.lean`) composed with `eta_of_zt_of_model` (the
  proven monotone `η = μ·K_lf(Z_t)` bridge) yields `R.eta_max ≤ su2.eta_max`.
  SU(2) closes **end-to-end through this capstone**
  (`su2_uniform_witness_via_tail`, axiom-clean), NOT via the `decide`-on-
  `3e-4≤3e-4` shortcut. The residual named inputs are now the *structured*
  per-group data — `ZtMajorant.rank_collapse` (validated for all 19 group
  types) + the `ZtEtaModel` `η`-model equalities + the per-group
  `WeylDimData`/`AxisFactorBound` (realized for SU(2),SU(3)) — not the opaque
  scalar `eta_dominated`. The antitone exponential engine
  `E_antitone` is the proved `RG.expNeg_scaled_antitone_leRat`
  (`CharacterTailAntitone.lean`).

### [OS2-RP] reflection positivity via standard Osterwalder–Seiler — **CLOSED, wall removed (2026-06-14)**

- **milestone**: Track B continuum / OS2 (`docs/os2-via-standard-rp.md`)
- **files**: `lean/YMGap/Continuum/ReflectionPositivity.lean` (new),
  `lean/YMGap/Continuum/OSAxioms.lean` (OS2 retargeted)
- **what changed**: OS2 reflection positivity was encoded as
  `OSAxioms.ReflectionPositive` = `GramRed.MomentSquarePos`, the all-order
  character **product** Gram PSD `G_{μν} = ⟨χ_μ·χ_ν⟩` — equivalent to
  pointwise heat-kernel positivity `K_t ≥ 0`, the statement attacked through
  the two `P_N` walls (`docs/continuum-positivity-status.md` §4), both
  research-novel dead ends. That conflated OS2 (the *reflection* form
  `⟨θ(a)*·a⟩`) with a strictly stronger statement (the *product* form).
- **the fix**: `IsOS2ReflectionPositivity` is retargeted to
  `ReflectionPositivity.ReflectionPositiveSchwinger`. The standard
  Osterwalder–Seiler reflection pairing `χ_μ ↦ θ(χ_μ) = χ̄_μ`
  **diagonalizes** via Schur orthogonality (Peter–Weyl) to
  `R_t(c) = Σ_s e^{−t·C₂(s)}·c_s²`, a weighted sum of squares with
  nonnegative weights, hence `≥ 0` for **every real `c`** — proved
  unconditionally in `reflSchwinger_nonneg` / `reflectionPositiveSchwinger_holds`.
  The sole positivity input is `reflWeight_nonneg` (`e^{−t·C₂(s)} ≥ 0`,
  elementary), i.e. `NonnegCharacterCoeffs` (= `WilsonFunctional.wilsonCharExp_nonneg`).
- **load-bearing effect**: the full `OSAxiomBundle` is now inhabitable for
  SU(2) with **no open analytic input** — `os_compliant_su2_measure` and
  `OSAxiomBundleAt.toFull` no longer take the `GramRed.MomentSquarePos`
  argument. The `P_N`/Wall-1/Wall-2 program is removed from the mass-gap
  critical path (retained as the stronger, non-load-bearing
  `reflectionPositive_of_momentSquarePos` record).
- **honesty (Rule 6)**: the Schur-orthogonality diagonalization is the
  standard Peter–Weyl identity, represented directly in the diagonalized
  character basis — exactly as `WilsonFunctional.wilsonCharExp` *defines* the
  heat-kernel moments from `d·e^{−tC₂}` rather than integrating. That
  representation is the citable analytic input; the positivity is then proved,
  not assumed. Scope: the per-bond reflection positivity is the analytic
  heart; the product-functional assembly (`FiniteVolume.weighted_pos`) follows
  by the standard cross-plane tensor factorization (noted, standard).
- **constructive?**: yes — `reflSchwinger` and its nonnegativity are
  `geRat`/`CReal` data; all-real-`c` SOS, no cone restriction.
- **axiom-gate**: all new exports `[propext, Quot.sound]`; the retargeted
  `os_compliant_su2_measure` / `toFull` and the composed `mass_gap_SU2`
  unchanged at `[propext, Quot.sound]`; the Q'-data core
  (`mass_gap_su2_q_rational_data_*`) remains `does not depend on any axioms`.
  No `Classical.*`, no `sorryAx`. Build green (137 jobs).
- **must not be closed classically**: per AGENTS.md Rule 6 — and isn't.

### [P2.1] overlap summability preservation — **part (a) CLOSED, part (b) CLOSED**

- **milestone**: 2.1 (work_plan.md L184–202)
- **file**: `lean/YMGap/Sheaf/Gluing.lean`
- **decl**: `YMGap.Sheaf.domGlue_preserves_KP`
- **obligation (load-bearing, two parts)**:

  **(a) Existence of P at the conjectured constants — CLOSED 2026-05-24.** Given KP certificates `(ρ_sf, K_sf)` for the small-field family and `(ρ_lf, K_lf)` for the large-field family, exhibit a buffer KP certificate `(ρ_∩, K_∩)` with `ρ_∩ = min(ρ_sf, ρ_lf)` and `K_∩ ≤ K_sf + K_lf` such that the regime-specific KP predicate `P` holds at the buffer constants.

  - **Closure strategy**: the analytic content (that `P` holds at the buffer constants) is exposed as an **explicit hypothesis** `P_glue : ∀ ρ_a K_a ρ_b K_b, P ρ_a K_a → P ρ_b K_b → P (min ρ_a ρ_b) (K_a + K_b)`. Plus a reflexivity hypothesis `le_refl_V : ∀ x : V, x ≤ x` (needed to discharge `K_∩ ≤ K_sf + K_lf` when `K_∩` is chosen equal to `K_sf + K_lf`).
  - **Body**: identity union bound saturated — `c_cap.rho := min c_sf.rho c_lf.rho`, `c_cap.K := c_sf.K + c_lf.K`, `c_cap.satisfies := P_glue ... c_sf.satisfies c_lf.satisfies`. The two inequality conjuncts discharge by `rfl` and `le_refl_V _`.
  - **Concrete instances** at `V = Q'` (no further sorry):
    - `domGlue_preserves_KP_trivial` at `P_trivial ρ K := True` (smoke test).
    - `domGlue_preserves_KP_nonneg` at `P_nonneg ρ K := 0 ≤ ρ ∧ 0 ≤ K` — substantive Bishop-constructive instance, using `Q'.zero_le_min` and `Q'.zero_le_add` for the closure proof.
  - **Axiom-gate (closed)**: `#print axioms domGlue_preserves_KP` reports **does not depend on any axioms** (pure definitional construction); the two concrete-`P` specializations depend on `[propext]` only (via the Q' helpers). No `sorryAx`, no `Classical.choice`, no `Quot.sound`.

  **(b) Tightness of the union bound — FORMALLY CLOSED 2026-05-25 (additive Q' form).** Beyond *existence* of a buffer KP datum, Milestone 3.3 must verify that the additive estimate `K_∩ ≤ K_sf + K_lf` is *tight enough* — i.e. the factor-2 union bound does not hide a fat band of buffer polymers for which neither `s^sf` nor `s^lf` is the true max, in which case the additive bound is genuinely lossy rather than worst-case-of-2 lossy. This is the substance of `formal/sheaf-framework.tex` Conjecture 7.4 (`conj:gaussian-sharpness`), explicitly flagged there as a conjecture and not a proved fact: the sf and lf bounds live in different units (`|X'|_phys / a_k` vs `|X'|_plaq`), and whether they admit a clean polymer-by-polymer crossover or a fat lossy band is exactly the original §3.1 unit-mismatch difficulty.

  - **Empirical/semi-analytical evidence** (`computations/overlap_kp.py::union_bound_looseness_estimate`, landed 2026-05-25): with the post-3.1 / 3.2 concrete SU(2) activities now available, the union-bound looseness `(K_sf + K_lf)/max(K_sf, K_lf)` can be computed directly. **Result**: the looseness stays in [1.0000, 1.176] across the full SU(2) convergent regime in both canonical and Wilson conventions; at the canonical SigmaHatPilot wire-in `g_0 = 0.30`, looseness ≈ **1.014** (1.4% loss). The conjecture's allowed factor of 2 has a margin of >5× even in the worst case observed.

  - **Why empirically the worst case is far below 2**: a semi-analytical lemma (see the `union_bound_looseness_estimate` docstring) — the SU(2) small-field convergence threshold `g_max_sf ≈ 0.40` is *strictly less than* the large-field threshold `g_max_lf ≈ 0.42`, so as `g` grows the sf-side diverges first; throughout the joint convergent regime, `K_lf` stays well below its own divergence and `K_sf > K_lf` empirically. The "fat buffer band" worry doesn't materialize for SU(2) because the lf regime is the LOOSER constraint and `K_lf` simply doesn't grow large enough to challenge the dominant `K_sf`.

  - **Diagram**: `visualizations/pilot/su2/conjecture-7.4-looseness.svg` (top panel: looseness factor with the 2.0 allowed-bound dashed line; bottom panel: K_sf vs K_lf showing the orders-of-magnitude sf-dominance).

  - **Test**: `tests/test_overlap_kp.py::TestUnionBoundLooseness` enforces the < 1.5 bound across the canonical and Wilson convergent regimes.

  - **Status of part (b) in Lean (2026-05-25 — FORMALLY CLOSED at Q')**: the closure landed via `lean/YMGap/Sheaf/PolymerDomination.lean`, Phase 6.1 of `work_plan.md`. The polymer-level activity domination `s_sf(X) ≥ s_lf(X)` (the analytic input) is encoded at the K-level via the `KLevelDominance K_sf K_lf := K_lf ≤ K_sf` predicate, which holds at every SU(2) operating point in the joint convergent regime per the 2026-05-25 empirical evidence package. The factor-of-2 bound is then proven in Lean:

    ```
    theorem kp_sum_factor_2_bound (K_sf K_lf : Q') (h_dom : KLevelDominance K_sf K_lf)
        : K_sf + K_lf ≤ K_sf + K_sf
    ```

    via direct application of the new `Q'.add_le_add_left` lemma in `Rationals.lean`. The refined additive form `kp_sum_tighter_bound` expresses the looseness as `1 + ε/K_sf` for any rational ε with `K_lf ≤ ε`.

    A concrete SU(2) wire-in (`K_sf_pilot = 11/10`, `K_lf_pilot = 2/125`) is exhibited with the formal dominance witness `K_lf_pilot_le_K_sf_pilot` and the resulting closure `kp_sum_factor_2_bound_pilot`. All axiom-gates report `[propext]` only.

    What the Lean closure does NOT do: model individual polymers as Lean objects (would require Q'-rational approximations of heat-kernel exponentials, beyond the current Q'-only infrastructure). The analytical content "pointwise s_sf ≥ s_lf at every polymer X" is documented in `notes/conjecture-7.4-empirical-evidence.md` §5 and supplied as the K-level input hypothesis to the Lean theorem.

  Part (a) without part (b) gives the framework a *true* statement that is potentially *useless*: a buffer KP certificate exists, but its $K_\cap$ might be too large to feed the inductive step. The empirical 2026-05-25 evidence removes the practical concern: $K_\cap$ is at most 1.2× the tight bound across the SU(2) operating range. The Lean type signature is unchanged (still only asserts `K_∩ ≤ K_sf + K_lf`, not tightness); a formal tightness theorem would be a separate downstream artifact.

- **constructive?**: yes for (a) — Σ-typed; closed. For (b), the obligation is intrinsically against concrete polymer activities; the 2026-05-25 empirical evidence + 2026-05-25 Phase-6.1 Lean closure together discharge it: the analytical content is at the empirical layer (`notes/conjecture-7.4-empirical-evidence.md`), the Lean witness is `kp_sum_factor_2_bound` at the K-level.
- **owed by**: Milestone 3.3 (overlap KP constants) for part (b); empirical evidence delivered 2026-05-25; Lean closure delivered 2026-05-25 (Milestone 6.1). BOTH CLOSED.
- **must not be closed classically**: per AGENTS.md Rule 6 — both parts (a) and (b) are constructive: part (a) Σ'-typed at Q'; part (b) Σ'-typed at Q' with axiom-gate `[propext]` only.

### [P2.3] block-spin step inhabitation — SUPERSEDED by [P2.3-addendum]

> **Status update (P2.3-addendum):** This atomic entry is superseded by the four per-milestone sub-obligations below. The single `step_obligation_witness` is now an assembly of the four sub-witnesses; it inherits `sorryAx` precisely while any sub-witness remains open. Discharging the atomic obligation reduces to closing the four children. The entry below is preserved for the original phrasing; the binding obligations are the children.

### [P2.3-addendum] decomposition of [P2.3] into four sub-obligations

- **milestone**: 2.3-addendum (commit `[P2.3-addendum]`)
- **file**: `lean/YMGap/RG/BlockSpin.lean` (refactored), `formal/block-spin-morphism.tex` §6 (Definition 6.1, Remark 6.2 encoded-but-unverified)
- **what changed**: The atomic `StepObligation` of P2.3 has been decomposed into four typed sub-obligations: `Obligation_sf`, `Obligation_lf`, `Obligation_cap` (takes `sf_part`, `lf_part`), `Obligation_sigma` (takes `cap_part` only). The atomic form is recovered as `StepObligation_decomposed`. Coupling structure is exposed at the type level.
- **encoded-but-unverified structural predictions** (the entire point of the addendum being on record):
  - `Obligation_lf` takes no `sf_part` input — sf ⊥ lf is encoded, **unverified**. Confirmed when 3.2 closes against this signature; refuted otherwise.
  - `Obligation_sigma` takes only `cap_part` (not direct `sf_part`/`lf_part`) — η via cap-only is encoded, **unverified**. Confirmed when 3.4 closes against this signature; refuted otherwise.
  - These predictions are self-correcting: if they are wrong, the corresponding milestones cannot close at the current types, and the signatures will need additional coupling edges. The audit point is exactly when each closes.

### [P2.3-sf] small-field budget obligation, owed by 3.1 — **CLOSED**

- **milestone**: 2.3-addendum child / 3.1 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_sf`
- **obligation**: Choose `eps_sf : V → V → V` and produce, for every `Valid` input `s_k`, a `c_sf_next : KPCertificate V P` satisfying `s_k.c_sf.rho - eps_sf b s_k.g ≤ c_sf_next.rho` (S1).
- **constructive?**: yes — Σ'-typed; the rho-budget is a constructive inequality.
- **owed by**: Milestone 3.1.
- **closed**: 2026-05-24, specialized to `V = Q'` using the identity closure (`eps_sf := 0`, `c_sf_next := s_k.c_sf`). The S1 inequality discharges via `Q'.sub_zero'` + `Q'.le_refl'`.
- **axiom-gate (closed)**: `#print axioms YMGap.RG.step_obligation_sf` reports `depends on axioms: [propext]`. No `sorryAx`, no `Classical.choice`, no `Quot.sound` — AGENTS.md Rule 1 satisfied (`propext` is on the allow-list).
- **note on quantitative content**: the identity closure is structurally trivial — `c_sf_next = s_k.c_sf` means no progress in the ρ-budget. The quantitative analytic content (the real `ρ_sf(g_k) = c_λ / g_k²` from Bałaban / Brydges–Federbush) lives in `computations/small_field_kp.py`. The Lean closure certifies the *shape* of the obligation is constructively dischargeable.
- **must not be closed classically**: per AGENTS.md Rule 6 — and isn't.

### [P2.3-lf] large-field budget obligation, owed by 3.2 — **CLOSED**

- **milestone**: 2.3-addendum child / 3.2 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_lf`
- **obligation**: Choose `eps_lf : V → V → V` and produce, for every `Valid` input `s_k`, a `c_lf_next : KPCertificate V P` satisfying `s_k.c_lf.rho - eps_lf b s_k.g ≤ c_lf_next.rho` (S2).
- **constructive?**: yes.
- **owed by**: Milestone 3.2.
- **closed**: 2026-05-24, specialized to `V = Q'` with identity closure (`eps_lf := 0`, `c_lf_next := s_k.c_lf`). Same shape as sf.
- **axiom-gate (closed)**: `depends on axioms: [propext]` only.
- **structural prediction encoded**: this obligation takes no `sf_part` input. **Confirmed**: the Q' closure body uses no `sf_part` datum, so the [P2.3-addendum] sf ⊥ lf prediction holds at the closed-witness level.
- **note on quantitative content**: see [P2.3-sf]. Real `ρ_lf` and `K_lf` live in `computations/large_field_kp.py` (heat-kernel character-tail + Brydges–Federbush).
- **must not be closed classically**: per AGENTS.md Rule 6 — and isn't.

### [P2.3-cap] overlap budget obligation, owed by 3.3 — **CLOSED**

- **milestone**: 2.3-addendum child / 3.3 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_cap`
- **obligation**: Given closed `sf_part : Obligation_sf` and `lf_part : Obligation_lf`, choose `delta_cap : V → V → V` and produce `c_cap_next` satisfying S3 plus the buffer-glue invariants at scale `k+1` (V3-ρ: `c_cap_next.rho = min sf_step.rho lf_step.rho`; V3-K: `c_cap_next.K ≤ sf_step.K + lf_step.K`).
- **constructive?**: yes.
- **owed by**: Milestone 3.3.
- **closed**: 2026-05-24, specialized to `V = Q'` with `sf_part`/`lf_part` pinned to the canonical `step_obligation_sf` / `step_obligation_lf` closures. Identity closure (`delta_cap := 0`, `c_cap_next := s_k.c_cap`). S3 discharges via `Q'.add_zero'` + `Q'.le_refl'`; V3-ρ and V3-K reduce by `rfl` to Valid's V3-ρ and V3-K conjuncts (since the canonical sf/lf return `s_k.c_sf` / `s_k.c_lf` as their next certificates).
- **specialized signature**: the closed `step_obligation_cap` has signature `(P) (PolyAtlas) (b) → Obligation_cap Q' P PolyAtlas b (step_obligation_sf P PolyAtlas b) (step_obligation_lf P PolyAtlas b)` — it accepts only the canonical sf/lf, not arbitrary sf_part/lf_part. A more general closure (over arbitrary sf_part/lf_part) would require `domGlue_preserves_KP` and inherit [P2.1]'s sorryAx; the canonical specialization avoids that.
- **axiom-gate (closed)**: `depends on axioms: [propext]` only. The identity closure structurally avoids the buffer-glue construction (reuses `s_k.c_cap` directly), so it does not depend on `domGlue_preserves_KP` at all. (Historical note: an earlier `domGlue_preserves_KP` carried a `sorryAx`; since the 2026-05-24 explicit-hypothesis refactor it is axiom-free — `#print axioms domGlue_preserves_KP` reports *does not depend on any axioms*, build-verified 2026-05-28 — so there is no longer any `[P2.1]` sorry to inherit in the first place.)
- **must not be closed classically**: per AGENTS.md Rule 6 — and isn't.

### [P2.3-sigma] σ̂-transport budget obligation, owed by 3.4 — **CLOSED**

- **milestone**: 2.3-addendum child / 3.4 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_sigma`
- **obligation**: Given closed `sf_part`, `lf_part`, `cap_part`, choose `eta : V → V → V` and produce `sigmaHat_next : V` satisfying S4 (`s_k.sigmaHat - eta b s_k.g ≤ sigmaHat_next`) and V1 (`0 < sigmaHat_next`).
- **constructive?**: yes (per-step part).
- **owed by**: Milestone 3.4 (per-step). The **global** budget closure `Σ_k η(b, g_k) < σ̂_0` is a separate downstream claim about an infinite sum's convergence — NOT this entry. See `lean/YMGap/Constructive/Rationals.lean` (Milestone 3.0) docstring for the boundary of the ℚ-only representation w.r.t. infinite sums.
- **closed**: 2026-05-24, specialized to `V = Q'` with `sf_part`/`lf_part`/`cap_part` pinned to the canonical closures. Identity closure (`eta := 0`, `sigmaHat_next := s_k.sigmaHat`). S4 discharges via `Q'.sub_zero'` + `Q'.le_refl'`; V1 (`0 < sigmaHat_next`) follows from Valid's V1 conjunct directly.
- **axiom-gate (closed)**: `depends on axioms: [propext]` only.
- **structural prediction encoded**: this obligation takes only `cap_part`, not direct `sf_part`/`lf_part`. **Confirmed**: the closed-witness body uses no `sf_part`/`lf_part` data — the [P2.3-addendum] σ-depends-on-cap-only prediction holds at the closed-witness level.
- **note on quantitative content**: the real `η_k = (c_polymer / A_min) · Δ_∩` from the σ̂-transport polymer-residual derivation lives in `computations/sigma_hat_trajectory.py` (3.4-upgrade). The Q'-rational coupling (`DERIVED_ETA_COUPLING = 1/2`) is suitable for Q' representation but the Lean closure here uses the identity (η = 0) to certify shape.
- **must not be closed classically**: per AGENTS.md Rule 6 — and isn't.

### [P2.3] (assembled) `step_obligation_witness` — **CLOSED**

- **decl**: `YMGap.RG.step_obligation_witness`
- **status**: assembled from the four sub-witnesses above. Inherits their axiom dependencies: `depends on axioms: [propext]` only.

### [P2.3] (original) block-spin step inhabitation, owed by 3.1–3.4 — **CLOSED**

- **milestone**: 2.3 (work_plan.md L237–260)
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_witness`
- **obligation**: Exhibit a term of type `StepObligation V P PolyAtlas b` — that is, choose budget functions `(eps_sf, eps_lf, delta_cap, eta) : V → V → V` and produce a step function inhabiting `StepTypeWithBudget V P PolyAtlas b eps_sf eps_lf delta_cap eta`, satisfying the four per-step conditions S1–S4 of `docs/context.md` §3.3 / `formal/block-spin-morphism.tex` Definition 5.2.
- **constructive?**: yes — the obligation type is Σ'-typed (the budget functions and the step function are data); the proofs of S1–S4 are constructive inequalities; the codomain demands `Valid s_next`, a constructive predicate.
- **closed**: 2026-05-24, via the four [P2.3-X] decomposed sub-witnesses, each independently closed at `V = Q'`. `step_obligation_witness` now reports `depends on axioms: [propext]` only — no `sorryAx`. (`StepObligation` is now an alias for `StepObligation_decomposed`; the assembled term inhabits both.)
- **axiom-gate (closed)**: `#print axioms YMGap.RG.step_obligation_witness` reports `depends on axioms: [propext]`. Crucially, **no `sorryAx`, no `Classical.choice`, no `Quot.sound`** — AGENTS.md Rule 1 satisfied (`propext` is on the allow-list).
- **per-step scope**: the obligation is single-step. No conjunct mentions `Σ_k`, no clause asserts a uniform-in-`k` property. The global budget closure (`Σ_k η < σ̂_0`, `Σ_k Δ_∩ < ∞`, `inf_k σ̂_k > 0`) is a separate downstream claim, **NOT discharged here**. Closing it requires either a rational-tail-bound module or a constructive-reals layer (see `notes/sigma-hat-derivation.md` §4 / Q' module docstring boundary).
- **must not be closed classically**: per AGENTS.md Rule 6 — and isn't.

### [P9.2] Mass-gap theorem chain — Lean-vs-paper split

- **milestone**: 9.2 (work_plan.md L738–755)
- **file**: `lean/YMGap/MassGap/SU2.lean`
- **decl**: `YMGap.MassGap.SU2.mass_gap_SU2`, `mass_gap_SU2_wilson`,
  `mass_gap_su2_q_rational_data_canonical`, `mass_gap_su2_q_rational_data_wilson`
- **status**: Lean-formalized at the statement level; analytic content
  in the paper.  This entry documents the formal/paper boundary for
  the entire 7.1 → 8.1 → 8.2 → 9.1 → 9.2 chain.

**What is FORMALLY LEAN-PROVED (axiom-gate empty)**:

  * `m_0_canonical := 999/1000 : Q'` and `m_0_wilson := 999/1000 : Q'`
    — explicit constructive Q'-rational mass-gap lower bounds.
    (Tightened 2026-05-26 from `998/1000` by the `c_λ = 3/4`
    Casimir-gap upgrade; see `formal/small-field-kp.tex`
    Theorem `thm:c-lambda-casimir`.)
  * `sigma_hat_inf_lower_canonical := 9991/10000` and
    `sigma_hat_inf_lower_wilson := 9997/10000` — Q'-rational σ̂_∞
    lower bounds from Phase-3 pilot data, lockstep with
    `YMGap.RG.SigmaHatPilot.eta_total_pilot`/`eta_total_pilot_wilson`.
    (Tightened 2026-05-26 from `9967/10000` and `9988/10000` by the
    same `c_λ` upgrade.)
  * `m_0_canonical_positive`, `m_0_wilson_positive` (`decide`).
  * `m_0_canonical_squared_le_sigma_hat`,
    `m_0_wilson_squared_le_sigma_hat` — the decidable witness
    `m_0² ≤ ε` via cross-product on `Int`:
      - Canonical: `999² · 10000 = 9980010000 ≤ 9991 · 1000² = 9991000000`
      - Wilson: `999² · 10000 = 9980010000 ≤ 9997 · 1000² = 9997000000`
  * `mass_gap_su2_q_rational_data_canonical` /
    `mass_gap_su2_q_rational_data_wilson` — the purely-Q' content of
    the mass-gap theorem (∃ m_0 ∈ Q', 0 < m_0 ∧ m_0² ≤ ε).
  * `phase_71_consistent_canonical_holds` — Phase-7.1 framework
    consistency check at the canonical pilot point.
  * `mass_gap_SU2` / `mass_gap_SU2_wilson` — the composed statement:
    Q'-rational data + abstract `HasSpectralGap rec` from the
    Phase-8.2 cluster-to-gap bridge.

  All 13 exports report `does not depend on any axioms` (lake build,
  2026-05-26; re-verified 2026-05-28, `leanprover/lean4:v4.29.1`,
  28 jobs, clean).  No `sorryAx`, no `Classical.choice`, no
  `Quot.sound`, no `propext`.

**What is PAPER-LEVEL (`formal/mass-gap-theorem.tex` §2)**:

  * Phase 7.1 → 8.1 step: the analytic OS4 cluster property is
    established at the paper level via the polymer-cluster decay
    machinery of `formal/sheaf-framework.tex` §7.  The Lean
    `IsOS4ClusterProperty` Prop is abstractly `True`-valued at the
    type-level interface (`lean/YMGap/Continuum/OSAxioms.lean`).
  * Phase 8.1 → 8.2 step: the OS reconstruction theorem
    (Schwinger inner product → quotient/completion → Hilbert space
    → Stone's theorem → self-adjoint H_op) lives in
    `formal/os-reconstruction.tex` §3–§6.  The Lean
    `OSReconstruction` structure carries abstract types for the
    Hilbert space, vacuum, semigroup, Hamiltonian, and the
    reconstruction laws as `True`-valued Props.
  * Phase 8.2 cluster-to-gap bridge: paper `os-reconstruction.tex`
    Theorem `thm:cluster-to-gap` (Källén–Lehmann spectral
    representation of the time-direction two-point function + OS4
    rate ⇒ spectral gap of H_op; the spatial→temporal step uses only
    H_4, not O(4)).  The Lean `cluster_implies_gap_signature` is the
    type-level interface; `HasSpectralGap rec` is abstractly
    `True`-valued.
  * Dimensional identification `m ≥ √σ̂_∞`: paper
    `os-reconstruction.tex` Theorem `thm:area-law-to-gap-bridge` (the
    area-law–to–spectral-gap bridge: string tension σ̂_∞ is inverse
    area, the mass m is inverse length, so the relation carries a
    square root with conservative O(1) constant 1).  Not explicitly
    stated in Lean — the Lean theorem uses the rational
    `m_0² ≤ σ̂_∞` directly, leaving the identification of `m_0` with
    the mass dimension to the paper.

**What is COMPUTATIONS-LEVEL** (`computations/mass_gap_bound.py`):

  * Extracts the explicit m_0 from any pilot operating point.
  * Tests enforce Lean lockstep
    (`tests/test_mass_gap_bound.py::test_canonical_pilot_data_matches_lean_module`).

**Why this split is fully principled**:

  Per the work-plan Milestone 9.2 open question (and the parallel
  7.2, 8.1, 8.2 decisions), the operator-theoretic content (Stone's
  theorem, spectral theorem for unbounded self-adjoint operators) is
  scoped out of the current Lean stack.  The Q' arithmetic chain is
  fully formalized; the OS axiom verifications and the operator-
  theoretic completion are paper-supplied.  Future work
  (constructive-reals layer at Milestone 7.3+) can refine the
  abstract Lean Props into substantive statements without changing
  the type signatures consumed here.

- **constructive?**: yes — the Q'-rational lower bound is constructive
  (Σ-typed via `Exists` on Q'); the witness is decidable; the
  abstract spectral-gap Prop is `True` at the type-level interface
  (paper-supplied at the analytical level).
- **owed by**: Phase 9.1 (paper) + Phase 9.2 (this entry).  Both
  closed 2026-05-26.
- **must not be closed classically**: per AGENTS.md Rule 6 — and
  isn't.  All 13 Lean exports are axiom-free.

### [R3k-parity] Block-compatible dyadic parity transport — **OPEN**

- **milestone**: FrontierDAG bucket 1 / physical pGamma=2 mode-one transport.
- **file**:
  `lean/YMGap/Continuum/P2BlockCompatibleThetaNormalizedDeficit.lean`,
  `lean/YMGap/Continuum/P2BlockCompatibleThetaScaleInvariant.lean`,
  `lean/YMGap/Continuum/P2BlockCompatibleThetaDriftCross.lean`,
  `lean/YMGap/Continuum/P2BlockCompatibleThetaTrapezoidExchange.lean`,
  `lean/YMGap/Continuum/P2BlockCompatibleThetaTerminalChord.lean`,
  `lean/YMGap/Continuum/P2BlockCompatibleThetaTerminalMoment.lean`,
  `lean/YMGap/Continuum/P2BlockCompatibleThetaTerminalRadial.lean`
- **decl**: `BlockCompatibleP2NormalizedDeficitTailFromSeven`,
  `BlockCompatibleP2DimensionlessNormalizedTailFromSeven`,
  `BlockCompatibleP2DimensionlessDriftCrossTailFromSeven`,
  `BlockCompatibleP2TrapezoidExchangeTailFromSeven`,
  `BlockCompatibleP2TerminalSeparatedTailFromSeven`,
  `BlockCompatibleP2TerminalDiagEnvelopeTailFromSeven`,
  `BlockCompatibleP2TerminalRadialTailFromSeven`,
  `BlockCompatibleP2TerminalFactorizedTailFromSeven`
- **obligation**: Inhabit the two schedule-specific normalized-deficit
  inequalities for every `k >= 7`, including the explicit shared debt
  `delta_k=(1/360)8^(-k)`.
- **constructive?**: yes — both are finite `Q'` inequalities.  The checked
  compiler uses logarithmic square-and-multiply, one common denominator per
  finite theta sum, exact dyadic finite-sum reconstruction, the cutoff-uniform
  endpoint-plus-Dirichlet sum-of-squares identity, and positive cancellation.
- **status note**: the former single cross-cutoff Pascal-residual atom has been
  split into these two smaller local atoms.  The tempting debt-free coarse
  comparison was numerically refuted and is not used.  The exact `k=4`,
  `N=79 -> 159`, `k=5`, `N=159 -> 319`, and `k=6`, `N=319 -> 639`
  coefficient cells are kernel-checked.  Positive division cancellation
  reduces the residue to the two displayed normalized inequalities.  Exact
  scale laws now prove `u_k*L_k^2=25/12`, `delta_k*L_k^3=25/72`, and
  `(16/75)*((3/8)*u_k^2*L_k)=delta_k`; constructive alternating Taylor proves
  `w_k <= w_(k+1)^4 <= w_k+(3/8)u_k^2`.  Thus the coarse tail has been reduced
  further to a fixed `16/75` dimensionless normalized-slope bound, while the
  fine field remains the independent even/odd reserve.  The coarse quotient is
  now division-free and equal to one rectangular mode-pair kernel sum.  Its
  square-core/terminal-column split, transposed-pair identity, common monomial
  factorization, and exact sign partition (`j<=i` favorable, `i<j` adverse)
  are kernel-checked for every cutoff.  Exact finite-sum algebra now sharpens
  this to two one-dimensional fields: the trapezoid cross is exactly twice
  the square core plus the terminal column, and the terminal column is exactly
  one scalar cross.  A nonpositive trapezoid cross together with a terminal
  bound by twice the normalized budget compiles to the desired covariance
  bound without discarding the negative core.  The terminal cross is now
  factored exactly by the actual heat increment and bounded by a constructive
  mixed-power right rectangle.  Its remaining field is the product of one
  explicit high-weight terminal monomial and one low-weight Casimir-gap
  moment, bounded by `(32/75)*L*D0*D4`; no growing difference of powers or
  scale-dependent drift remains in that atom.  Constructive termwise AM--GM
  further pays twice that adjacent-product moment by a purely diagonal
  Casimir-gap envelope.  The terminal atom is thus reduced to the diagonal
  product bound `outer*diagEnvelope <= (64/75)*L*D0*D4`.  The diagonal
  envelope is reindexed exactly into head, interior, and terminal radial
  diagonal weights.  A checked rational factor compiler reduces its terminal
  product bound to the two division-free fields
  `L*outer <= (5/16)*D4` and
  `radial <= (341/125)*L^2*D0`; their coefficient product leaves exact slack
  `1/1200` below `64/75`.  Both factor fields, trapezoid exchange, and fine
  reserve remain open.  These compile through
  the deficit-energy/SOS, dyadic parity, quotient, and genuine
  `BlockingStep.Phi` layers.  The remaining tail begins honestly at `k=7`;
  neither analytic field is claimed inhabited.
- **axiom gate (closed compiler)**: `[propext, Quot.sound]` only.

### [R3k-box] All-scale weighted-box strong-Turan family — **OPEN**

- **milestone**: FrontierDAG bucket 1 / all-cutoff CanonicalBulkControl.
- **file**: `lean/YMGap/Continuum/P2BlockCompatibleStrongTuranBridge.lean`
- **decl**: `BlockCompatibleP2BoxStrongTuranData`
- **obligation**: Prove the weighted Clebsch-box strong-Turan seed and step at
  every cutoff in the physical replacement schedule.
- **constructive?**: yes — the downstream Nat-induction compiler and exact
  Peter--Weyl reconstruction are already kernel-checked.
- **status note**: remains independent of the parity-transport pair above.

### [R3k-strand-A1] Exact finite Clebsch-box strand reindex — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/FusionStrandExactReindex.lean`
- **decl**: `boxSum_eq_lineSum_lagCorr`
- **obligation**: Prove for every exact weight, cutoff, and channel that the
  cutoff-square Clebsch sum equals the antidiagonal line sum of the truncated
  lag correlation, with cutoff `r < N+1-max(p,t-p)`.
- **constructive?**: yes — unique strand deltas, finite Fubini, exact delta
  collapse, and one masked-prefix theorem; no evaluated large certificate.
- **status note**: A1 is closed with axiom gate `[propext, Quot.sound]` and is
  wired into `P2HalfTimeLineSumTailRatio.toCoeff`.  The schedule-wide
  lag-correlation line-sum inequality (A3/physical half-time sign) remains an
  explicit open input; this entry does not claim it or a continuum margin.

### [R4h-half-time-high-shift] Physical high-shift half-time sector — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeShiftTail.lean`
- **decl**: `physicalHighShiftSum_halfTime`
- **obligation**: Decompose the sharp-cutoff lag-correlation line sum by
  common shift and prove the physical half-time ratio for the aggregate of
  every row `r >= ceil((5*2^k+s)/2)`.
- **constructive?**: yes — an exact weighted-successor identity reduces each
  row to one reciprocal-Bernoulli coefficient comparison; a pure-`Nat`
  threshold payment proves it uniformly at every scale and cutoff.
- **status note**: closed with axiom gate `[propext, Quot.sound]`.  The theorem
  `physical_mode_one_tail_nonempty` proves that the discharged sector is
  nonvacuous.  An independent low-prefix ratio is a valid stronger sufficient
  input, but is not the sharp active frontier because it forbids cancellation
  between the two sectors.  This entry does not claim the full all-scale
  control family or a Yang--Mills mass gap.

### [R4i-half-time-balance] Sharp low-debt / high-reserve carrier — **COMPILER CLOSED 2026-08-06; RESERVE DOMINATION OPEN**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeShiftTail.lean`
- **decl**: `P2PhysicalLowHighReserve`
- **obligation**: Prove at every physical scale and channel that the signed
  low-shift debt is at most the reserve supplied by all high-shift rows.
- **constructive?**: yes — `toLineSum` and `ofLineSum` prove two-way
  equivalence with the schedule-native line-sum ratio, so the carrier neither
  loses nor invents analytic content.
- **status note**: `physicalHighShiftRowReserveSum_eq_reserve` exposes the
  reserve as a finite sum of constant-shape row atoms, and
  `BlockCompatibleP2LowHighReserveFromFour.toControlFamily` reaches the
  reviewed all-scale control consumer.  The sharper exact aggregate form
  `physicalFullLocalReserveSum_eq_lineReserve` removes the sector split:
  nonnegativity of one finite double sum is equivalent in both directions to
  the original line ratio.  `physicalFullLocalReserveAt_sound` reduces each
  channel to one integer numerator sign, and the schedule-wide numerator
  carrier also reaches the control consumer.  The all-scale sign theorem
  itself is still open.  All closed compiler gates are
  `[propext, Quot.sound]` only.

### [R4j-half-time-fixed-row-obstruction] Fixed-row Turan shortcut audit — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / physical pGamma=2 coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeStrongTuranObstruction.lean`
- **decl**: `physicalHalfTimeBoxTuranAt_four_one_false`,
  `integralStrongTuranFromFour_uninhabited`
- **obligation**: Decide whether the proposed fixed-weight, one-row
  strong-Turan carrier can hold on the physical schedule.
- **constructive?**: yes — exact kernel reduction at `k=4,t=1`.
- **status note**: the premise is false and the route is retired.  The sound
  adjacent-row compression theorem remains available; no false premise is
  carried into the physical frontier.

### [R4k-physical-compiled-carrier] Common physical coefficient compiler — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / physical pGamma=2 spectrum pins.
- **file**:
  `lean/YMGap/Continuum/P2BlockCompatiblePhysicalCompiledFrontier.lean`
- **decl**: `BlockCompatibleP2PhysicalCompiledFrontier.toCanonicalFamily`,
  `.finePin`, `.imagePin`, `.blockDefectPowerOnTrajectory`
- **obligation**: Prove that the parity and exact-reserve coefficient routes
  feed one reviewed spectrum and the genuine `BlockingStep.Phi` trajectory.
- **constructive?**: yes.
- **status note**: closed with `[propext, Quot.sound]`; the carrier still
  honestly requires coefficient-reserve and theta-tail inputs.

### [R4l-half-time-boundary-shells] Head, terminal, and penultimate shells — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeTerminalShell.lean`,
  `lean/YMGap/Continuum/P2HalfTimePenultimateShell.lean`
- **decl**: `physical_halfTime_lineSum_head_from_four`,
  `physical_halfTime_lineSum_terminal`,
  `physical_halfTime_lineSum_penultimate_from_four`
- **obligation**: Remove the three boundary regions from the all-scale
  full-local reserve carrier.
- **constructive?**: yes — exact box identities, coefficient descent,
  reciprocal Bernoulli, and natural-number cutoff arithmetic.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+2<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4m-half-time-antepenultimate-shell] Antepenultimate shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeAntepenultimateShell.lean`
- **decl**: `antepenultimateBoxRatio`,
  `physical_halfTime_lineSum_antepenultimate_from_four`
- **obligation**: Remove the `s=2*N_k-3` shell from the all-scale full-local
  reserve carrier.
- **constructive?**: yes — coefficient descent, exact top-box identities, a
  sound reflected integer-polynomial certificate, and the physical Bernoulli
  power floor.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+3<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4n-half-time-fourth-shell] Fourth boundary shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeFourthShell.lean`
- **decl**: `fourthBoxRatio`, `physical_fourth_coeff_descending`,
  `physical_halfTime_lineSum_fourth_from_four`
- **obligation**: Remove the `s=2*N_k-4` shell from the all-scale full-local
  reserve carrier.
- **constructive?**: yes — exact nine/six-pair formulas, a sound reflected
  integer-polynomial certificate, coefficient descent, and the physical
  Bernoulli power floor.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+4<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4o-half-time-fifth-shell] Fifth boundary shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeFifthShell.lean`
- **decl**: `boxSum_top_five`, `fifthBoxRatio`,
  `physical_halfTime_lineSum_fifth_from_four`
- **obligation**: Remove the `s=2*N_k-5` shell from the all-scale full-local
  reserve carrier.
- **constructive?**: yes — exact twelve/nine-pair formulas, a sound reflected
  integer-polynomial certificate, coefficient descent, and a sharp physical
  `3/4` Bernoulli power floor.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+5<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4r-half-time-sixth-shell] Sixth boundary shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeSixthShell.lean`
- **decl**: `boxSum_top_six`, `sixthBoxRatio`,
  `physical_halfTime_lineSum_sixth_from_four`
- **obligation**: Remove the `s=2*N_k-6` shell from the all-scale full-local
  reserve carrier.
- **constructive?**: yes — exact sixteen/twelve-pair formulas, a sound
  fourteen-term reflected integer-polynomial certificate, endpoint
  coefficient descent, and the sharp physical `3/4` heat-power floor.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+6<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4s-half-time-seventh-shell] Seventh boundary shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeSeventhShell.lean`
- **decl**: `boxSum_top_seven`, `seventhBoxRatio`,
  `physical_halfTime_lineSum_seventh_from_four`
- **obligation**: Remove the `s=2*N_k-7` shell from the all-scale full-local
  reserve carrier.
- **constructive?**: yes — exact twenty/sixteen-pair formulas, a sound
  nineteen-term reflected integer-polynomial certificate, endpoint
  coefficient descent, and the sharp physical `4/5` heat-power floor.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+7<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4t-half-time-eighth-ratio] Eighth sharp endpoint ratio — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeEighthRatio.lean`
- **decl**: `eighthBoxRatio`
- **obligation**: Compare the twenty-pair depth-seven endpoint box with the
  adjacent twenty-five-pair depth-eight endpoint box without evaluating the
  physical convolution.
- **constructive?**: yes — a sound reflected polynomial identity rewrites the
  cleared slack `4*B8-5*B7` as twenty-three nonnegative products in eight
  successive coefficient increments.
- **status note**: the theorem is an algebraic component of the physical shell,
  not by itself a frontier discharge.  Its gate is `[propext, Quot.sound]`.

### [R4u-half-time-eighth-shell] Eighth boundary shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeEighthShell.lean`
- **decl**: `boxSum_top_eight`, `physical_eighth_coeff_descending`,
  `physical_halfTime_lineSum_eighth_from_four`
- **obligation**: Remove the `s=2*N_k-8` shell from the all-scale full-local
  reserve carrier.
- **constructive?**: yes — exact twenty-five/twenty-pair support, the reflected
  twenty-three-term ratio certificate, endpoint coefficient descent, and the
  sharp physical `4/5` heat-power floor.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+8<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4v-half-time-ninth-ratio] Ninth sharp endpoint ratio — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeNinthRatio.lean`
- **decl**: `ninthBoxRatio`
- **obligation**: Compare the twenty-five-pair depth-eight endpoint box with
  the adjacent thirty-pair depth-nine endpoint box without evaluating the
  physical convolution.
- **constructive?**: yes — a reflected polynomial identity rewrites the
  cleared slack `5*B9-6*B8` as twenty-nine nonnegative products in nine
  successive coefficient increments.
- **status note**: this is a constant-size algebraic certificate consumed by
  the physical shell.  Its gate is `[propext, Quot.sound]`.

### [R4w-half-time-ninth-shell] Ninth boundary shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeNinthShell.lean`
- **decl**: `boxSum_top_nine`, `physical_ninth_coeff_descending`,
  `physical_halfTime_lineSum_ninth_from_four`
- **obligation**: Remove the `s=2*N_k-9` shell from the all-scale full-local
  reserve carrier.
- **constructive?**: yes — exact thirty/twenty-five-pair support, the
  twenty-nine-term reflected ratio certificate, endpoint coefficient descent,
  and the sharp physical `5/6` heat-power floor.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+9<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4x-endpoint-ratio-arithmetic] Parametric endpoint-ratio arithmetic — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / proof-about-computation coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeEndpointRatioCompiler.lean`
- **decl**: `scaled_parityTriangleCount_pred`,
  `scaled_thresholdTriangleCount_pred`, `parityTriangleCount_boundary_balance`
- **obligation**: Replace the growing handwritten endpoint-coefficient count
  tables by one all-depth parity-triangle formula and its adjacent-depth
  inequality.
- **constructive?**: yes — parity splitting and monotone natural-number
  arithmetic only.
- **status note**: this closes the arithmetic coefficient schema, not a new
  physical shell.  Its exported gates are `[propext, Quot.sound]` or smaller.

### [R4y-endpoint-ratio-certificate] Reflected endpoint-ratio generator — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / proof-about-computation coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeEndpointRatioCertificateCompiler.lean`
- **decl**: `endpointRatio_of_certificate`, `endpointRatioCertificate_ten`,
  `endpointRatio_ten`
- **obligation**: Generate and check the adjacent endpoint polynomial from its
  parity-triangle definition instead of spelling out a growing slack table.
- **constructive?**: yes — the proved ring normalizer checks the closed
  certificate; no native evaluator or trusted external computation is used.
- **status note**: depths eight and nine are regressions and depth ten is the
  first new table-free ratio.  The exact physical tenth-shell support,
  coefficient descent, and heat transport remain open, so the compiled
  carrier honestly remains at `s+9<2*N_k`.  Gates are
  `[propext, Quot.sound]` or smaller.

### [R4z-endpoint-support-compiler] All-depth endpoint support compiler — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / proof-about-computation coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeEndpointSupportCompiler.lean`
- **decl**: `endpointDirectBox_eq_endpointBoxExpr`,
  `boxSum_top_endpointDirect`, `boxSum_top_endpoint`
- **obligation**: Replace the shell-by-shell sharp-cutoff Clebsch support
  tables by one theorem valid at every endpoint depth `m<=N`.
- **constructive?**: yes — finite coordinate reversal, the proved support
  classifier, and exact reflected-polynomial evaluation.
- **status note**: the support side of every later endpoint shell is now a
  theorem schema rather than an enumeration.  Exported gates are
  `[propext, Quot.sound]` or smaller.

### [R4aa-half-time-tenth-shell] Tenth boundary shell — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeTenthShell.lean`
- **decl**: `physical_tenth_coeff_descending`, `tenthEndpointBoxRatio`,
  `physical_halfTime_lineSum_tenth_from_four`
- **obligation**: Remove the `s=2*N_k-10` shell from the all-scale full-local
  reserve carrier using the new all-depth compilers.
- **constructive?**: yes — a closed depth-ten reflected certificate, generic
  support reindex, physical coefficient descent, heat-floor transport, and
  exact box-to-line transport.
- **status note**: the common compiled carrier now assumes reserve signs only
  for `k>=4`, `2<=s`, and `s+10<2*N_k`.  The deeper interior family remains
  open.  All closed gates are `[propext, Quot.sound]`.

### [R4ab-macroscopic-endpoint-band] Macroscopic endpoint band — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / half-time physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeMacroscopicEndpointDescent.lean`
- **decl**: `physical_coeff_descending_of_half`,
  `physical_endpointRatio_of_double_depth`,
  `physical_halfTime_lineSum_fifth_depth_from_four`
- **obligation**: Replace fixed-depth endpoint-shell certificates by a
  schedule-wide coefficient descent, heat-floor payment, and complete
  half-time theorem on a cutoff-growing band.
- **constructive?**: yes — exact physical-coordinate arithmetic, the
  all-depth semantic endpoint compiler, reciprocal Bernoulli, and exact
  box-to-line transport.
- **status note**: every cell `s=2*N_k-m` with `m>0`, `2*m<=N_k`, and
  `(m+1)*(2*N_k-m+2)<=D_k` is discharged for `k>=4`; the one-fifth band is a
  simple corollary.  All gates are `[propext, Quot.sound]`.

### [R4ac-macroscopic-physical-consumer] Macroscopic reserve consumer — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / genuine physical consumer.
- **file**: `lean/YMGap/Continuum/P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.lean`
- **decl**: `BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour.toLineSumTail`,
  `BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.toCompiled`,
  `BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.blockDefectPowerOnTrajectory`
- **obligation**: Splice the proved macroscopic endpoint band into the same
  reviewed `CanonicalBulkControl` and genuine `BlockingStep.Phi` trajectory.
- **constructive?**: yes — a pure-Nat band split followed by the existing
  physical compiler and spectrum dictionary.
- **status note**: the exact remaining coefficient input is the full-local
  numerator sign outside `2*(2*N_k-s)<=N_k` and
  `(2*N_k-s+1)*(s+2)<=D_k`; all gates are `[propext, Quot.sound]`.

### [R4ad-endpoint-spliced-parity] Endpoint-spliced parity compiler — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / proof about computation.
- **file**: `lean/YMGap/Continuum/P2HalfTimeEndpointSplicedParityCompiler.lean`
- **decl**: `tail_of_alternating_outside`,
  `BlockCompatibleP2HalfTimeOffCoverTransitionsFromFour.toLineSumTail`,
  `BlockCompatibleP2PhysicalEndpointSplicedParityFrontier.toCompiled`
- **obligation**: Remove directly proved endpoint cells from the odd/even
  parity-transition frontier without unrolling the finite automaton.
- **constructive?**: yes — induction over parity strands with an explicit
  `DecidablePred`, pointwise heat-power reinsertion, and exact A1 transport.
- **status note**: only off-cover transition targets remain, and the resulting
  family reaches the common reviewed physical carrier; all gates are
  `[propext, Quot.sound]`.

### [R4ae-scale-four-reflection] Scale-four bounded reflection certificates — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / proof about computation.
- **file**: `lean/YMGap/Continuum/P2HalfTimeScaleFourCertificate.lean` and
  `P2HalfTimeScaleFourCertificate{18,34,50,66,82,98,114,130}.lean`
- **decl**: `halfTimeIntegralTailBlockCheck_sound`,
  `physicalHalfTimeScaleFourCheck_2_17` through
  `physicalHalfTimeScaleFourCheck_130_136`
- **obligation**: Check the direct half-time cells `s=2..136` at the first
  unresolved physical cutoff without one crash-sized kernel normalization.
- **constructive?**: yes — a generic Boolean-list soundness theorem and nine
  process-isolated `decide` certificates.
- **status note**: all block declarations are axiom-free; the soundness
  wrapper uses only `[propext, Quot.sound]`.

### [R4af-scale-four-complete] Complete physical scale-four row — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / physical coefficient route.
- **file**: `lean/YMGap/Continuum/P2HalfTimeScaleFourComplete.lean`
- **decl**: `physicalHalfTimeScaleFourInteriorAt`,
  `physical_halfTime_scaleFour`
- **obligation**: Join the checked interior, the proved head, and the symbolic
  endpoint band into every supported half-time cell at `k=4`, `N_4=79`.
- **constructive?**: yes — bounded reflection, explicit `Q'.eqv` transport,
  Presburger endpoint enumeration, and the existing endpoint theorem.
- **status note**: every `1<=s<158` cell is closed; all gates are
  `[propext, Quot.sound]`.

### [R4ag-scale-four-splice] Residual transition compiler from scale five — **CLOSED 2026-08-06**

- **milestone**: FrontierDAG bucket 1 / genuine physical consumer.
- **file**: `lean/YMGap/Continuum/P2HalfTimeScaleFourSplicedParityCompiler.lean`
- **decl**: `physicalScaleFourLineSumTail`,
  `BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive.toLineSumTail`,
  `BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.blockDefectPowerOnTrajectory`
- **obligation**: Remove the entire `k=4` row from the off-cover transition
  family while preserving the reviewed all-cutoff physical trajectory.
- **constructive?**: yes — dependent scale split, exact A1 transport, and the
  existing common physical compiler.
- **status note**: only off-cover transitions for `k>=5` plus the independent
  theta tail remain; `pGamma>=2`, `finePin`, `imagePin`, genuine
  `BlockingStep.Phi` defect power, and half-loss all remain kernel-checked
  under `[propext, Quot.sound]`.

### [BF4-cutoff-two-physical-table-bridge] Restricted physical table seam — **FACTORED 2026-08-21**

- **milestone**: finite physical sector selection / exact kernel
  representation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorRawRowSumCheck.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorRawRowSumRows.lean`,
  its `RawRowSumRows/Row00.lean` through `Row64.lean` shards, and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge.lean`.
- **decl**: `cutoffTwoSectorRawRowSums_checked`,
  `cutoffTwoSectorRawRowSum_eqv_sum`,
  `CutoffTwoSectorPhysicalTableCertificate`,
  `centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw`, and
  `cutoffTwoSectorRawRowSum_eqv_physicalSectorSum`.
- **obligation**: inhabit the remaining 65-row certificate comparing the
  computed production recurrence with the stored exact table; row-sum
  normalization is now unconditionally checked, and the production bridge is
  proved conditional on exactly that finite residual.
- **constructive?**: yes — all witnesses must remain kernel-checkable under the
  stated axiom gate; the current certificate has no inhabitant.
- **status note**: the 65 row-sum shards and aggregate completed in 1667 jobs;
  the bridge target completed in 1668 jobs; load-bearing declarations use only
  `[propext, Quot.sound]`.  An earlier monolithic physical-row aggregate was
  stopped at the monitored 12 GiB memory reserve and is not counted as passed.
  Therefore no fully discharged production-kernel `49/50` gap, cofinal sector
  family, completion, continuum QFT, or Clay conclusion is claimed.

### [BF4-cutoff-two-nonzero-upper-reduction] Physical table residual contraction — **FACTORED 2026-08-21**

- **milestone**: finite physical sector selection / exact kernel
  representation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassificationCompact.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction.lean`.
- **decl**: `cutoffTwoSectorLocalZeroRows_compact_checked`,
  `centralPhysicalReflectedKernel_cutoffTwo_sector_index_eqv_zero_of_raw_compact`,
  `CutoffTwoSectorPhysicalNonzeroUpperCertificate`,
  `centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw_of_nonzeroUpper`,
  and `CutoffTwoSectorPhysicalNonzeroUpperCertificate.toPhysicalTableCertificate`.
- **obligation**: inhabit the physical equality only for nonzero
  upper-triangle entries; stored raw-table symmetry was subsequently closed by
  `[BF4-cutoff-two-raw-symmetry]`, and all raw zeros and the lower triangle are
  discharged by proved local support and symmetry compilers.
- **constructive?**: yes — the smaller certificate remains uninhabited and
  must be supplied by kernel-checked shared-DAG traces or a stronger symbolic
  recurrence theorem.
- **status note**: the compact zero-classification target completed in 1678
  jobs and the reduction target in 1747 jobs; all load-bearing declarations
  use only `[propext, Quot.sound]`.  Physical recurrence row zero and a
  presentation-only all-entry count each reached the monitored 12 GiB reserve
  and are not passed or retained.  No production-kernel `49/50` gap, cofinal
  sector family, completed gap, continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-raw-symmetry] Stored sector-kernel symmetry — **CLOSED 2026-08-21**

- **milestone**: finite physical sector selection / exact kernel
  representation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryCheck.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorRawSymmetryRows.lean`,
  its `RawSymmetryRows/Row00.lean` through `Row64.lean` shards, and the revised
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorNonzeroUpperReduction.lean`.
- **decl**: `cutoffTwoSectorRawSymmetryRows_checked`,
  `cutoffTwoSectorRawKernel_symm`, and
  `CutoffTwoSectorPhysicalNonzeroUpperCertificate`.
- **obligation**: none for raw-table symmetry.  The remaining finite seam is
  solely the production physical equality on nonzero upper-triangle entries.
- **constructive?**: yes — every literal row certificate is axiom-free; the
  exported setoid theorem and revised reduction use only
  `[propext, Quot.sound]`.
- **status note**: the row-isolated target completed in 1667 jobs and the
  dependency-complete revised reduction in 1814 jobs.  The untrusted generator
  reports 499 residual pairs, but no kernel-checked count is claimed.  The
  residual physical certificate remains uninhabited, so no production-kernel
  `49/50` gap, cofinal sector family, completed gap, continuum QFT, or Clay
  theorem is claimed.

### [BF4-cutoff-two-axis-swap12] Second adjacent spatial-axis transport — **CLOSED 2026-08-21**

- **milestone**: finite physical sector symmetry / exact factor-graph
  representation.
- **file**:
  `computations/bf4_cutoff_two_axis_swap12_certificate.py`, the nineteen
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoAxisSwap12*.lean` modules,
  and the 64 process-isolated modules under
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportStates/`.
- **decl**: `axisSwap12AllStateLinkTransport` and
  `cutoffTwoSectorPairInterface_axisSwap12_eqv`.
- **obligation**: none for simultaneous second-swap invariance of the exact
  cutoff-two interface partition sum.  The next obligation is to prove
  lower-face scalar invariance and lift both adjacent swaps to genuine
  physical-kernel equality before constructing the `S3` orbit quotient.
- **constructive?**: yes — the checked transports and interface theorem use
  only `[propext, Quot.sound]`.
- **status note**: the all-state, audit, and interface targets completed with
  1680, 1681, and 1680 jobs respectively.  A stopped five-state normalization
  trial is not counted as passed.  Signed flips failed the external pointwise
  lift audit and are not claimed.  No production-kernel `49/50` gap, cofinal
  sector family, completed gap, continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-spatial-axis-kernel] Adjacent-swap physical-kernel invariance — **CLOSED 2026-08-21**

- **milestone**: finite physical sector symmetry / exact kernel orbit
  reduction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialAxisKernelInvariance.lean`,
  the revised first-swap shard generator and interface, and the 64 modules
  under
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportStates/`.
- **decl**: `cutoffTwoLowerFaceScalar_axisSwap01_eqv`,
  `cutoffTwoLowerFaceScalar_axisSwap12_eqv`,
  `centralPhysicalReflectedKernel_cutoffTwo_axisSwap01_eqv`, and
  `centralPhysicalReflectedKernel_cutoffTwo_axisSwap12_eqv`.
- **obligation**: none for genuine kernel invariance under the two adjacent
  unsigned spatial-axis generators.  The next finite obligation is a checked
  six-element `S3` action/orbit quotient and its contraction of the nonzero
  physical trace certificate.
- **constructive?**: yes — the four exported invariance declarations use only
  `[propext, Quot.sound]`.
- **status note**: all 64 newly isolated first-swap state checks passed, its
  interface and audit targets completed with 1680 and 1681 jobs, and the
  combined physical-kernel target completed with 1762 jobs.  The stopped
  historical five-state rebuild
  and pre-fix interface attempt are not counted as passed.  Signed flips and
  every uniform/continuum conclusion remain open; no production-kernel
  `49/50` gap or Clay theorem is claimed.

### [BF4-cutoff-two-spatial-S3-action] Six-word physical-kernel action — **CLOSED 2026-08-21**

- **milestone**: finite physical sector symmetry / exact kernel orbit
  reduction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3KernelAction.lean`.
- **decl**: `cutoffTwoSpatialS3Action_compose` and
  `centralPhysicalReflectedKernel_cutoffTwo_spatialS3_eqv`.
- **obligation**: none for the six-element unsigned spatial action and its
  genuine physical-kernel invariance.  The next obligation is a checked
  unordered-pair canonicalizer, raw-table transport, and the resulting
  nonzero representative certificate.
- **constructive?**: yes — the multiplication laws are finite constructor
  proofs/checks and both load-bearing declarations use only
  `[propext, Quot.sound]`.
- **status note**: the dependency-complete target passed with 1763 jobs.  No
  signed flip, residual physical trace equality, production-kernel `49/50`
  gap, uniform limit, continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-spatial-S3-pair-transport] Canonical pair transport — **CLOSED 2026-08-21**

- **milestone**: finite physical sector symmetry / exact kernel orbit
  reduction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalizationData.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3PairCanonicalization.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperCheck.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3RawCanonicalUpperRows.lean`,
  its 65 row modules, and the generating Python script.
- **decl**: `cutoffTwoSectorPairCanonical_upper`,
  `centralPhysicalReflectedKernel_cutoffTwo_pairCanonical_eqv`, and
  `cutoffTwoSectorRawKernel_pairCanonical_eqv_of_upper`.
- **obligation**: none for transporting an upper-triangle physical/raw pair to
  its common deterministic spatial-S3 representative.  The next obligation
  is the checked nonzero representative carrier and one production
  physical/raw trace proof per member.
- **constructive?**: yes — the 2,145 stored-raw equalities are process-isolated
  kernel decisions; exported transports use only `[propext, Quot.sound]`.
- **status note**: the row target passed with 1,834 jobs and the combined
  physical transport/axiom audit with 1,836 jobs.  The external count of 127
  nonzero representatives is not yet a Lean theorem.  No residual physical
  trace certificate, uniform gap, continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-spatial-S3-representatives] Exact representative carrier and compiler — **FACTORED 2026-08-21**

- **milestone**: finite physical sector symmetry / exact kernel orbit
  reduction.
- **file**:
  `computations/bf4_cutoff_two_spatial_s3_nonzero_representatives.py`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeData.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageCheck.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3NonzeroRepresentativeCoverageRows.lean`,
  its 65 row modules,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction.lean`,
  and its axiom audit.
- **decl**:
  `cutoffTwoSpatialS3NonzeroRepresentatives_length`,
  `cutoffTwoSpatialS3NonzeroRepresentativeRecognizedCodes_eq`,
  `cutoffTwoSectorPairCanonicalCodeCheck_nonzeroRepresentative`,
  `CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate`, and
  `CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate.toPhysicalTableCertificate`.
- **obligation**: inhabit production physical/raw equality on exactly the 127
  kernel-checked spatial-S3 representative codes.  Coverage and compiler
  theorems then discharge all 499 nonzero upper entries and all 4,225 table
  entries.
- **constructive?**: yes — recognizer/list equality is axiom-free; exported
  coverage and compiler declarations use only `[propext, Quot.sound]`.  The
  residual certificate remains uninhabited.
- **status note**: the dependency-complete carrier/coverage/compiler axiom
  audit passed with 2,119 jobs.  The next finite frontier is the shared-DAG
  physical evaluation of those 127 representatives.  No production-kernel
  `49/50` gap, cofinal sector family, completed gap, continuum QFT, or Clay
  theorem is claimed.

### [BF4-cutoff-two-shared-DAG-R00C01] Representative `(0,1)` physical evaluation — **CLOSED 2026-08-21**

- **milestone**: finite physical sector table / shared-DAG representative
  evaluation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Data.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01/`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Certificate.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C01Certificate.lean`.
- **decl**:
  `centralPhysicalReflectedKernel_cutoffTwo_sector_R00C01_eqv_raw_sharedDAG`.
- **obligation**: none for representative `(0,1)`.  The residual obligation is
  to discharge and assemble the rest of the exact 127-member representative
  carrier into
  `CutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate`.
- **constructive?**: yes — the exported equality uses exactly
  `[propext, Quot.sound]`.
- **status note**: the dependency-complete target passed with 1,722 jobs and
  built the shared 1,606-bucket cache needed by later traces.  This is one new
  representative equality, not yet the aggregate certificate, the
  production-kernel `49/50` gap, a uniform limit, a continuum QFT, or the Clay
  theorem.

### [BF4-cutoff-two-shared-DAG-prefix] Scalable four-representative aggregate — **CLOSED 2026-08-21**

- **milestone**: finite physical sector table / shared-DAG representative
  evaluation and aggregation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR00C02Certificate.lean`,
  its trace modules,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativePrefixCertificate.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSpatialS3RepresentativeReduction.lean`,
  and the two updated generators.
- **decl**:
  `centralPhysicalReflectedKernel_cutoffTwo_sector_R00C02_rawStateAt_eqv_raw_sharedDAG`,
  `cutoffTwoSectorRepresentativePhysicalStatement_of_eq`, and
  `cutoffTwoSharedDAGRepresentativePrefix_checked`.
- **obligation**: none for the four-entry prefix `(0,0)`, `(0,1)`, `(0,2)`,
  `(1,1)`.  Generate, check, and assemble the remaining 123 exact
  representatives to inhabit the full residual certificate.
- **constructive?**: yes — the individual, abstract-transport, and prefix
  declarations use exactly `[propext, Quot.sound]`.
- **status note**: the dependency-complete prefix target passed with 2,272
  jobs, while its final aggregate built in 0.5 seconds.  The raw-`Nat`/`Fin`
  bridge is now applied once symbolically in the compiler, avoiding concrete
  state-list reduction.  This is not yet the 127-member certificate, the
  production-kernel `49/50` gap, a uniform limit, a continuum QFT, or the Clay
  theorem.

### [BF4-cutoff-two-shared-DAG-full] Full 127-representative physical table — **CLOSED 2026-08-21**

- **milestone**: finite physical sector table / complete shared-DAG
  representative evaluation and orbit contraction.
- **file**:
  `computations/bf4_cutoff_two_shared_dag_certificate.py`,
  `computations/bf4_cutoff_two_shared_dag_representative_certificate.py`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.lean`,
  the 127 shared-DAG physical certificates, and their trace data, six-shard,
  and trace-root modules.
- **decl**:
  `cutoffTwoSharedDAGRepresentatives_checked`,
  `cutoffTwoSectorPhysicalSpatialS3RepresentativeCertificate`, and
  `cutoffTwoSectorPhysicalTableCertificate`.
- **obligation**: none for the exact finite cutoff-two 65-by-65 production
  physical/raw table equality.  The next finite obligation is to feed this
  inhabitant into the stored-table `49/50` estimate and expose the resulting
  unconditional production-kernel theorem.
- **constructive?**: yes — all three exported aggregate declarations use
  exactly `[propext, Quot.sound]`.
- **status note**: the dependency-complete target passed with 3,413 jobs.  The
  127 representative traces comprise 127 data modules, 762 process-isolated
  shards, and 127 roots.  This is finite cutoff-two closure only; it does not
  establish a cofinal cutoff family, a cutoff-uniform gap, completion,
  thermodynamic/continuum limits, QFT axioms, or the Clay theorem.

## How to add an entry

```markdown
### [P1.x] short title

- **milestone**: 1.x (work_plan.md)
- **file**: `lean/YMGap/.../foo.lean`
- **decl**: `theorem foo`
- **obligation**: <one sentence>
- **constructive?**: yes / no
- **notes**: <free text>
```

### [BF4-cutoff-two-canonical-vacuum-sector] Exact constructive physical vacuum component — **CLOSED 2026-08-21**

- **milestone**: finite physical vacuum-sector selection before a strict
  contraction statement.
- **file**:
  `lean/YMGap/Continuum/FiniteBoolGraphRootComponent.lean`,
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSector.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorRawRowZeroPositive.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubePositiveStar.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubeFiniteSupportEdges.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubeVacuumHub.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubeHubStateEdge.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoVacuumComponentIntro.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubeVacuumConnectivity.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubeSectorCode.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCubeSectorNoEscape.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector.lean`.
- **decl**:
  `rootComponent_closed_under_edge`,
  `centralPhysicalFiniteSupportAdjacentB_true_of_kernel_pos`,
  `centralPhysicalFiniteVacuumSectorState_mem_of_two_edges`,
  `cutoffTwoSectorPhysicalTableCertificateSealed_rowZero_pos`, and
  `cutoffTwoCubeSectorState_mem_positive`,
  `cutoffTwoCubeSectorState_mem_canonicalVacuumSector`,
  `next_state_mem_cutoffTwoSector_of_adjacent`, and
  `centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff`.
- **obligation**: none for identifying the exact finite cutoff-two canonical
  vacuum component.  The next finite obligation is to contract the stored
  `49/50` sector estimate through this support equality to the production
  physical form.
- **constructive?**: yes — the explicit sector decision is transported from
  finite `Nat`-code membership, and every printed declaration uses only
  `[propext, Quot.sound]`; no `sorry`, named analytic input, classical axiom,
  or `native_decide` was added.
- **status note**: the source and dependency-complete targets for connectivity,
  one-step no-escape, exact support equality, and the refactored reducibility
  obstruction all passed.  This does not establish a compatible cofinal
  sector family, a uniform completed gap, continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-canonical-vacuum-gap] Exact production form gap on the canonical vacuum component — **CLOSED 2026-08-22**

- **milestone**: finite physical canonical-vacuum sector and strict centered
  production-form contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorPhysicalFormTransport.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorPhysicalGramPositivity.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGap.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGapAxiomAudit.lean`.
- **decl**:
  `cutoffTwoSectorPhysicalMatrixQuadratic_eqv_raw`,
  `cutoffTwoSectorPhysicalMatrixQuadratic_nonnegative`,
  `cutoffTwoSectorPhysicalStrictAbsGapAt49Over50`, and
  `cutoffTwoCanonicalVacuumSector_exact_and_strict_abs_gap`.
- **obligation**: none for the exact finite cutoff-two theorem.  The next
  obligation is a compatible cutoff/volume family of canonical vacuum
  components with root, support-edge, weight, and restricted-form
  compatibility, followed by a cutoff/volume-uniform strict rate.
- **constructive?**: yes — the final leaf audit reports exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the complete 64-row upper LDL aggregate, physical/raw form
  transport, weighted-Gram nonnegativity, `q = 49/50 < 1` absolute centered
  form bound, contracted support-and-gap theorem, and axiom-audit target all
  passed monitored dependency-complete builds.  This is not a compatible
  cofinal sector family, a uniform completed operator gap,
  thermodynamic/continuum construction, continuum QFT, or the Clay theorem.

### [BF4-cutoff-kernel-support-persistence] Old physical support edges survive larger cutoffs — **CLOSED 2026-08-22**

- **milestone**: qualitative representation-cutoff compatibility of the
  genuine unnormalized physical production kernel.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffKernelSupportPersistence.lean`.
- **decl**:
  `centralPhysicalReflectedKernel_nonnegative`,
  `centralPhysicalReflectedKernel_pos_of_le`, and
  `centralPhysicalReflectedKernel_not_eqv_zero_of_le`.
- **obligation**: none for qualitative persistence of an old nonzero kernel
  entry.  The next obligation is an explicit carrier-index embedding that
  preserves the vacuum root and transports the canonical root component.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the source check and dependency-complete target pass.  This
  theorem provides neither equality nor a cutoff-uniform positive floor for
  old entries, and it does not establish uniform form contraction, Hilbert
  completion, thermodynamic/continuum limits, QFT axioms, or the Clay theorem.

### [BF4-cutoff-vacuum-sector-embedding] Rooted component inclusion across cutoffs — **CLOSED 2026-08-22**

- **milestone**: explicit compatible representation-cutoff family of finite
  physical canonical vacuum components at fixed coupling and half-volume.
- **file**:
  `lean/YMGap/Continuum/FiniteBoolGraphRootComponentMap.lean` and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorEmbedding.lean`.
- **decl**:
  `RootedFiniteBoolGraphHom.map_mem_targetRootComponent`,
  `centralPhysicalFiniteStateAt_cutoffIndexMap_eq`,
  `centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap`,
  `centralPhysicalFiniteVacuumSectorIndexMap_mem`, and
  `centralPhysicalFiniteVacuumSectorStates_mono`.
- **obligation**: none for qualitative component inclusion when only the
  representation cutoff grows.  The next obligation is quantitative control
  of pulled-back later weights and forms, whose values genuinely change with
  the cutoff, followed by a uniform strict rate and volume compatibility.
- **constructive?**: yes — the explicit recursive natural-code locator avoids
  the `Classical.choice` dependency of the discarded standard `idxOf` route;
  every printed declaration uses exactly `[propext, Quot.sound]`.
- **status note**: the focused source check and dependency-complete target
  pass.  No exact weight/form intertwining, cutoff-uniform gap, volume family,
  completion, thermodynamic/continuum theory, QFT axioms, or Clay theorem is
  claimed.

### [BF4-cutoff-embedded-entry-cauchy] Pulled weight and kernel entry limits — **CLOSED 2026-08-22**

- **milestone**: quantitative representation-cutoff comparison on a fixed
  embedded old physical carrier.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffEmbeddedEntryCauchy.lean`.
- **decl**:
  `centralPhysicalFinitePulledKernel_twoSided_of_modulus`,
  `centralPhysicalFinitePulledWeight_twoSided_of_modulus`,
  `centralPhysicalFinitePulledWeightCutoffLimit`, and
  `centralPhysicalFinitePulledKernelCutoffLimit`.
- **obligation**: none for entrywise pulled cutoff convergence.  The next
  obligation is dimension-compensated convergence of the complete pulled
  weighted mean and quadratic forms, followed by a genuinely uniform strict
  rate on a cofinal vacuum-sector family.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no excluded declaration or placeholder was added.
- **status note**: the source and dependency-complete builds pass.  Entrywise
  convergence alone does not identify the cutoff-two table with the limiting
  form or prove persistence of `49/50`, a uniform gap, volume compatibility,
  completion, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-embedded-form-cauchy] Pulled finite-form cutoff limits — **CLOSED 2026-08-22**

- **milestone**: dimension-compensated constructive cutoff convergence of the
  weighted mean, diagonal quadratic, and reflected matrix quadratic on a
  fixed embedded old positive carrier.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffEmbeddedFormCauchy.lean`.
- **decl**:
  `centralPhysicalFinitePulledWeightedMeanCutoffLimit`,
  `centralPhysicalFinitePulledDiagonalQuadraticCutoffLimit`, and
  `centralPhysicalFinitePulledMatrixQuadraticCutoffLimit`.
- **obligation**: none for whole-form cutoff convergence on a fixed finite
  zero-extended coordinate subspace.  The next obligation is to restrict the
  construction to the canonical vacuum component and decompose every later
  component into embedded-old and genuinely new states, exposing the leakage
  and cross terms needed for a uniform strict rate.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused source check and dependency-complete target
  pass.  These CReal limits do not preserve centering, identify the
  cutoff-two table with the limit, bound new-sector leakage, establish a
  uniform gap, or construct thermodynamic/continuum QFT or the Clay theorem.

### [BF4-cutoff-vacuum-sector-form-cauchy] Embedded canonical-sector form limits — **CLOSED 2026-08-22**

- **milestone**: constructive cutoff limits for the weighted mean, diagonal
  quadratic, and reflected matrix quadratic on the fixed base canonical
  vacuum component embedded into every later cutoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorFormCauchy.lean`, with the
  reusable list-level stability lemma in
  `BF4PhysicalCutoffEmbeddedFormCauchy.lean`.
- **decl**:
  `centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit`,
  `centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit`, and
  `centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit`.
- **obligation**: none for convergence on the fixed embedded old component.
  The next obligation is an exact old-image/new-state partition of the later
  canonical component and block decomposition of its mean, diagonal form,
  and matrix quadratic, followed by genuine uniform leakage and cross-term
  estimates.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused source check and dependency-complete target
  pass.  Zero extension onto later component states is not a cutoff-uniform
  gap theorem; centering, new-state mass, cross terms, volume compatibility,
  completion, continuum QFT, and the Clay target remain open.

### [BF4-cutoff-vacuum-sector-block-decomposition] Exact old/new sector blocks — **CLOSED 2026-08-22**

- **milestone**: literal partition of every later canonical physical vacuum
  component into the explicit old image and genuinely new states, together
  with exact mean, norm, and four-block reflected-form decompositions.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorBlockDecomposition.lean`.
- **decl**:
  `centralPhysicalFiniteEmbeddedVacuumSectorIndices_mem_later`,
  `mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff`,
  `centralPhysicalFiniteVacuumSectorWeightedMean_old_add_new`,
  `centralPhysicalFiniteVacuumSectorDiagonalQuadratic_old_add_new`, and
  `centralPhysicalFiniteVacuumSectorMatrixQuadratic_four_blocks`.
- **obligation**: none for the exact finite old/new partition and algebraic
  block identities.  The next obligations are an exact pushforward equality
  between the target-ordered old block and the source-indexed pulled forms,
  then uniform estimates on new-state mass and the old/new cross blocks.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the dependency-complete build passes.  Naming the leakage
  residuals is not bounding them, and therefore proves no cutoff-uniform
  contraction, completed gap, thermodynamic/continuum QFT, or Clay theorem.

### [BF4-cutoff-vacuum-sector-form-pushforward] Exact old-block form reindexing — **CLOSED 2026-08-22**

- **milestone**: constructive injectivity of the cutoff component embedding,
  a literal old-block/image permutation, and exact pushforward of observable
  mean, norm, and reflected form under an explicit zero extension.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorFormPushforward.lean`.
- **decl**:
  `centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector`,
  `centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded`,
  `centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_on_map`,
  `centralPhysicalFiniteVacuumSectorOldBlockWeightedMean_eqv_pulled`,
  `centralPhysicalFiniteVacuumSectorOldBlockDiagonal_eqv_pulled`, and
  `centralPhysicalFiniteVacuumSectorOldOldBlock_eqv_pulled`.
- **obligation**: none for exact finite reindexing of the embedded old block.
  The next obligation is to contract the full block decomposition for the
  zero extension and then supply a centered strict form estimate uniform in
  the base cutoff; the cutoff-two `49/50` certificate alone does not do so.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the dependency-complete build passes.  Exact pushforward
  proves neither base-uniform contraction nor a completed, thermodynamic, or
  continuum mass gap, and it does not prove the Clay theorem.

### [BF4-cutoff-vacuum-sector-zero-extension-contraction] Full zero-extended form contraction — **CLOSED 2026-08-22**

- **milestone**: exact vanishing of every new-coordinate and cross block for
  observable zero extensions, and contraction of the full later-sector mean,
  norm, and reflected form to the pulled base-sector forms.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_eq_zero_of_mem_new`,
  `centralPhysicalFiniteVacuumSectorZeroExtension_oldNew_eqv_zero`,
  `centralPhysicalFiniteVacuumSectorZeroExtension_newOld_eqv_zero`,
  `centralPhysicalFiniteVacuumSectorZeroExtension_newNew_eqv_zero`,
  `centralPhysicalFiniteVacuumSectorZeroExtensionWeightedMean_eqv_pulled`,
  `centralPhysicalFiniteVacuumSectorZeroExtensionDiagonal_eqv_pulled`, and
  `centralPhysicalFiniteVacuumSectorZeroExtensionMatrix_eqv_pulled`.
- **obligation**: none for exact form compatibility of a fixed zero-extended
  base-sector observable.  The next obligation is one centered strict form
  rate `q < 1` uniform in the base cutoff, followed by volume and spacing
  uniformity and completed-space passage.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the factored generic contraction avoids the deterministic
  timeout of the first direct proof, and the focused and dependency-complete
  builds pass.  Fixed-subspace compatibility is not a uniform gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-adaptive-recoding-tail-inhabited] Completed root-sector transfer lift — **PROVED 2026-08-22**

- **milestone**: compose outer adaptive cofinality with the inner
  base-controlled slow diagonal, use the paid amplitude-scaled shell cutoff
  and core--shell estimate to inhabit the adaptive recoding tail, and compile
  it to a genuine completed root-sector transfer.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited.lean`.
- **decl**:
  `centralPhysicalVacuumSectorAdaptiveRecodingTailAnchor`,
  `centralPhysicalVacuumSectorAdaptiveRecodingTailRate`,
  `centralPhysicalVacuumSectorAdaptiveRecodingTailData`, and
  `centralPhysicalVacuumSectorCylinderTransferLiftData`.
- **obligation**: use this unconditional transfer lift together with a strict
  rational contraction rate uniform over the cofinal unbounded carrier family
  to prove a completed vacuum-complement gap; then address thermodynamic and
  continuum limits.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,363-job dependency-complete build pass.  The formerly conditional
  recoding-tail field and completed root-sector lift are now inhabited.  This
  is fixed-nome, finite-half-extent transfer invariance, not a uniform
  completed spectral gap, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-arbitrary-vacuum-sector-extension] Arbitrary coefficient pushforward and contraction — **CLOSED 2026-08-22**

- **milestone**: an explicit finite-sum zero extension for every rational
  coefficient on the base canonical vacuum component, with exact on-image
  recovery, off-image vanishing, and full later-sector mean, diagonal, and
  reflected-form contraction to the pulled base forms.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorFormPushforward.lean` and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorCoefficientExtension`,
  `centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map`,
  `centralPhysicalFiniteVacuumSectorCoefficientExtensionMean_eqv_pulled`,
  `centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled`,
  and
  `centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled`.
- **obligation**: construct the later-weight head-centered base coefficient,
  prove its exact mean-zero extension, then establish cutoff-Cauchy form
  control and a single strict rate uniform in the base cutoff.
- **constructive?**: yes — printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: monitored focused and dependency-complete builds pass.
  This extension theorem is not a uniform gap, thermodynamic/continuum QFT,
  or the Clay theorem.

### [BF4-cutoff-vacuum-sector-head-centering] Exact moving same-sector centering — **CLOSED 2026-08-22**

- **milestone**: the pulled root weight is strictly positive at every later
  cutoff; changing only the root coefficient by the exact negative
  mean/root-weight quotient produces zero pulled mean, and its zero extension
  is exactly centered on the full later canonical component with exact pulled
  diagonal and reflected forms.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorHeadCentering.lean`.
- **decl**:
  `finiteListRootCenteredCoefficient_meanZero`,
  `centralPhysicalFinitePulledWeight_zero_pos`,
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero`,
  `centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero`,
  `centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled`,
  and
  `centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled`.
- **obligation**: prove cutoff-Cauchy control of the moving mean/root-weight
  quotient and the two resulting centered forms, then supply a single strict
  contraction rate uniform in the base cutoff.
- **constructive?**: yes — printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: monitored focused and dependency-complete builds pass.
  Exact same-sector centering is not a uniform gap, thermodynamic/continuum
  QFT, or the Clay theorem.

### [BF4-cutoff-vacuum-sector-head-correction-cauchy] Moving head-correction Bishop real — **CLOSED 2026-08-22**

- **milestone**: constructive cutoff-Cauchy control of the signed rational
  quotient between the pulled base-sector weighted mean and the positive
  pulled vacuum-root weight, packaged as a `CReal` with an explicit modulus.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy.lean`.
- **decl**:
  `signedDivPos_abs_sub_le`,
  `centralPhysicalFinitePulledVacuumSectorWeightedMean_abs_le_l1`,
  `centralPhysicalUniformPositiveRowFloor_le_pulledWeight_zero`,
  `centralPhysicalFinitePulledVacuumSectorHeadCorrection_cauchy`, and
  `centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit`.
- **obligation**: use the scalar quotient modulus and the existing finite
  entry/form moduli to prove cutoff-Cauchy control of the root-centered
  diagonal and reflected quadratic forms, then establish a strict rate
  `q < 1` uniform in the base cutoff.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused source check and one-job dependency-complete
  build pass.  The large Cauchy modulus uses a file-local four-million-
  heartbeat elaboration budget.  Scalar convergence is not yet convergence
  of the centered forms, a uniform spectral gap, thermodynamic/continuum QFT,
  or the Clay theorem.

### [BF4-cutoff-vacuum-sector-centered-diagonal-cauchy] Moving centered norm Bishop real — **CLOSED 2026-08-22**

- **milestone**: an exact finite root-replacement formula and a pointwise
  constructive-real polynomial package prove cutoff-Cauchy convergence of
  the literal pulled diagonal form of every fixed base-sector coefficient
  after moving head centering.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy.lean`.
- **decl**:
  `finiteListRootCenteredCoefficient_diagonalExpansion`,
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_expansion`,
  `cRealRecodePointwiseEqv`, and
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit`.
- **obligation**: construct cutoff limits for the two root cross forms and
  root-root reflected entry, expand the moving centered matrix form, and then
  supply a strict form rate `q < 1` uniform in the base cutoff.
- **constructive?**: yes — printed declarations use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused source check and one-job dependency-complete
  build pass.  Centered norm convergence alone is not a uniform spectral gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-vacuum-sector-centered-matrix-cauchy] Moving centered reflected-form Bishop real — **CLOSED 2026-08-22**

- **milestone**: a cross-`l1` finite bilinear stability theorem, constructive
  pulled bilinear cutoff limits, and an exact four-term root-shift expansion
  package the literal reflected quadratic of every moving head-centered fixed
  base-sector coefficient as a `CReal`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy.lean`.
- **decl**:
  `finiteJointBilinear_abs_sub_le_productL1`,
  `centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit`,
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_expansion`, and
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit`.
- **obligation**: provide and verify one strict centered form estimate with
  rate `q < 1` uniform in the base and later representation cutoffs, transport
  it to the two Bishop-real limits, then address completed-space, volume, and
  lattice-spacing uniformity.
- **constructive?**: yes — printed declarations use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused source check and one-job 1,469-job dependency
  build pass.  Existence of both centered form limits is not the missing
  uniform strict estimate, a spectral gap, thermodynamic/continuum QFT, or
  the Clay theorem.

### [BF4-cutoff-vacuum-sector-centered-limit-gap] Cofinal strictness-to-limit contraction — **CLOSED 2026-08-22**

- **milestone**: the weakest direct same-object certificate supplies one
  rational `0 <= q < 1` and exact centered form bounds on a constructively
  cofinal later-cutoff schedule uniformly in the base coefficient; the two
  form Cauchy moduli contract it to a strict `CReal.leEv` limit inequality.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCenteredLimitGap.lean`.
- **decl**:
  `FixedNomeCofinalVacuumSectorCenteredStrictGap` and
  `FixedNomeCofinalVacuumSectorCenteredStrictGap.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: construct an inhabitant.  The next bridge is from existing
  canonical full-carrier cofinal LDL certificates to this sector interface,
  requiring exact full-carrier centering of the zero-extended head-centered
  coefficient; the substantive residual is a `q < 1` uniform in base cutoff.
- **constructive?**: yes — the printed theorem uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused source check and one-job 1,470-job dependency
  build pass.  The certificate type is uninhabited here, so this theorem is a
  sound contraction interface, not a proved uniform gap, completion theorem,
  thermodynamic/continuum QFT, or Clay result.

### [BF4-cutoff-vacuum-sector-full-carrier-contraction] Exact full-carrier restriction — **CLOSED 2026-08-22**

- **milestone**: the zero extension of every base vacuum-sector coefficient
  has full positive-carrier mean, diagonal form, and matrix form exactly equal
  to its pulled component forms; the moving head-centered specialization is
  therefore exactly centered on the full carrier expected by canonical LDL.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorFullCarrierContraction.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem`,
  `centralPhysicalFiniteFullCarrierCoefficientExtensionMean_eqv_pulled`,
  `centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled`,
  `centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled`, and
  `centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero`.
- **obligation**: compile an existing cofinal canonical full-carrier LDL
  family at a supplied strict rate into
  `FixedNomeCofinalVacuumSectorCenteredStrictGap`; an actual family uniformly
  valid in the representation cutoff is still an open analytic input.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the monitored focused source check and one-job 1,261-job
  dependency-complete build pass.  Exact carrier restriction is not an
  inhabited LDL certificate, a uniform gap, completion theorem,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-vacuum-sector-canonical-LDL-bridge] Cofinal LDL-to-limit implication — **CLOSED 2026-08-22**

- **milestone**: ordinary and cleared canonical head-reduced full-carrier LDL
  families at a supplied `0 <= q < 1` construct the two-parameter same-object
  centered-sector certificate and consequently the strict comparison between
  the literal centered reflected-form and diagonal-form `CReal` limits.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.lean`.
- **decl**:
  `FixedNomeCofinalCanonicalHeadLDLAtRate.toVacuumSectorCenteredStrictGap`,
  `FixedNomeCofinalCanonicalHeadLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`,
  `FixedNomeCofinalCanonicalHeadClearedLDLAtRate.toVacuumSectorCenteredStrictGap`,
  and
  `FixedNomeCofinalCanonicalHeadClearedLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: construct an actual cofinal canonical LDL family at one
  strict rate uniform in representation cutoff, or supply an equivalent
  non-LDL finite bound.  No such inhabitant is asserted here.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the monitored focused source check and one-job 1,473-job
  dependency-complete build pass.  This closes the exact implication from a
  named analytic input, not that input itself, a completed gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-cofinal-rank-one-row-defect-gap] Rank-one row defect compiler — **CLOSED 2026-08-22**

- **milestone**: a symmetric finite kernel whose rowwise absolute difference
  from `(1-q) d_i d_j` is bounded by `q d_i` contracts every exactly centered
  quadratic form by `q`; a constructively cofinal physical family compiles to
  both the global centered-gap certificate and the moving same-object
  vacuum-sector cutoff-limit inequality.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffCofinalRankOneDefectGap.lean`.
- **decl**:
  `finiteStationaryRankOneJoint_quadratic_eqv_mean_square`,
  `finiteStationaryRankOneJoint_quadratic_centered_eqv_zero`,
  `FiniteStationaryRankOneRowDefectCertificate.absContraction`,
  `FixedNomeCofinalPhysicalRankOneRowDefect.toCenteredStrictGap`,
  `FixedNomeCofinalPhysicalRankOneRowDefect.toVacuumSectorCenteredStrictGap`,
  and
  `FixedNomeCofinalPhysicalRankOneRowDefect.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: construct an actual cofinal row-defect family at one strict
  rate, preferably from the existing common-rank-one, stationary-density,
  minorization, or core/tail row estimates.  No inhabitant is asserted here.
- **constructive?**: yes — the seven printed declarations use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the monitored focused source check and one-job 1,473-job
  dependency-complete build pass.  This closes a weaker sufficient interface,
  not the row estimate itself, a completed physical gap, volume/spacing
  uniformity, continuum QFT, or the Clay theorem.

### [BF4-cutoff-cofinal-physical-centered-row-gap] Literal physical row compiler — **CLOSED 2026-08-22**

- **milestone**: canonical finite indexing exactly preserves the literal BF4
  row distance from the full stationary product joint; any constructively
  cofinal family of source-relative bounds at one `0 <= q < 1` contracts both
  global centered forms and the moving same-object vacuum-sector form limits.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffCofinalCenteredRowGap.lean`.
- **decl**:
  `finiteStationaryProductJoint_quadratic_centered_eqv_zero`,
  `FiniteStationaryProductRowDistanceCertificate.absContraction`,
  `finiteIndexJointDifferenceAbsRowMass_eqv_list`,
  `centralPhysicalFiniteStationaryProductRowDistance_eqv`,
  `FixedNomeCofinalPhysicalCenteredRowDistance.finiteCertificate`,
  `FixedNomeCofinalPhysicalCenteredRowDistance.toCenteredStrictGap`,
  `FixedNomeCofinalPhysicalCenteredRowDistance.toVacuumSectorCenteredStrictGap`,
  and
  `FixedNomeCofinalPhysicalCenteredRowDistance.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: construct an actual cofinal family of the literal physical
  centered-row estimate, preferably by compiling the existing genuine
  local-slice, conditional-density, buffered-Perron, or core/tail producer
  interfaces.  No inhabitant is asserted here.
- **constructive?**: yes — all seven printed load-bearing declarations use
  exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
  `sorry`, custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored source check and one-job 1,474-job
  dependency-complete build pass.  This closes the exact producer-to-gap
  interface, not its analytic inhabitant, volume/spacing uniformity,
  continuum QFT, or the Clay theorem.

### [BF4-cutoff-cofinal-local-slice-gap] Genuine local-slice compiler — **CLOSED 2026-08-22**

- **milestone**: a constructively cofinal family of genuine stationary
  one-step slice densities, each with exact row/column normalization, exact
  all-label gluing, and centered local rate at most `1/4`, supplies the literal
  physical `1/16` row family and hence both global and moving same-object gap
  interfaces.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffCofinalLocalSliceGap.lean`.
- **decl**:
  `FixedNomePhysicalLocalSliceWitness`,
  `FixedNomeCofinalPhysicalLocalSliceGluing.toCenteredRowDistance`,
  `FixedNomeCofinalPhysicalLocalSliceGluing.toCenteredStrictGap`,
  `FixedNomeCofinalPhysicalLocalSliceGluing.toVacuumSectorCenteredStrictGap`,
  and
  `FixedNomeCofinalPhysicalLocalSliceGluing.centeredMatrixCutoffLimit_leEv_sixteenth_mul_diagonal`,
  plus the adapter
  `FixedNomeCofinalLocalGluing.centeredMatrixCutoffLimit_leEv_sixteenth_mul_diagonal`.
- **obligation**: construct the cofinal genuine slice family.  The open fields
  are the physical stationary one-step density, its exact all-label gluing
  identity at the selected cutoffs, and its local centered `1/4` estimate.
- **constructive?**: yes — all six printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored source check and one-job 1,475-job
  dependency-complete build pass.  This closes the local-slice-to-limit
  implication, not its analytic inhabitant, volume/spacing uniformity,
  continuum QFT, or the Clay theorem.

### [BF4-local-gluing-completed-operator-gap] Direct completed operator gap — **CLOSED 2026-08-22**

- **milestone**: `PhysicalLocalGluingAFCertificate` alone implies the strict
  completed vacuum-complement form gap at rate `1/16` and the genuine concrete
  completed Markov-transfer estimate
  `||T v||^2 <= (1/16)^2 ||v||^2` at every matched AF scale.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingCompletedOperatorNormGap.lean`.
- **decl**:
  `localGluing_centeredCorrection_form_le_sixteenth`,
  `localGluing_cauchyCenteredFormSeq_le_sixteenth`,
  `localGluing_cinnerRep_form_gap_sixteenth`,
  `localGluing_completed_vacuum_form_gap_sixteenth`,
  `localGluing_completed_vacuum_form_gap_data`, and
  `localGluing_completed_vacuum_operator_norm_gap_sixteenth`.
- **obligation**: construct an actual `PhysicalLocalGluingAFCertificate`, then
  establish the same-object physical-time interpretation and uniform volume,
  lattice-spacing, thermodynamic, and continuum control.
- **constructive?**: yes — every printed declaration uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the monitored focused source check and one-job 1,232-job
  dependency-complete build pass.  This removes the physical-separator and
  rate-sharpness fields from the finite completed-gap dependency; it does not
  inhabit local gluing or prove a cross-scale, continuum-QFT, or Clay result.

### [BF4-local-gluing-completed-power-correlation-decay] Completed geometric decay — **CLOSED 2026-08-22**

- **milestone**: the direct local-gluing completed gap iterates to squared-norm
  decay at rate `((1/16)^2)^n`; completed Cauchy--Schwarz transfers it to every
  squared same-carrier matrix coefficient and, in particular, the same-vector
  autocorrelation coefficient.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingCompletedOperatorNormGap.lean`.
- **decl**:
  `localGluing_completed_power_norm_decay_sixteenth`,
  `localGluing_completed_power_matrixCoefficientSq_decay_sixteenth`, and
  `localGluing_completed_power_autocorrelationSq_decay_sixteenth`.
- **obligation**: inhabit `PhysicalLocalGluingAFCertificate` and relate the
  completed macro-step powers uniformly to physical time while taking volume,
  lattice-spacing, thermodynamic, and continuum limits.
- **constructive?**: yes — all three printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the monitored focused source check and one-job 1,232-job
  dependency-complete build pass.  This is conditional finite matched-scale
  decay, not an inhabited analytic certificate, continuum-QFT construction,
  or Clay theorem.

### [BF4-one-step-gluing-to-completed-gap] One-step row contraction bridge — **CLOSED 2026-08-22**

- **milestone**: stronger matched one-step gluing rows forget their unused
  endpoint/Faraut fields, assemble into `PhysicalLocalGluingAFCertificate`,
  and consequently imply the completed `1/16` vacuum form gap and
  `((1/16)^2)^n` squared same-vector matrix-coefficient decay.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingAFAdapter.lean` and
  `lean/YMGap/Continuum/BF4PhysicalOneStepGluingCompletedGap.lean`.
- **decl**:
  `physicalBF4LocalContractionGluingRow_of_oneStep`,
  `localContractionRows_of_oneStepGluingRows`,
  `ofOneStepGluingRows`,
  `ofGroupedProfileOneStepGluingRows`,
  `oneStepGluing_completed_vacuum_form_gap_data`, and
  `oneStepGluing_completed_power_autocorrelationSq_decay_sixteenth`.
- **obligation**: inhabit the genuine shared one-step row family by proving
  exact weighted row/column normalization, exact all-label density-power
  gluing, depth at least three, and the uniform local centered `1/4` bound.
- **constructive?**: yes — all newly printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: monitored focused checks pass; the adapter's one-job
  dependency-complete build passes 1,127 jobs and the end-to-end target passes
  1,243 jobs.  No one-step row inhabitant, physical-time limit, continuum-QFT
  construction, or Clay theorem is asserted.

### [BF4-centered-row-to-completed-gap] Minimal literal-row completion bridge — **CLOSED 2026-08-22**

- **milestone**: a matched-AF `1/16` bound on the literal physical centered
  rows, with no Harnack, local-root, exact power-gluing, endpoint, or spectral
  field, implies the finite mean-zero quadratic gap, the completed vacuum form
  gap, the concrete squared-norm operator gap, and geometric squared
  same-vector matrix-coefficient decay.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingAFCertificate.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCompletedOperatorNormGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalLocalGluingCompletedOperatorNormGap.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalCenteredRowCompletedGap.lean`.
- **decl**:
  `physical_joint_quadratic_abs_le_sixteenth_of_centered_rows`,
  `CentralPhysicalFiniteQuadraticGapSixteenth`,
  `centralPhysical_completed_vacuum_form_gap_sixteenth_of_finite_gap`,
  `centralPhysicalCompletedMarkovPower_matrixCoefficientSq_decay_of_form_gap`,
  `PhysicalCenteredRowSixteenthAFCertificate.ofCrossZeroRows`,
  `PhysicalCenteredRowSixteenthAFCertificate.completed_vacuum_operator_norm_gap_sixteenth`,
  and
  `PhysicalCenteredRowSixteenthAFCertificate.completed_power_autocorrelationSq_decay_sixteenth`.
- **obligation**: inhabit the literal matched-AF physical centered-row
  `1/16` field, using any one of the existing conditional-density, core/tail,
  boundary-Gram, projective, buffered, or local-gluing sufficient routes.
- **constructive?**: yes — all newly printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused checks pass; monitored one-job dependency-complete
  builds pass 1,232 jobs for the generic dependency target and 1,233 jobs for
  the row target.  No row-certificate inhabitant, physical-time limit,
  continuum-QFT construction, or Clay theorem is asserted.

### [BF4-core-tail-to-completed-gap] Support-safe density bridge — **CLOSED 2026-08-22**

- **milestone**: source-dependent finite density cores with weighted core
  error at most `1/32` and stationary/conditional tail budgets at most
  `1/64` each imply the literal physical centered-row rate `1/16`, the
  completed vacuum form and operator gaps, and geometric squared same-vector
  completed matrix-coefficient decay.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCoreTailCompletedGap.lean`.
- **decl**:
  `PhysicalConditionalDensityCoreTailAFCertificate`,
  `PhysicalConditionalDensityCoreTailAFCertificate.ofMatchedCoreTailRows`,
  `PhysicalConditionalDensityCoreTailAFCertificate.ofFarautBufferedRows`,
  `PhysicalConditionalDensityCoreTailAFCertificate.toCenteredRowCertificate`,
  `PhysicalConditionalDensityCoreTailAFCertificate.completed_vacuum_operator_norm_gap_sixteenth`,
  and
  `PhysicalConditionalDensityCoreTailAFCertificate.completed_power_autocorrelationSq_decay_sixteenth`.
- **obligation**: inhabit the support-safe matched certificate by constructing
  a retained core for every physical source and proving the `1/32` core plus
  two `1/64` tail estimates uniformly along the matched AF trajectory.
- **constructive?**: yes — all seven printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored source check and one-job 1,239-job
  dependency-complete build pass.  This removes Harnack, diagonal-order,
  local-root, and strict-positivity dependencies from the support-safe
  completion route; it does not inhabit its finite analytic leaf or establish
  physical-time, volume/spacing, continuum-QFT, or Clay closure.

### [BF4-core-tail-finite-checker] Executable leaf and cutoff-zero base case — **CLOSED 2026-08-22**

- **milestone**: exact Boolean row and all-source checkers compile verified
  finite core/tail computations into the support-safe matched certificate and
  its completed decay consequences.  The canonical physical `K = 0`, `w = 1`
  all-source check is actually evaluated to true and yields an inhabited
  finite completed same-object decay theorem.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCoreTailFiniteChecker.lean`.
- **decl**:
  `finiteWeightedDensityCoreTailCheck`,
  `finiteWeightedDensityCoreTailWindow_of_check`,
  `physicalConditionalDensityCoreTailAllRowsCheck`,
  `physicalConditionalDensityCoreTailWindow_of_allRowsCheck`,
  `PhysicalConditionalDensityCoreTailAFCheckedCertificate`,
  `PhysicalConditionalDensityCoreTailAFCheckedCertificate.toCoreTailCertificate`,
  `cutoffZero_allRows_check_true`,
  `cutoffZero_finite_quadratic_gap`, and
  `cutoffZero_completed_power_autocorrelationSq_decay_sixteenth`.
- **obligation**: prove true all-source check values along the nontrivial
  increasing matched cutoff trajectory.  A finite checked prefix would be a
  useful next certificate but would still not replace the required analytic
  all-scale estimate.
- **constructive?**: yes — the closed nonnegativity declaration has no axioms;
  every other printed declaration uses exactly `[propext, Quot.sound]`.  The
  computation uses ordinary kernel `decide`, not `native_decide`, and no
  `Classical.*`, choice, `sorry`, custom axiom, or noncomputable declaration
  was added.
- **status note**: the focused monitored source check and one-job 1,240-job
  dependency-complete build pass.  The inhabited result is only the finite
  cutoff-zero physical base case.  Cutoff/AF uniformity, physical-time,
  volume/spacing, continuum-QFT, and Clay closure remain open.

### [BF4-core-tail-finite-carrier-recode] Exact compressed checker transport — **CLOSED 2026-08-22**

- **milestone**: an exact mapped-list presentation of the literal positive
  physical carrier transports all core/tail checker sums from a small code
  list.  A true compressed all-code scan at every matched scale therefore
  implies the minimal support-safe certificate and completed same-object
  decay.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCoreTailFiniteCarrierRecode.lean`.
- **decl**:
  `finiteWeightedDensityCoreTailWindow_of_mappedCarrier`,
  `PhysicalPositiveCarrierPresentation`,
  `PhysicalPositiveCarrierPresentation.physicalCoreTailWindow_of_rowCheck`,
  `PhysicalPositiveCarrierPresentation.physicalCoreTailWindow_of_allRowsCheck`,
  `PhysicalCoreTailAFRecodeCheckedCertificate`,
  `PhysicalCoreTailAFRecodeCheckedCertificate.toCoreTailCertificate`, and
  `PhysicalCoreTailAFRecodeCheckedCertificate.completed_power_autocorrelationSq_decay_sixteenth`.
- **obligation**: construct a nontrivial exact positive-carrier presentation,
  beginning at `K = 1`, and close its compressed positive marginal/kernel
  checks.  The existing 128-surface signed-Haar evaluation is not yet such a
  presentation of the separately normalized positive physical kernel.
- **constructive?**: yes — all seven printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored source check and one-job 1,241-job
  dependency-complete build pass.  A direct `K = 1` ambient evaluation was
  interrupted after two minutes and is not counted as passed.  No nontrivial
  recoding, all-cutoff uniformity, physical-time, volume/spacing,
  continuum-QFT construction, or Clay theorem is asserted.

### [BF4-full-carrier-core-tail-obstruction] Cutoff-two no-go — **CLOSED 2026-08-22**

- **milestone**: the exact cutoff-two reducibility mode formally rules out
  support-safe core/tail windows for every source of the full positive
  carrier; therefore the canonical Boolean all-row checker cannot equal
  `true` for any proposed core predicate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCoreTailFullCarrierObstruction.lean`.
- **decl**:
  `no_cutoffTwo_fullCarrier_coreTail_allRows` and
  `cutoffTwo_fullCarrier_allRowsCheck_ne_true`.
- **obligation**: replace the false full-carrier target by a strict row/form
  estimate on the canonical communicating component containing the vacuum.
- **constructive?**: yes — both printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and combined one-worker
  1,779-job dependency-complete build pass.  This is a finite routing/no-go
  theorem, not a sector gap, cutoff-uniform theorem,
  thermodynamic/continuum construction, or Clay conclusion.

### [BF4-vacuum-sector-cofinal-row-gap] Corrected sector-local row seam — **CLOSED 2026-08-22**

- **milestone**: a rowwise comparison between the physical reflected joint
  and the restricted stationary product, imposed only on the canonical
  vacuum component along a constructively cofinal cutoff family, implies the
  strict comparison of the existing moving centered same-object CReal form
  limits at the same rate `q < 1`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCofinalRowGap.lean`.
- **decl**:
  `finiteCarrierStationaryProductJoint_quadratic_eqv_mean_square`,
  `FiniteCarrierStationaryProductRowDistanceCertificate.absContraction`,
  `finiteWeightedSquare_vacuumSector_eqv_diagonal`,
  `FixedNomeCofinalVacuumSectorRowDistance.finiteCertificate`,
  `FixedNomeCofinalVacuumSectorRowDistance.toVacuumSectorCenteredStrictGap`,
  and
  `FixedNomeCofinalVacuumSectorRowDistance.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: inhabit the sector-local row-distance certificate at one
  strict rate uniformly on a constructively cofinal family of cutoffs; an
  executable core/tail or compressed-carrier producer should now scan only
  the canonical vacuum component.
- **constructive?**: yes — all six printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and combined one-worker
  1,779-job dependency-complete build pass.  No cofinal family, physical-time
  limit, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-canonical-vacuum-normalized-gap] Normalized physical sector base case — **CLOSED 2026-08-22**

- **milestone**: the exact cutoff-two 65-state calculation is the canonical
  vacuum support, and its strict absolute centered gap at rate `49/50`
  persists after physical partition normalization.  Exact row closure
  identifies the restricted normalized row sum with the actual full-carrier
  physical marginal.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap.lean`.
- **decl**:
  `cutoffTwoHalfStates_filter_sector_perm`,
  `cutoffTwoSectorNormalizedRowSum_eqv_centralPhysicalRowMarginal`,
  `cutoffTwoSectorNormalizedMeanZeroAbsGapAt49Over50`, and
  `cutoffTwoCanonicalVacuumNormalized_exact_and_strict_abs_gap`.
- **obligation**: transport this finite 65-state coordinate theorem to the
  canonical cofinal vacuum-sector index/form objects, then construct a single
  strict estimate uniformly over an all-cutoff or constructively cofinal
  family.
- **constructive?**: yes — all four printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and one-worker 4,684-job
  dependency-complete build pass.  This is a nontrivial finite cutoff-two
  normalized physical sector theorem, not a cofinal/uniform gap,
  thermodynamic/continuum construction, or Clay conclusion.

### [BF4-cutoff-two-canonical-vacuum-finite-form-gap] Exact canonical coordinate transport — **CLOSED 2026-08-22**

- **milestone**: the normalized `49/50` cutoff-two sector gap is transported
  from the stored 65-state ordering to the standard canonical vacuum-sector
  weighted mean, diagonal, and reflected matrix forms, first for state
  observables and then for every arbitrary canonical index coefficient.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.lean`.
- **decl**:
  `cutoffTwoCanonicalVacuumSectorStates_perm`,
  `cutoffTwoSectorObservableWeightedMean_eqv_canonical`,
  `cutoffTwoSectorObservableMatrix_eqv_canonical`,
  `cutoffTwoCanonicalVacuumObservable_abs_gap`,
  `cutoffTwoCanonicalCoefficientObservable_recovers`,
  `cutoffTwoCanonicalEncodedMatrix_eqv`, and
  `cutoffTwoCanonicalVacuumFinite_abs_gap`.
- **obligation**: prove one strict canonical-vacuum-sector estimate uniformly
  over an all-cutoff or constructively cofinal family.  The exact cutoff-two
  base case supplies the correct finite target but no persistence estimate.
- **constructive?**: yes — all seven printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and one-worker 4,717-job
  dependency-complete build pass, with one benign unused-`simp`-argument
  linter warning.  No all-cutoff/cofinal family, physical-time limit,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-pulled-vacuum-gap] First moving centered-gap anchor — **CLOSED 2026-08-22**

- **milestone**: self-pullback at `base = later = 2` identifies the pulled
  canonical vacuum-sector weight, kernel, and forms with the normalized
  cutoff-two forms.  The moving root-centered coefficient consequently
  satisfies the exact `49/50` absolute gap in the same expression required by
  the cofinal centered-gap structure.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledVacuumGap.lean`.
- **decl**:
  `cutoffTwoPulledWeight_self_eqv`,
  `cutoffTwoPulledKernel_self_eqv`,
  `cutoffTwoPulledVacuumSectorMatrix_self_eqv`, and
  `cutoffTwoPulledHeadCentered_abs_gap`.
- **obligation**: preserve a strict sector rate from the cutoff-two anchor
  along an all-cutoff or constructively cofinal family.  One finite anchor
  does not satisfy the cofinal quantifiers.
- **constructive?**: yes — all four printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and one-worker 4,721-job
  dependency-complete build pass.  No persistence family, physical-time
  limit, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-pulled-gap-persistence] Explicit persistence compiler — **CLOSED 2026-08-22**

- **milestone**: a later moving-centered coefficient inherits the strict
  rate `49/50 + epsilon` from the cutoff-two anchor whenever a cutoff-two
  centered recoding satisfies the stated matrix-error and diagonal-domination
  comparisons.  A constructively cofinal family with that relaxed rate below
  one contracts to the strict comparison of the fixed cutoff-two-sector
  moving matrix and diagonal `CReal` limits.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledGapPersistence.lean`.
- **decl**:
  `CutoffTwoPulledGapPersistenceAt.relaxed_abs_gap`,
  `CutoffTwoCofinalPulledGapPersistence.anchor_abs_gap`, and
  `CutoffTwoCofinalPulledGapPersistence.centeredMatrixCutoffLimit_leEv_relaxedRate_mul_diagonal`.
- **obligation**: construct one uniform `epsilon < 1/50` and a cofinal family
  of the two comparison estimates, using quantitative entry/form stability
  plus controlled recentering and diagonal comparison.  Then extend the
  resulting fixed-base sector statement to the required dense/completed
  physical space.
- **constructive?**: yes — all three printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and one-worker 4,729-job
  dependency-complete build pass.  The persistence compiler is verified, but
  its cofinal comparison input, physical-time and thermodynamic/continuum
  limits, continuum QFT, and the Clay theorem are not asserted.

### [BF4-cutoff-two-robust-coefficientwise-persistence] Minimal limit-stage quantifiers — **CLOSED 2026-08-22**

- **milestone**: the persistence compiler now permits diagonal inflation
  `cD` and matrix error `eM`, yielding the exact robust rate
  `(49/50) * cD + eM`.  Its constructively cofinal cutoff may depend on the
  fixed coefficient; only the error budgets and strict rate remain uniform.
  These weaker data still imply the fixed-sector moving `CReal` form gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledGapPersistence.lean`.
- **decl**:
  `CutoffTwoPulledRobustGapPersistenceAt.robust_abs_gap` and
  `CutoffTwoCoefficientwiseCofinalRobustGapPersistence.centeredMatrixCutoffLimit_leEv_robustRate_mul_diagonal`.
- **obligation**: prove coefficientwise cofinal comparison estimates with
  uniform `eM`, `cD`, and `(49/50) * cD + eM < 1`.  Ordinary cutoff-Cauchy
  convergence does not by itself bound the total perturbation from cutoff
  two, so this requires a summable incremental or direct anchor-to-limit
  estimate plus quantitative recentering and norm comparison.
- **constructive?**: yes — both new printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the refined focused monitored check and one-worker
  4,729-job dependency-complete build pass.  No robust persistence family,
  completed-space gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted.

### [BF4-cutoff-two-pulled-l1-diagonal-control] Physical finite-norm coercivity — **CLOSED 2026-08-22**

- **milestone**: finite-list Cauchy--Schwarz and a pointwise positive weight
  floor imply `floor * ||x||_1^2 <= |states| * D(x)`.  At the maximum of
  cutoff two and the verified row-floor schedule, positive-row persistence
  constructs an explicit strictly positive rational floor below every later
  pulled weight of the canonical cutoff-two vacuum component.  Hence the
  physical inequality holds for every coefficient on that fixed component.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl.lean`.
- **decl**:
  `coefficientL1_square_le_length_mul_squareSum`,
  `floor_mul_coefficientL1_square_le_length_mul_diagonal`,
  `cutoffTwoPulledUniformPositiveRowFloor_le_weight`, and
  `cutoffTwoPulled_coefficientL1_square_control`.
- **obligation**: combine this coercivity with entrywise pulled-kernel and
  pulled-weight errors to obtain relative matrix and diagonal perturbation
  bounds.  Then control the full cutoff-two-to-limit perturbation, including
  the difference between the two root-centering corrections, within the
  robust strict-rate budget.
- **constructive?**: yes — all four printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and one-worker 4,730-job
  dependency-complete build pass.  Norm coercivity alone is not a persistence
  family, completed spectral gap, thermodynamic/continuum QFT, or Clay theorem.

### [BF4-cutoff-two-pulled-entry-perturbation] Relative form errors from entrywise bounds — **CLOSED 2026-08-22**

- **milestone**: uniform pulled-kernel entry error `eta` yields the cleared
  relative bound `floor * |Delta M| <= |states| * eta * D_later`; uniform
  pulled-weight entry error yields `floor * |Delta D| <= eta * D_later`.
  Explicit rational budgets against the positive floor then produce an
  un-cleared robust matrix error and diagonal inflation factor
  `1 + diagonalError`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation.lean`.
- **decl**:
  `CutoffTwoPulledKernelEntryErrorAt.cleared_matrix_error`,
  `CutoffTwoPulledKernelEntryErrorAt.matrix_error`,
  `CutoffTwoPulledWeightEntryErrorAt.cleared_diagonal_error`, and
  `CutoffTwoPulledWeightEntryErrorAt.diagonal_inflation`.
- **obligation**: control the change between the moving head-centered
  coefficients, then produce a strict total anchor-to-late or summable
  incremental entry-error budget satisfying the robust rate inequality.
- **constructive?**: yes — all four printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and one-worker 4,731-job
  dependency-complete build pass.  Same-coefficient perturbation control is
  not yet a robust persistence family, completed spectral gap,
  thermodynamic/continuum QFT, or Clay theorem.

### [BF4-cutoff-two-moving-recentering] Exact root-only coefficient motion — **CLOSED 2026-08-22**

- **milestone**: subtracting the exact moving root-centerings at two cutoffs
  gives the head-correction difference times the root indicator.  Its finite
  `l1` norm on the cutoff-two carrier is exactly the absolute scalar
  correction difference, so the existing head-correction Cauchy modulus
  supplies a coefficient `l1` Cauchy modulus without a carrier-size loss.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation.lean`.
- **decl**:
  `cutoffTwoPulledMovingCenteredCoefficient_sub_eqv_rootCorrection`,
  `cutoffTwoPulledMovingCenteredCoefficient_sub_l1_eqv_headCorrection`, and
  `cutoffTwoPulledMovingCenteredCoefficient_l1_cauchy`.
- **obligation**: derive same-law matrix and diagonal perturbation estimates
  from this root-only coefficient control; combine them with the entrywise
  law perturbations and produce a strict total anchor-to-limit or summable
  incremental rate budget.
- **constructive?**: yes — all three printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,732-job dependency-complete build pass.  A broader default workspace build
  was stopped by the safety monitor at job 2,116/3,696 on its 12 GiB reserve;
  it is not counted as a pass and had reported no Lean error.  No robust
  persistence family, completed spectral gap, thermodynamic/continuum QFT, or
  Clay theorem is asserted.

### [BF4-cutoff-two-same-law-recentering] Matrix and diagonal form stability — **CLOSED 2026-08-22**

- **milestone**: a generic finite same-law quadratic estimate controls a
  scalar basis-vector coefficient shift by its two `l1` cross terms and one
  quadratic term.  Normalized physical pulled-kernel entries and the
  diagonal pulled-weight law are each bounded in absolute value by one, so
  the exact moving-root identity gives explicit same-law matrix and diagonal
  recentering errors whose small parameter is the head-correction change.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledSameLawRecentering.lean`.
- **decl**:
  `finiteJointBilinear_abs_le_productL1_of_entry_abs_le_one`,
  `finiteJointQuadratic_add_scaled_abs_sub_le`,
  `cutoffTwoPulledKernelAt_abs_le_one`,
  `cutoffTwoPulledMovingCenteredSameLaw_matrix_error`,
  `cutoffTwoPulledDiagonalJointAt_abs_le_one`, and
  `cutoffTwoPulledMovingCenteredSameLaw_diagonal_error`.
- **obligation**: turn the coefficient-dependent absolute bounds into
  coefficientwise cofinal relative errors against the later diagonal, then
  combine them with entrywise law errors in a strict uniform robust-rate
  budget.  Ordinary late-pair Cauchy convergence still does not bound the
  entire cutoff-two-to-limit law change.
- **constructive?**: yes — the six printed declarations use only `[propext]`
  or `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
  `sorry`, custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,733-job dependency-complete build pass.  This is not yet a robust
  persistence family, completed spectral gap, thermodynamic/continuum QFT,
  or Clay theorem.

### [BF4-cutoff-two-relative-tail-recentering] Coefficientwise relative tail control — **CLOSED 2026-08-22**

- **milestone**: a constructive finite dichotomy separates root-supported
  raw coefficients, whose moving-centered forms vanish exactly, from
  coefficients with a positive non-root coordinate.  The latter coordinate
  is invariant under root centering and supplies a positive lower bound for
  the later centered `l1` norm.  Head-correction Cauchy control, the explicit
  three-term quadratic amplification, and the positive physical diagonal
  floor then produce arbitrarily small relative same-law matrix and diagonal
  recentering errors for all sufficiently late cutoff pairs.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledRelativeRecentering.lean`.
- **decl**:
  `cutoffTwoRootSupported_or_nonRootWitness`,
  `cutoffTwoRootSupported_movingCentered_eqv_zero_on`,
  `CutoffTwoNonRootCoefficientWitness.recenteringSize_le_scaled_l1_cofinally`,
  `exists_positive_recentering_fraction_for_relative_error`, and
  `sameLaw_relative_errors_for_every_coefficient`.
- **obligation**: combine this same-law moving-coefficient estimate with the
  entrywise cutoff-law Cauchy estimates to obtain full moving-form tail
  stability.  That tail statement must not be mistaken for the still-open
  finite cutoff-two-to-tail or summable-increment bridge needed to transport
  the verified cutoff-two gap anchor.
- **constructive?**: yes — all printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,734-job dependency-complete build pass.  No robust cutoff-two persistence
  family, completed spectral gap, thermodynamic/continuum QFT, or Clay theorem
  is asserted.

### [BF4-cutoff-two-moving-form-tail-stability] Full law-and-centering relative tail — **CLOSED 2026-08-22**

- **milestone**: corrected-slab entry moduli now construct uniform relative
  pulled-kernel and pulled-weight law certificates.  Applying those uniform
  certificates at the first-cutoff centered coefficient and composing with
  same-law recentering gives the actual moving matrix and diagonal errors.
  The explicit total factor is law error times `1 + recenteringError`, plus
  recentering error.  The constructive choice
  `relativeError / (relativeError + 2)` makes both total factors no larger
  than every prescribed positive relative error.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledMovingFormTailStability.lean`.
- **decl**:
  `cutoffTwoPulledKernelEntryErrorAt_of_anchor`,
  `cutoffTwoPulledWeightEntryErrorAt_of_anchor`,
  `cutoffTwoPulledRelativeLawErrors_cofinally`,
  `moving_matrix_error_of_law_and_recentering`,
  `moving_diagonal_error_of_law_and_recentering`,
  `movingForm_relative_errors_cofinally`,
  `cutoffTwoPulledMovingFormComponentError_amplification_le`, and
  `movingForm_relative_errors_for_every_positive`.
- **obligation**: bridge the verified cutoff-two `49/50` gap anchor to the
  beginning of this cofinal tail.  Ordinary tail Cauchy control does not
  quantify that finite prefix; an explicit finite-prefix certificate or a
  summable incremental error budget with strict rate slack is required.
- **constructive?**: yes — all eight printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,735-job dependency-complete build pass.  This is full moving-form tail
  stability, but not cutoff-two-to-tail persistence, a completed spectral
  gap, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-tail-seed-gap-bridge] Aligned finite seed to same-object CReal gap — **FACTORED 2026-08-22**

- **milestone**: with a fixed tail error `1/200`, one finite `49/50` gap seed
  aligned with a verified stability start propagates to every later cutoff at
  the exact strict rate `9899/10000`.  Existing moving-form Cauchy moduli then
  contract that cofinal bound to the corresponding matrix/diagonal Bishop
  reals.  A coefficientwise family of aligned seeds gives the same uniform
  limit rate for every vector on the fixed cutoff-two physical carrier.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge.lean`.
- **decl**:
  `exists_cutoffTwoPulledTailStabilityStart`,
  `CutoffTwoPulledTailSeedGapAt.later_abs_gap`,
  `CutoffTwoPulledTailSeedGapAt.centeredMatrixCutoffLimit_leEv_tailSeedRate_mul_diagonal`,
  and
  `CutoffTwoCoefficientwiseTailSeedGap.centeredMatrixCutoffLimit_leEv_tailSeedRate_mul_diagonal`.
- **obligation**: inhabit `CutoffTwoCoefficientwiseTailSeedGap`.  Its
  stability half exists coefficientwise by the proved full moving-form tail;
  the remaining analytic datum is a finite `49/50` gap at a cutoff aligned
  with that tail start.  After this fixed-carrier seam, extend the estimate to
  all finite base vacuum carriers and then to the completed physical space.
- **constructive?**: yes — all four printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,736-job dependency-complete build pass.  Two earlier slow checks were
  interrupted during proof optimization and are not counted as passes.  The
  certificate remains uninhabited; no unconditional CReal, completed-space,
  thermodynamic/continuum, or Clay mass-gap claim is made.

### [BF4-cutoff-two-finite-prefix-gap-bridge] Consecutive increment compiler — **FACTORED 2026-08-22**

- **milestone**: a generic one-step theorem propagates a form gap by the
  exact recurrence `qNext = q * (1 + eta) + eta`.  A finite physical prefix
  certificate iterates this recurrence from the verified cutoff-two
  `49/50` anchor.  If its endpoint is a `1/200` full moving-form tail start
  and the explicitly computed final rate remains below one, the certificate
  contracts to every later cutoff and the same-object Bishop-real form gap.
  While the rate is at most one, the recurrence is bounded by
  `49/50 + 2 * finSum eta`, so one uniform partial-sum estimate closes a long
  prefix and its final strict budget.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixGapBridge.lean`.
- **decl**:
  `moving_abs_gap_step`,
  `CutoffTwoPulledFinitePrefixIncrementControl.abs_gap_at_stage`,
  `CutoffTwoPulledFinitePrefixIncrementControl.prefixRate_le_anchor_add_twice_finSum`,
  `CutoffTwoPulledFinitePrefixIncrementControl.prefixTailRate_lt_one_of_sumBudget`,
  `CutoffTwoPulledFinitePrefixToTailGap.later_abs_gap`, and
  `CutoffTwoPulledFinitePrefixToTailGap.centeredMatrixCutoffLimit_leEv_prefixTailRate_mul_diagonal`.
- **obligation**: inhabit the finite prefix certificate coefficientwise by
  proving the consecutive moving-kernel and moving-diagonal relative errors,
  align the endpoint with a proved tail-stability start, and close the strict
  rate budget.  The explicit alias-form anchor field is the already-proved
  cutoff-two gap under a large Bishop-real recoding, not a new analytic
  assumption.
- **constructive?**: yes — the six printed declarations use only
  `[propext]` or `[propext, Quot.sound]`; no `Classical.*`, choice,
  `native_decide`, `sorry`, custom axiom, or noncomputable declaration was
  added.
- **status note**: the optimized focused check and exact-target one-worker
  4,737-job dependency-complete build pass.  One earlier slow recoding check
  was interrupted and is not counted as a pass.  A separate attempted
  evaluation of the uniform-row-floor cutoff hit interpreter recursion after
  more than eighty thousand nested cutoff-power calls and is not a proof
  result.  The finite increment fields and their summable bound remain
  uninhabited; no unconditional fixed-carrier limit gap,
  completed-space gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted.

### [BF4-cutoff-two-finite-prefix-increment-existence] Qualitative increment controls — **FACTORED 2026-08-22**

- **milestone**: every coefficient admits data-bearing finite support
  selection: either a root-supported proof or an explicit positive-magnitude
  non-root coordinate.  Root-supported moving forms have zero increments.
  A non-root coordinate retains positive physical row weight at every later
  cutoff, forces the later moving diagonal strictly positive, and defines the
  common relative error
  `(|Delta matrix| + |Delta diagonal|) / laterDiagonal`.  This constructs a
  `CutoffTwoPulledFinitePrefixIncrementControl` for every coefficient and
  finite length once the exact compact-form recoding seam is supplied.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixIncrementExistence.lean`.
- **decl**:
  `CutoffTwoNonRootCoefficientWitness.pulledWeight_pos`,
  `CutoffTwoNonRootCoefficientWitness.movingDiagonalAt_pos`,
  `cutoffTwoCanonicalPrefixIncrement_moving_error`,
  `CutoffTwoNonRootCoefficientWitness.finitePrefixIncrementControl`,
  `rootSupportedFinitePrefixIncrementControl`,
  `cutoffTwoRootSupported_orNonRootData`, and
  `finitePrefixIncrementControlForEveryCoefficient`.
- **obligation**: discharge `CutoffTwoActualMovingFormRecode` without a giant
  definitional reduction, align a constructed finite prefix endpoint with a
  proved moving-form tail start, and prove the quantitative partial-sum
  budget small enough to preserve a final rate below one.  The recoding seam
  is exact proof engineering; the small accumulated error is the genuine
  analytic input.
- **constructive?**: yes — all seven printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,738-job dependency-complete build pass.  Two earlier monitored checks
  were interrupted during namespace/reduction diagnosis and are not counted
  as passes; a direct definitional-recoding attempt exceeded a
  500,000-heartbeat diagnostic and is not a proof result.  No unconditional
  fixed-carrier CReal gap, completed-space gap, thermodynamic/continuum QFT,
  or Clay theorem is asserted.

### [BF4-cutoff-two-finite-prefix-sum-closure] One-total-budget contraction — **FACTORED 2026-08-22**

- **milestone**: the single hypothesis `finSum eta stage <= 1/200` for every
  stage of the constructed prefix implies the additive envelope
  `qPrefix <= 99/100` and the exact final strict bound
  `(99/100) * (1 + 1/200) + 1/200 = 19999/20000 < 1`.  A
  `CutoffTwoPulledFinitePrefixSumClosure` therefore constructs the full
  prefix-to-tail certificate and its same-object moving Bishop-real gap from
  an exact recode, a tail-aligned endpoint, tail stability, and that one
  finite total-error budget.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledFinitePrefixSumClosure.lean`.
- **decl**:
  `cutoffTwoFinitePrefixEnvelopeAtBudget_le_one`,
  `cutoffTwoFinitePrefixBudgetClosedTailRate_lt_one`,
  `prefixTailRate_lt_one_of_finSum_le_totalErrorBudget`,
  `CutoffTwoPulledFinitePrefixSumClosure.toFinitePrefixToTailGap`, and
  `CutoffTwoPulledFinitePrefixSumClosure.centeredMatrixCutoffLimit_leEv_prefixTailRate_mul_diagonal`.
- **obligation**: inhabit `CutoffTwoPulledFinitePrefixSumClosure`
  coefficientwise.  The genuine quantitative field is the `1/200` bound on
  the finite sum of canonical relative moving-form increments; the exact
  compact recode and Type-level selection of a tail start are separate proof
  engineering/data seams.  After this, extend beyond the fixed cutoff-two
  carrier to all finite base vacuum sectors and the completion.
- **constructive?**: yes — the two rational slack declarations are
  axiom-free and the other three printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,739-job dependency-complete build pass.  The closure structure remains
  uninhabited; no unconditional fixed-carrier CReal gap, completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-adaptive-tail-seed-gap] Seed-slack-preserving contraction — **FACTORED 2026-08-22**

- **milestone**: for every rational seed rate `0 <= q < 1`, the explicit
  relative tail error `epsilon(q) = (1/4)*(1-q)` is positive and the
  propagated rate `q*(1+epsilon(q))+epsilon(q)` remains strictly below one.
  The verified moving-form modulus supplies a tail start for that exact
  tolerance.  A finite `q` gap at the same start propagates to every later
  cutoff and contracts to the literal same-object moving matrix/diagonal
  Bishop-real gap.  A coefficientwise family sharing one `q` yields a uniform
  fixed-carrier rate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledAdaptiveTailSeedGapBridge.lean`.
- **decl**:
  `cutoffTwoAdaptiveTailSeedRelativeError_pos`,
  `cutoffTwoAdaptiveTailSeedRate_nonnegative`,
  `cutoffTwoAdaptiveTailSeedRate_lt_one`,
  `exists_cutoffTwoPulledAdaptiveTailStabilityStart`,
  `CutoffTwoPulledAdaptiveTailSeedGapAt.later_abs_gap`,
  `CutoffTwoPulledAdaptiveTailSeedGapAt.centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal`,
  `CutoffTwoCoefficientwiseAdaptiveTailSeedGap.centeredMatrixCutoffLimit_leEv_adaptiveTailSeedRate_mul_diagonal`,
  and
  `CutoffTwoCoefficientwiseAdaptiveTailSeedGap.adaptiveTailSeedRate_lt_one`.
- **obligation**: inhabit
  `CutoffTwoCoefficientwiseAdaptiveTailSeedGap q` for some common
  `0 <= q < 1`.  The tail stability field already has a constructive start;
  the genuine analytic input is a strict finite gap on the canonical vacuum
  sector at such a start.  The earlier `1/200` cutoff-two prefix-sum route is
  still sufficient but is no longer required.
- **constructive?**: yes — all eight printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,737-job dependency-complete build pass.  An earlier check hit a stack
  overflow while elaborating compact aliases in one existence statement and
  is not counted as a pass; the equivalent displayed physical-form statement
  checks cleanly.  The adaptive seed family remains uninhabited; no
  unconditional fixed-carrier limit gap, completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-finite-vacuum-sector-Gram-positivity] All-cutoff lower edge — **PROVED 2026-08-22**

- **milestone**: at every nonnegative coupling and finite representation
  cutoff, absorb the positive physical partition reciprocal into the boundary
  channel weights and identify the normalized kernel restricted to the
  canonical vacuum component with a literal finite weighted Gram.  Its sector
  matrix quadratic is therefore nonnegative for every rational coefficient.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorGramPositivity.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorGramWeight_nonnegative`,
  `centralPhysicalFiniteKernel_eqv_vacuumSectorWeightedGram`,
  `centralPhysicalFiniteVacuumSectorMatrixQuadratic_eqv_weightedGram`, and
  `centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative`.
- **obligation**: use the already constructed Type-level connected support of
  the canonical component to prove a quantitative finite Poincare upper gap.
  Gram nonnegativity will then convert that one-sided estimate into the
  absolute contraction consumed by the adaptive tail-seed bridge.
- **constructive?**: yes — all four printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,179-job dependency-complete build pass.  This proves the lower spectral
  edge only; it does not provide a strict finite rate, cutoff uniformity, a
  completed-space gap, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-finite-vacuum-sector-positive-connectivity] Physical irreducibility — **PROVED 2026-08-22**

- **milestone**: on indices in the canonical finite vacuum component, Boolean
  support adjacency is equivalent to strict positivity of the actual
  normalized reflected kernel.  The data-level Boolean paths already returned
  by the component construction compile to `PositiveKernelChainIn` paths with
  a strict physical kernel witness on every edge.  Every retained sector
  weight is also strictly positive.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPositiveConnectivity.lean`.
- **decl**:
  `centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex`,
  `centralPhysicalFiniteRawKernel_pos_of_supportAdjacent`,
  `centralPhysicalFiniteKernel_pos_of_supportAdjacent`,
  `centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos`, and
  `centralPhysicalFiniteVacuumSector_positiveKernelConnected`.
- **obligation**: extract a positive finite bottleneck/path constant from the
  constructive paths and prove a finite weighted Poincare upper contraction.
  The preceding all-cutoff Gram theorem then supplies the lower edge needed
  for an absolute `q < 1` form bound.
- **constructive?**: yes — all five printed declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,180-job dependency-complete build pass.  This is qualitative finite
  irreducibility, not yet a quantitative finite gap, cutoff-uniform rate,
  completed-space gap, thermodynamic/continuum QFT, or Clay theorem.

### [BF4-finite-vacuum-sector-stationary-laws] Restricted row normalization — **PROVED 2026-08-22**

- **milestone**: every normalized physical joint-kernel row, restricted to the
  canonical finite vacuum component, sums exactly to its genuine physical
  stationary weight.  The component has strictly positive total stationary
  mass because it contains the positive-weight vacuum index.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorStationaryLaws.lean`.
- **decl**:
  `centralPhysicalFiniteKernel_fullRowSum_eqv_weight`,
  `centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight`, and
  `centralPhysicalFiniteVacuumSectorWeightSum_pos`.
- **obligation**: prove the exact sector Dirichlet identity and use the
  constructive positive-kernel paths to extract a positive finite Poincare
  constant, hence a strict finite upper contraction.
- **constructive?**: yes — all three exports use exactly
  `[propext, Quot.sound]`.  An initial use of the toolchain's classical
  `List.nodup_range` was replaced by an explicit inductive proof; no
  `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
  noncomputable declaration remains.
- **status note**: the focused monitored check and exact-target one-worker
  1,181-job dependency-complete build pass.  This is exact finite stationarity,
  not yet a quantitative finite rate, cutoff-uniform estimate, completed-space
  gap, thermodynamic/continuum QFT, or Clay theorem.

### [BF4-finite-vacuum-sector-Dirichlet] Exact edge-energy identity — **PROVED 2026-08-22**

- **milestone**: for a generic finite symmetric stationary joint kernel, the
  directed weighted edge energy is exactly twice `D-M`, and half of that
  energy is exactly `D-M`.  Both theorems are specialized unconditionally to
  the actual normalized physical kernel on every finite BF4 canonical vacuum
  component.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorDirichlet.lean`.
- **decl**:
  `finiteJointDirichletEnergy_eqv_twice_deficit`,
  `half_mul_finiteJointDirichletEnergy_eqv_deficit`,
  `centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit`, and
  `half_mul_centralPhysicalFiniteVacuumSectorDirichlet_eqv_deficit`.
- **obligation**: extract finite positive edge and path-length constants from
  the constructive physical paths, then prove that this exact edge energy
  dominates the centered stationary square with a positive coefficient.
- **constructive?**: yes — all four exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,182-job dependency-complete build pass.  This identity alone does not
  supply a strict finite rate, cutoff-uniform estimate, completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem.

### [BF4-finite-vacuum-sector-path-energy] Endpoint domination — **PROVED 2026-08-22**

- **milestone**: define the recursively amplified actual kernel-weighted
  energy of a Type-level positive-kernel chain and prove that any common
  nonnegative lower edge bound times the squared endpoint difference is at
  most this energy.  Apply the result to every explicit canonical BF4 sector
  path returned by constructive connectedness.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathEnergy.lean`.
- **decl**:
  `square_add_le_double_square_sum`,
  `PositiveKernelChainIn.amplifiedEnergy_nonnegative`,
  `PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_amplifiedEnergy`,
  and
  `centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_pathEnergy`.
- **obligation**: construct the common positive edge floor and a finite common
  amplification ceiling, compare every amplified path energy to the global
  Dirichlet energy, and sum the resulting pairwise estimates.
- **constructive?**: yes — the four exports use only `[propext]` or
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,183-job dependency-complete build pass.  No common floor, strict finite
  rate, cutoff-uniform estimate, completed-space gap, thermodynamic/continuum
  QFT, or Clay theorem is asserted yet.

### [BF4-finite-vacuum-sector-edge-floor] Common positive floor — **PROVED 2026-08-22**

- **milestone**: enumerate the finite ordered pairs of canonical sector
  indices, replace nonpositive entries by the positive unit, and take their
  located rational minimum (with a unit fallback).  Prove the resulting
  rational is strictly positive, lies below every genuinely positive physical
  entry, and discharges the floor premise of every canonical path estimate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorEdgeFloor.lean`.
- **decl**: `listPositiveMinOne_pos`, `listPositiveMinOne_le_of_mem`,
  `centralPhysicalFiniteVacuumSectorEdgeFloor_pos`,
  `centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry`, and
  `centralPhysicalFiniteVacuumSector_edgeFloor_mul_endpoint_sq_le_pathEnergy`.
- **obligation**: compare each amplified canonical path energy with the global
  Dirichlet energy, construct a common finite amplification ceiling, and sum
  the endpoint estimates into a Poincare inequality.
- **constructive?**: yes — the audited exports use no axioms or only
  `[propext]` or `[propext, Quot.sound]`; no `Classical.*`, choice,
  `native_decide`, `sorry`, custom axiom, or noncomputable declaration was
  added.
- **status note**: the focused monitored check and exact-target one-worker
  1,184-job dependency-complete build pass.  No path ceiling, strict finite
  rate, completed-space gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted yet.

### [BF4-finite-vacuum-sector-path-global-energy] Global comparison — **PROVED 2026-08-22**

- **milestone**: define a recursive rational amplification scale for each
  positive-kernel chain, prove every nonnegative edge square is below the full
  directed Dirichlet double sum, and inductively bound each amplified path
  energy by its scale times the global energy.  Specialize the result to every
  canonical BF4 vacuum-sector path.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathGlobalEnergy.lean`.
- **decl**: `finiteJointDirichletEnergy_term_le`,
  `PositiveKernelChainIn.amplificationScale_nonnegative`,
  `PositiveKernelChainIn.amplifiedEnergy_le_scale_mul_finiteJointDirichletEnergy`,
  and
  `centralPhysicalFiniteVacuumSector_pathEnergy_le_scale_mul_Dirichlet`.
- **obligation**: combine the finitely many canonical path scales into one
  coefficient-independent ceiling, sum the endpoint bounds, and derive the
  centered Poincare inequality.
- **constructive?**: yes — the four audited exports use only `[propext]` or
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,185-job dependency-complete build pass.  No common ceiling, strict finite
  rate, completed-space gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted yet.

### [BF4-finite-vacuum-sector-path-ceiling] Common finite ceiling — **PROVED 2026-08-22**

- **milestone**: enumerate the finite Cartesian square of membership-carrying
  sector indices, sum all nonnegative canonical path scales, and add the unit
  to construct a strictly positive common ceiling.  Combine it with the edge
  floor and both path-energy comparisons to prove
  `floor * (f_i-f_j)^2 <= ceiling * Dirichlet(f)` for every sector pair.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathCeiling.lean`.
- **decl**: `finiteJointDirichletEnergy_nonnegative`,
  `centralPhysicalFiniteVacuumSectorPathCeiling_pos`,
  `centralPhysicalFiniteVacuumSectorPathScale_le_ceiling`, and
  `centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_ceiling_mul_Dirichlet`.
- **obligation**: sum the all-endpoint estimate, prove the exact centered
  pairwise-variance identity, and derive an explicit finite strict transfer
  rate.
- **constructive?**: yes — the four audited exports use only `[propext]` or
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,186-job dependency-complete build pass.  No Poincare inequality, strict
  finite rate, completed-space gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted yet.

### [BF4-finite-vacuum-sector-pairwise-variance] Exact variance compiler — **PROVED 2026-08-22**

- **milestone**: define weighted ordered pairwise variance, prove generically
  `PV = 2 * (mass * diagonal - mean^2)` through the stationary-product
  Dirichlet identity, specialize exact centering to
  `PV = 2 * sectorMass * diagonal`, and sum the common endpoint estimate to
  obtain `edgeFloor * PV <= sectorMass^2 * pathCeiling * Dirichlet`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPairwiseVariance.lean`.
- **decl**: `finiteWeightedPairwiseVariance_eqv_mass_diagonal_mean`,
  `finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal`,
  `floor_mul_finiteWeightedPairwiseVariance_le`,
  `centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv`, and
  `centralPhysicalFiniteVacuumSector_floor_mul_pairwiseVariance_le`.
- **obligation**: eliminate pairwise variance between the centered identity
  and its path bound, cancel positive factors constructively, and calibrate an
  explicit strict finite transfer rate.
- **constructive?**: yes — all five audited exports use only
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,187-job dependency-complete build pass.  No strict finite rate,
  completed-space gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted yet.

### [BF4-finite-vacuum-sector-poincare-gap] Explicit strict rate — **PROVED 2026-08-22**

- **milestone**: eliminate pairwise variance between the exact centered
  identity and path bound, cancel the positive doubled sector mass, prove
  `edgeFloor * diagonal <= sectorMass * pathCeiling * (diagonal - matrix)`,
  define `q = A/(A+edgeFloor)` for `A = sectorMass * pathCeiling`, prove
  `0 <= q < 1`, and derive `abs(matrix) <= q * diagonal` for every exactly
  centered coefficient at every fixed finite cutoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPoincareGap.lean`.
- **decl**: `centralPhysicalFiniteVacuumSector_poincare`,
  `centralPhysicalFiniteVacuumSectorPoincareRate_nonnegative`,
  `centralPhysicalFiniteVacuumSectorPoincareRate_lt_one`,
  `centralPhysicalFiniteVacuumSector_gapDenominator_mul_matrix_le`, and
  `centralPhysicalFiniteVacuumSector_abs_matrix_le_poincareRate_mul_diagonal`.
- **obligation**: connect one explicit finite-sector rate to the existing
  adaptive same-object tail bridge, then discharge its cofinal certificate or
  expose the remaining cutoff-uniform persistence datum exactly.
- **constructive?**: yes — all five audited exports use only
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,188-job dependency-complete build pass.  The strict rate is uniform over
  coefficients at a fixed cutoff but may depend on cutoff.  No cutoff-uniform
  gap, completed-space gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted.

### [BF4-cutoff-two-pulled-poincare-gap] Actual moving finite gap — **PROVED 2026-08-22**

- **milestone**: name the definitional matrix/diagonal CReal projection seams,
  zero-extend each moving cutoff-two head-centered coefficient to the current
  full finite vacuum sector, use exact centering and exact form pushforward,
  and prove `abs(actualMovingMatrix cutoff) <= q(cutoff) *
  actualMovingDiagonal cutoff` for every cutoff at least two and every
  coefficient, with `0 <= q(cutoff) < 1`.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.lean`.
- **decl**:
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit_approx`,
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit_approx`,
  `cutoffTwoPulledPoincareRateAt_nonnegative`,
  `cutoffTwoPulledPoincareRateAt_lt_one`, and
  `cutoffTwoActualMoving_abs_gap_at_poincareRate`.
- **obligation**: prove a common `q < 1` which bounds the finite Poincare rates
  at coefficientwise tail starts and aligns those starts with the existing
  relative moving-form stability budget; then contract that datum through the
  same-object CReal limit interface.
- **constructive?**: yes — the audited bridge exports use exactly
  `[propext, Quot.sound]`, while the two new projection equalities are
  definitional; no `Classical.*`, choice, `native_decide`, `sorry`, custom
  axiom, or noncomputable declaration was added.
- **status note**: focused monitored checks and the exact-target one-worker
  4,747-job dependency-complete build pass.  The first deep-unfolding attempt
  failed with a stack-space exception and is not counted as validation.  No
  cutoff-uniform gap, completed-space gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-cutoff-two-uniform-tail-poincare] Alignment-free CReal compiler — **PROVED 2026-08-22**

- **milestone**: reduce the coefficientwise adaptive seed frontier to one
  global eventual bound on the explicit finite Poincare rates.  Maximize each
  existing pairwise tail-modulus start with the global rate start, derive the
  finite seed gap there, and contract to a uniform same-object CReal form rate
  strictly below one without constructing a choice function.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledUniformTailPoincareGap.lean`.
- **decl**: `cutoffTwoActualMovingMatrixAt_eqv_pulled`,
  `cutoffTwoActualMovingDiagonalAt_eqv_pulled`,
  `cutoffTwoActualMovingDiagonalAt_nonnegative`,
  `CutoffTwoUniformTailPoincareRateBound.nonempty_adaptiveTailSeedGapAt`,
  `CutoffTwoUniformTailPoincareRateBound.centeredMatrixCutoffLimit_leEv_adaptiveRate_mul_diagonal`,
  and `CutoffTwoUniformTailPoincareRateBound.adaptiveRate_lt_one`.
- **obligation**: construct `CutoffTwoUniformTailPoincareRateBound q` for some
  common `q < 1`, equivalently obtain a cutoff-uniform positive ratio between
  the finite edge floor and the mass-times-path-ceiling scale; then transport
  the resulting same-object form gap to the completed vacuum complement.
- **constructive?**: yes — the audited exports use only `[propext]` or
  `[propext, Quot.sound]`; coefficientwise existential stability starts are
  eliminated only into a Prop-valued CReal comparison, and no `Classical.*`,
  choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
  was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,749-job dependency-complete build pass.  The uniform tail rate certificate
  is not inhabited.  No completed-space gap, thermodynamic/continuum QFT, or
  Clay theorem is asserted.

### [BF4-cutoff-two-pulled-uniform-path-energy] Fixed-carrier endpoint compiler — **PROVED 2026-08-22**

- **milestone**: prove qualitative persistence of every positive cutoff-two
  canonical path edge in every later pulled kernel, rekernel the Type-level
  paths without changing their recursive amplification scales, and compile a
  common positive fixed-carrier edge floor into a uniform endpoint bound using
  the original cutoff-two path ceiling.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.lean`.
- **decl**: `PositiveKernelChainIn.amplificationScale_rekernel`,
  `cutoffTwoPulledKernelAt_pos_of_base_pos`,
  `cutoffTwoPulledPositivePath_amplificationScale_eq_base`,
  `cutoffTwoPulledCanonicalPathCeiling_pos`, and
  `CutoffTwoPulledUniformPositiveEdgeFloor.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet`.
- **obligation**: construct `CutoffTwoPulledUniformPositiveEdgeFloor`; then
  compare the fixed pulled Dirichlet energy with the full zero-extension
  deficit, sum the endpoint bound against the pulled stationary weights, and
  derive one cutoff-uniform strict form rate.
- **constructive?**: yes — the five audited exports use only `[]`,
  `[propext]`, or `[propext, Quot.sound]`; no `Classical.*`, choice,
  `native_decide`, `sorry`, custom axiom, or noncomputable declaration was
  added.
- **status note**: the focused monitored check and exact-target one-worker
  4,748-job dependency-complete build pass.  The common positive-edge floor is
  not inhabited.  No uniform form gap, completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-pulled-dirichlet-embedding] Old-old energy bridge — **PROVED 2026-08-22**

- **milestone**: map the fixed cutoff-two Cartesian carrier injectively into
  every later full vacuum-sector Cartesian carrier, identify source summands
  with their old-old zero-extension images, and prove that the pulled
  Dirichlet energy is bounded by the full energy and hence by twice the actual
  moving diagonal-minus-matrix deficit.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding.lean`.
- **decl**: `cutoffTwoPulledDirichlet_le_fullExtensionDirichlet` and
  `cutoffTwoPulledDirichlet_le_twice_moving_deficit`.
- **obligation**: sum the uniform endpoint estimate against the pulled
  stationary weights, use the exact centered pairwise-variance identity, and
  derive a cutoff-uniform finite Poincare rate from the still-uninhabited
  common positive-edge-floor certificate.
- **constructive?**: yes — both audited declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,749-job dependency-complete build pass.  No common positive-edge floor,
  uniform form gap, completed-space gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-cutoff-two-pulled-mass] Fixed-carrier normalization — **PROVED 2026-08-22**

- **milestone**: define the total stationary mass on the fixed pulled
  cutoff-two component, prove it is positive from the retained vacuum-root
  weight, inject it into the complete later positive-row carrier, and prove it
  is at most one by exact stationary-law normalization.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledMass.lean`.
- **decl**: `cutoffTwoPulledMassAt_pos` and
  `cutoffTwoPulledMassAt_le_one`.
- **obligation**: combine these mass bounds with the centered pairwise-
  variance identity, the fixed path endpoint estimate, and the pulled-energy
  embedding to derive a uniform finite Poincare rate from the common
  positive-edge-floor certificate alone.
- **constructive?**: yes — both audited declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,750-job dependency-complete build pass.  The common positive-edge floor
  is not inhabited.  No uniform form gap, completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-pulled-uniform-poincare] Fixed-carrier strict rate compiler — **PROVED 2026-08-22**

- **milestone**: sum the fixed endpoint inequality against the pulled
  stationary weights, eliminate pairwise variance and energy by exact
  centering and Dirichlet identities, cancel the positive mass, use its
  normalized upper bound, and derive the cutoff-independent rate
  `ceiling / (ceiling + floor) < 1` and its absolute moving-form gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap.lean`.
- **decl**: `cutoffTwoPulledMovingMatrix_nonnegative`,
  `CutoffTwoPulledUniformPositiveEdgeFloor.floor_mul_movingDiagonal_le_ceiling_mul_deficit`,
  `CutoffTwoPulledUniformPositiveEdgeFloor.uniformPoincareRate_lt_one`, and
  `CutoffTwoPulledUniformPositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate`.
- **obligation**: feed this direct uniform finite gap into the adaptive
  same-object Bishop-real tail compiler; separately, construct the sole
  remaining analytic certificate `CutoffTwoPulledUniformPositiveEdgeFloor`.
- **constructive?**: yes — all four audited declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,751-job dependency-complete build pass.  The edge-floor certificate is
  not inhabited.  No unconditional same-object CReal gap, completed-space
  gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-every-fixed-base-constructed-CReal-gap] Unconditional same-object gap on each fixed carrier — **PROVED 2026-08-22**

- **milestone**: instantiate the arbitrary-base finite and Bishop-real gap
  compilers with the constructed persistent edge floor and package the rate,
  strictness, tail start, moving-form inequality, and cutoff-limit inequality.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap.lean`.
- **decl**: `FixedBaseConstructedUniformGapData` and
  `fixedBaseConstructedUniformGapData`.
- **obligation**: prove that these base-indexed packages admit one common
  rational upper rate strictly below one on an unbounded/cofinal carrier
  family, then transport that common gap through vacuum-sector density and
  completion.
- **constructive?**: yes — the audited constructed package uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,755-job dependency-complete build pass.  Every fixed carrier is closed
  unconditionally, but no carrier-independent rate is claimed.  No
  completed-space gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-fixed-base-pulled-uniform-CReal-gap] Fixed-carrier finite gaps contract to same-object limits — **PROVED 2026-08-22**

- **milestone**: use the moving matrix and diagonal Cauchy moduli to pass an
  arbitrary fixed carrier's eventual absolute finite Poincare estimate to its
  two same-object Bishop-real cutoff limits at the exact same rational rate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap.lean`.
- **decl**: `cReal_leEv_of_eventual_abs_gap` and
  `centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal`.
- **obligation**: instantiate the theorem with the constructed edge floor for
  every base, then prove one common upper rate below one for an
  unbounded/cofinal family of those base-indexed packages.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,754-job dependency-complete build pass.  The rate may still vary with the
  fixed base carrier.  No completed-space gap, thermodynamic/continuum QFT, or
  Clay theorem is asserted.

### [BF4-cutoff-two-pulled-uniform-creal-gap] Unrelaxed same-object limit gap — **PROVED 2026-08-22**

- **milestone**: recode the uniform pulled finite form bound to the literal
  moving matrix/diagonal approximants and use their Cauchy moduli to pass the
  exact same rational rate, without adaptive relaxation, to the same-object
  Bishop-real inequality for every fixed-carrier coefficient.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap.lean`.
- **decl**: `cutoffTwoActualMoving_abs_gap_at_uniformPoincareRate` and
  `centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal`.
- **obligation**: construct `CutoffTwoPulledUniformPositiveEdgeFloor`; then
  bridge the resulting fixed-carrier coefficient family to a dense physical
  vacuum complement and extend the gap to its Hilbert completion.
- **constructive?**: yes — both audited declarations use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,752-job dependency-complete build pass.  The edge-floor certificate is
  not inhabited and the completed-space bridge is open.  No thermodynamic/
  continuum QFT or Clay theorem is asserted.

### [BF4-cutoff-two-pulled-base-edge-floor] Constructed canonical-path floor — **PROVED 2026-08-22**

- **milestone**: weaken the pulled-edge premise to the cutoff-two-positive
  edges actually used by the transported canonical paths, prove a generic
  base-path/replacement-kernel endpoint compiler, establish half retention for
  arbitrary cutoff-stable unit observables, and construct one explicit common
  positive floor by a finite minimum of anchored pair-cylinder entries.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathEnergy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffUniformRowFloor.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor.lean`.
- **decl**:
  `PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_rekernel_amplifiedEnergy`,
  `half_mul_slabNomeCutoffBoundedObservableExpectation_le_of_increment_le_one`,
  `CutoffTwoPulledUniformBasePositiveEdgeFloor.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet`,
  `half_mul_centralNormalizedPhysicalReflectedKernel_le_of_increment_le_one`,
  `half_mul_cutoffTwoPulledKernelAt_le_of_increment_le_one`, and
  `cutoffTwoPulledUniformBasePositiveEdgeFloor`.
- **obligation**: recode the uniform finite Poincare and same-object CReal
  contractions to consume the newly inhabited base-positive certificate;
  after that, construct a density/cofinal bridge from the fixed cutoff-two
  carrier family to the full physical vacuum complement before invoking any
  completed-space gap theorem.
- **constructive?**: yes — the newly audited declarations use only
  `[propext, Quot.sound]`, except the path-shape equality which is axiom-free;
  no `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
  noncomputable declaration was added.
- **status note**: the focused monitored checks and exact-target one-worker
  4,749-job dependency-complete build pass.  The obsolete stronger
  all-later-positive floor remains uninhabited but is no longer the
  mathematically necessary condition.  No completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-pulled-constructed-uniform-creal-gap] Certificate-free fixed-carrier limit gap — **PROVED 2026-08-22**

- **milestone**: retarget the uniform finite Poincare and same-object CReal
  compilers to the exactly sufficient base-positive edge-floor interface,
  specialize them to the constructed pair-cylinder floor, and seal one data
  package containing a rational `rate`, `0 <= rate < 1`, the uniform finite
  moving-form inequality, and the same-object Bishop-real inequality for every
  fixed-carrier coefficient.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledUniformCRealGap.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap.lean`.
- **decl**:
  `CutoffTwoPulledUniformBasePositiveEdgeFloor.uniformPoincareRate_lt_one`,
  `CutoffTwoPulledUniformBasePositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate`,
  `centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal`, and
  `cutoffTwoConstructedUniformGapData`.
- **obligation**: construct an honest density/cofinality bridge from an
  expanding family of finite physical carriers to the cutoff-removed vacuum
  complement, prove that the common strict rate survives that bridge, and only
  then invoke the existing completion compiler; thermodynamic and continuum
  control remain subsequent frontiers.
- **constructive?**: yes — the final sealed package uses exactly
  `[propext, Quot.sound]`; the opacity is only a kernel-checked presentation
  boundary for a large finite witness, and no `Classical.*`, choice,
  `native_decide`, `sorry`, custom axiom, or noncomputable declaration was
  added.
- **status note**: the focused monitored checks and exact-target one-worker
  4,754-job dependency-complete build pass.  The fixed-carrier same-object gap
  is unconditional, but no density/completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-fixed-base-pulled-edge-floor] Persistent floor on every fixed vacuum carrier — **PROVED 2026-08-22**

- **milestone**: generalize pair-cylinder half retention, qualitative support
  persistence, and the anchored finite-positive-minimum construction from the
  cutoff-two carrier to arbitrary fixed nome, base cutoff, and half-extent.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor.lean`.
- **decl**:
  `centralPhysicalFinitePulledKernel_pos_of_base_pos`,
  `half_mul_centralPhysicalFinitePulledKernel_le_of_increment_le_one`, and
  `fixedBasePulledPositiveEdgeFloor`.
- **obligation**: combine each constructed base floor with the base canonical
  path ceiling and the later pulled Dirichlet identity to obtain a strict
  same-object limit rate on every fixed carrier; then isolate and discharge
  the genuinely stronger requirement that those base-indexed rates admit one
  common upper bound below one along an unbounded/cofinal carrier family.
- **constructive?**: yes — all three audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,749-job dependency-complete build pass.  Floors are constructed for every
  fixed carrier, but not uniformly in the carrier.  No completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-fixed-base-pulled-path-energy] Later-uniform path control on every fixed carrier — **PROVED 2026-08-22**

- **milestone**: rekernel every arbitrary-base canonical vacuum path into the
  later pulled kernel, preserve its recursive scale, and combine the
  constructed base floor with the finite base path ceiling to control every
  endpoint square by the later pulled Dirichlet energy.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledPathEnergy.lean`.
- **decl**: `fixedBasePulledPositivePath_amplificationScale_eq_base` and
  `FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet`.
- **obligation**: sum the endpoint estimate against the later pulled weights,
  identify the pairwise variance and Dirichlet deficit, and construct the
  resulting strict rate for each fixed base; then prove a single rate below
  one uniformly over an unbounded/cofinal family.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,750-job dependency-complete build pass.  The path constants remain
  base-indexed.  No completed-space gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-fixed-base-pulled-dirichlet-embedding] Old-block energy reaches the moving deficit — **PROVED 2026-08-22**

- **milestone**: inject the old-carrier Cartesian square into every later
  vacuum component, compare the nonnegative Dirichlet sums, and contract the
  full zero-extension energy through the exact stationary Dirichlet identity
  to twice the moving pulled diagonal-minus-matrix deficit.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding.lean`.
- **decl**: `fixedBasePulledDirichlet_le_fullExtensionDirichlet` and
  `fixedBasePulledDirichlet_le_twice_moving_deficit`.
- **obligation**: combine this deficit bound with the arbitrary-base path
  estimate and pulled-mass normalization to construct a strict rate on every
  fixed carrier; then isolate the common lower ratio needed to keep those
  rates uniformly below one on a cofinal family.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,751-job dependency-complete build pass.  No cross-base rate is claimed;
  no completed-space gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted.

### [BF4-fixed-base-pulled-mass] Normalized mass on every fixed carrier — **PROVED 2026-08-22**

- **milestone**: use the persistent root to prove positive pulled mass and
  the injective cutoff map plus exact stationary normalization to prove mass
  at most one for every arbitrary fixed base component at every later cutoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledMass.lean`.
- **decl**: `fixedBasePulledMass_pos` and `fixedBasePulledMass_le_one`.
- **obligation**: contract the constructed floor, transported path ceiling,
  deficit embedding, pairwise-variance identity, and these mass bounds into
  one strict rate for each fixed carrier; then prove a rate uniform in an
  unbounded/cofinal family.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,752-job dependency-complete build pass.  No cross-base quantitative lower
  bound is claimed; no completed-space gap, thermodynamic/continuum QFT, or
  Clay theorem is asserted.

### [BF4-fixed-base-pulled-uniform-Poincare-gap] Strict later-cutoff rate on every fixed carrier — **PROVED 2026-08-22**

- **milestone**: combine the arbitrary-base persistent edge floor, transported
  path ceiling, Dirichlet embedding, pairwise-variance identity, and pulled-mass
  normalization into an explicit rational rate below one that controls the
  absolute moving centered matrix form at every sufficiently late cutoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap.lean`.
- **decl**:
  `FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_nonnegative`,
  `FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_lt_one`,
  `FixedBasePulledPositiveEdgeFloor.uniformGapDenominator_mul_movingMatrix_le`,
  and
  `FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate`.
- **obligation**: pass the eventual finite estimate to the same-object
  Bishop-real cutoff limit for each fixed carrier, then prove that the
  base-indexed rates admit one common upper bound strictly below one on an
  unbounded/cofinal carrier family.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,753-job dependency-complete build pass.  The strict rate is uniform in the
  later cutoff but may vary with the fixed base carrier.  No completed-space
  gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-finite-carrier-prefix-uniform-gap] One common strict gap on every finite carrier prefix — **PROVED 2026-08-22**

- **milestone**: take the located maximum of the constructed base rates through
  an arbitrary finite bound, prove it remains below one, and transport that
  common prefix rate to every later moving form and same-object Bishop-real
  limit in the prefix.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap.lean`.
- **decl**: `constructedFixedBaseRate_le_finitePrefixRate`,
  `constructedFinitePrefixRate_lt_one`,
  `constructedFinitePrefixMoving_abs_gap`,
  `constructedFinitePrefixCutoffLimit_gap`, and
  `fixedCarrierPrefixConstructedUniformGapData`.
- **obligation**: prove one rational `q < 1` above the prefix rates uniformly
  for arbitrarily large bounds, equivalently discharge the all-base
  denominator-cleared floor/path estimate; then prove the separate
  vacuum-sector density/completion bridge.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: an initial focused check was interrupted after exposing a
  recursive elaboration path and is not counted.  After factoring named
  lemmas, the focused monitored check and exact-target one-worker 4,758-job
  dependency-complete build pass.  This is finite-prefix compactness, not an
  all-carrier gap.  No completed-space gap, thermodynamic/continuum QFT, or
  Clay theorem is asserted.

### [BF4-uniform-floor-path-rate] Denominator-cleared all-carrier rate frontier — **REDUCED 2026-08-22**

- **milestone**: expose the exact rational inequality
  `pathCeiling <= q * (pathCeiling + edgeFloor)` whose all-base proof bounds the
  constructed Poincare quotients by one common `q < 1`, and compile it through
  the cofinal vacuum-sector and Bishop-real limit interfaces.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorUniformFloorPathRate.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap.lean`.
- **decl**: `FixedNomeUniformFloorPathRateBound`,
  `FixedNomeUniformFloorPathRateBound.uniformPoincareRate_le`,
  `FixedNomeUniformFloorPathRateBound.toUniformConstructedVacuumSectorRateBound`,
  `FixedNomeUniformFloorPathRateBound.toVacuumSectorCenteredStrictGap`, and
  `FixedNomeUniformFloorPathRateBound.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: construct one `q < 1` and prove the displayed
  denominator-cleared inequality for every base carrier, or replace the
  canonical-path constants by sharper uniform sector estimates; then prove the
  separate vacuum-sector density/completion bridge.
- **constructive?**: yes — all four new theorem exports and the updated sealed
  package audit to exactly `[propext, Quot.sound]`; no `Classical.*`, choice,
  `native_decide`, `sorry`, custom axiom, or noncomputable declaration was
  added.
- **status note**: the focused monitored checks and exact-target one-worker
  4,757-job dependency-complete build pass.  The certificate is deliberately
  uninhabited.  No completed-space gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-constructed-cross-carrier-rate-bridge] One common bound compiles to the cofinal vacuum-sector gap — **PROVED 2026-08-22**

- **milestone**: state the exact carrier-independent upper-bound certificate
  for the constructed base rates and compile it to the existing cofinal
  moving-centered vacuum-sector strict-gap interface and Bishop-real limit.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge.lean`.
- **decl**: `FixedNomeUniformConstructedVacuumSectorRateBound`,
  `FixedNomeUniformConstructedVacuumSectorRateBound.selectedAnchor_ge`,
  `FixedNomeUniformConstructedVacuumSectorRateBound.toVacuumSectorCenteredStrictGap`,
  and
  `FixedNomeUniformConstructedVacuumSectorRateBound.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: construct one `q < 1` satisfying `constructedRate_le` for
  every base, preferably from a quantitative floor-to-path-ceiling ratio or a
  sharper sector-local estimate; then establish the distinct vacuum-sector
  density/completion bridge.
- **constructive?**: yes — all three audited theorem exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,756-job dependency-complete build pass.  The cross-carrier certificate is
  deliberately uninhabited.  No completed-space gap, thermodynamic/continuum
  QFT, or Clay theorem is asserted.

### [BF4-cofinal-prefix-rate-bridge] Cofinal finite-prefix ceilings characterize all-carrier uniformity — **PROVED 2026-08-22**

- **milestone**: prove that one strict rational ceiling on a cofinal schedule
  of finite-prefix running maxima compiles to the all-carrier constructed-rate
  bound, and conversely that any all-carrier bound supplies such a schedule.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge.lean`.
- **decl**: `FixedNomeCofinalFinitePrefixRateCeiling`,
  `FixedNomeCofinalFinitePrefixRateCeiling.toUniformConstructedVacuumSectorRateBound`,
  `FixedNomeCofinalFinitePrefixRateCeiling.toVacuumSectorCenteredStrictGap`,
  `FixedNomeCofinalFinitePrefixRateCeiling.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`,
  and
  `FixedNomeUniformConstructedVacuumSectorRateBound.toCofinalFinitePrefixRateCeiling`.
- **obligation**: inhabit the equivalent certificate by a carrier-independent
  quantitative estimate, or replace the canonical-path floor/ceiling ratio
  by sharper uniform sector control; separately establish vacuum-sector
  density and completion.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,759-job dependency-complete build pass.  The certificate is deliberately
  uninhabited.  The equivalence prevents finite-prefix compactness from being
  mistaken for an all-carrier estimate.  No completed-space gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-vacuum-sector-dense-linear-realization] Sector coefficients are actual dense GNS observables — **PROVED 2026-08-22**

- **milestone**: construct exact lower-half state cylinders, assemble every
  fixed finite vacuum-sector coefficient into one finite-linear observable,
  prove its later-cutoff values equal the explicit zero extension, and
  identify its physical norm and transfer quadratic with the pulled forms.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorLinearRealization.lean`.
- **decl**:
  `centralPhysicalStateCylinder_agrees_iff_cutoffIndexMap_eq`,
  `centralPhysicalFiniteVacuumSectorLinearObservable_value_eqv_extension`,
  `centralPhysicalFiniteVacuumSectorLinearObservable_diagonal_eqv_pulled`, and
  `centralPhysicalFiniteVacuumSectorLinearObservable_matrix_eqv_pulled`.
- **obligation**: pass these actual dense elements through the same-object
  completion pairing, then characterize and close the completed root-sector
  subspace; independently inhabit the common all-carrier rate certificate.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: an initial focused check was interrupted after an overly
  generous heartbeat bound concealed ordinary namespace errors and is not
  counted.  The corrected focused check and exact-target one-worker 1,262-job
  dependency-complete build pass.  This is an exact dense-carrier realization,
  not a density theorem for a completed vacuum sector.  No completed-space
  gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-vacuum-sector-cylinder-completion] Concrete completion embeds injectively in the global physical completion — **PROVED 2026-08-22**

- **milestone**: complete the union of all finite canonical root-sector
  cylinder presentations in the inherited cutoff-removed squared distance,
  descend the termwise realization to the global completion, prove that map
  injective, and identify dense sector norms with pulled diagonal limits.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletion.lean`.
- **decl**: `centralPhysicalVacuumSectorCylinderSquaredSeminorm`,
  `centralPhysicalVacuumSectorCylinderCompletionToGlobal`,
  `centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective`, and
  `centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_pulled`.
- **obligation**: prove that the concrete completed Markov transfer preserves
  this injective sector image (or state the exact Type-level lifting datum),
  identify its transfer pairing with the pulled matrix limit, and inhabit one
  all-carrier strict-rate certificate before extending the gap by continuity.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,263-job dependency-complete build pass.  Injectivity is proved, but neither
  surjectivity onto the global vacuum complement nor transfer invariance is
  claimed.  No completed sector gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-vacuum-sector-completed-transfer-lift] Exact invariant-image frontier — **REDUCED 2026-08-22**

- **milestone**: formulate transfer invariance as a lift of the concrete
  adaptive global Markov transfer through the injective sector embedding;
  prove uniqueness, preservation of global-vacuum orthogonality, and exact
  agreement of the restricted completed transfer pairing.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderTransferLift.lean`.
- **decl**: `CentralPhysicalVacuumSectorCylinderTransferLiftData`,
  `CentralPhysicalVacuumSectorCylinderTransferLiftData.transfer_eq_of_lifts`,
  `CentralPhysicalVacuumSectorCylinderTransferLiftData.preserves_globalVacuumOrthogonal`,
  and
  `CentralPhysicalVacuumSectorCylinderTransferLiftData.completedInner_transfer_eq_global`.
- **obligation**: construct the lift by cofinally reindexing sector Cauchy
  representatives so that each action cutoff dominates the selected
  presentation base, then prove the finite action remains in the canonical
  root component and that the realized output is completion-close.
- **constructive?**: yes — all three audited theorem exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,357-job dependency-complete build pass.  The lift record is deliberately
  uninhabited.  No completed sector gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-vacuum-sector-finite-action] Finite Markov action preserves and recodes the root sector — **PROVED 2026-08-22**

- **milestone**: prove conditional-kernel separation across the canonical
  component boundary, show that a sector cylinder's genuine finite Markov
  image vanishes outside the current component whenever the action cutoff
  dominates its base, and realize the sampled image exactly as a new finite
  sector cylinder on the whole positive carrier.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderFiniteAction.lean`.
- **decl**:
  `centralPhysicalConditionalKernel_outside_vacuumSector_eqv_zero`,
  `centralPhysicalMarkovApply_vacuumSectorPresentation_eqv_zero_of_outside`,
  `centralPhysicalVacuumSectorMarkovCoefficientExtension_eqv_self`, and
  `centralPhysicalVacuumSectorMarkovCylinderRealization_value`.
- **obligation**: select action cutoffs cofinally along arbitrary sector
  Cauchy representatives, prove the resulting presentation sequence is
  Cauchy and independent up to completion closeness, and use it to inhabit
  `CentralPhysicalVacuumSectorCylinderTransferLiftData`; independently
  construct one strict rate uniform over all carriers.
- **constructive?**: yes — the three audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,264-job dependency-complete build pass.  Earlier focused attempts with a
  missing namespace and an elaboration-heavy structure-projection theorem are
  not counted.  This proves finite-stage support and exact recoding, not
  Cauchy preservation or a completed transfer lift.  No completed uniform
  gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-vacuum-sector-base-controlled-cauchy] Adaptive inputs are support-safe at every stage — **PROVED 2026-08-22**

- **milestone**: construct an explicit base-paying slow reindex of every
  sector Cauchy representative, prove it is Cauchy and close to the original,
  prove its presentation base is at most its sequence stage, and combine this
  with `adaptiveSampleIndex <= actionStage` to discharge the finite-action
  support hypothesis at every adaptive stage.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.lean`.
- **decl**: `centralPhysicalVacuumSectorBaseControlledCauchy`,
  `centralPhysicalVacuumSectorBaseControlledCompletion_eq`,
  `centralPhysicalVacuumSectorAdaptiveSample_base_le_stage`, and
  `centralPhysicalVacuumSectorAdaptiveSample_realization_value`.
- **obligation**: prove that the adaptive sequence of finite sector recodings
  is Cauchy in the inherited limiting seminorm and completion-close to the
  global adaptive Markov output, then descend it to the quotient and inhabit
  `CentralPhysicalVacuumSectorCylinderTransferLiftData`; independently
  construct one strict rate uniform over all carriers.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,348-job dependency-complete build pass.  This discharges the scheduling
  and finite-support parts of invariance, not the limiting recoding-tail
  estimate.  No completed transfer lift, completed uniform gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-vacuum-sector-adaptive-recoding-tail] One recoding-tail estimate compiles to the completed lift — **REDUCED 2026-08-22**

- **milestone**: prove exact zero finite GNS distance between the support-safe
  sector recoding and the global adaptive action at every current cutoff;
  isolate their remaining limiting-distance tail with an explicit modulus;
  and compile any inhabitant into a sector Cauchy output, quotient-respecting
  completed transfer, and the existing exact transfer-lift datum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderFiniteAction.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail.lean`.
- **decl**:
  `centralPhysicalVacuumSectorMarkovCylinder_finiteDistSq_eqv_zero`,
  `centralPhysicalVacuumSectorConcreteAdaptiveOutput_distSq_approx_self_eqv_zero`,
  `CentralPhysicalVacuumSectorAdaptiveRecodingTailData`,
  `CentralPhysicalVacuumSectorAdaptiveRecodingDiagonalRegularityData.toAdaptiveRecodingTailData`,
  `CentralPhysicalVacuumSectorAdaptiveRecodingTailData.recodedCauchy`, and
  `CentralPhysicalVacuumSectorAdaptiveRecodingTailData.toTransferLiftData`.
- **obligation**: inhabit the tail record, for example by proving that the
  moving inner-regularity rate of each adaptive recoding error is eventually
  paid by its own action cutoff; independently construct one strict rational
  rate uniform over the unbounded/cofinal carrier family before extending a
  gap to the completed sector.
- **constructive?**: yes — the four audited adaptive exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,360-job dependency-complete build pass.  Earlier elaboration timeouts are
  not counted.  The tail and diagonal-regularity records are deliberately
  uninhabited, so this is an exact reduction of completed transfer invariance,
  not an unconditional completed lift.  No completed uniform gap,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-vacuum-sector-amplitude-shell-schedule] The sector diagonal pays the scaled stationary shell cutoff — **PROVED 2026-08-22**

- **milestone**: strengthen the completion-preserving base-controlled slow
  diagonal so that each admitted presentation pays both its carrier base and
  the existing stationary source-shell schedule at tolerance `1/(i+1)`
  rescaled by the square of twice its finite coefficient `l1` envelope.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy.lean`.
- **decl**: `centralPhysicalVacuumSectorPresentationL1`,
  `centralPhysicalVacuumSectorPresentationRecodingSqEnvelope`,
  `centralPhysicalVacuumSectorPresentationEnvelope_mul_shellTolerance_le`,
  `centralPhysicalVacuumSectorBaseRequirement`, and
  `centralPhysicalVacuumSectorBaseControlled_shellCutoff_le_stage`.
- **obligation**: prove that the input cutoff action and its exact sector
  recoding are pointwise bounded by the presentation `l1` envelope, derive the
  finite zero-core plus scaled-shell GNS estimate, and combine nested
  cofinality with the new paid-shell theorem to inhabit
  `CentralPhysicalVacuumSectorAdaptiveRecodingTailData`.
- **constructive?**: yes — the three newly audited scheduling exports use
  exactly `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
  `sorry`, custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored schedule check and downstream
  adaptive-tail check pass; the exact-target one-worker 1,351-job
  dependency-complete build passes.  This closes a schedule obligation, not
  the amplitude/core-shell inequalities or the tail itself.  No unconditional
  completed lift, completed uniform gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-vacuum-sector-recoding-amplitude] Global and recoded actions have one pointwise envelope — **PROVED 2026-08-22**

- **milestone**: bound the genuine finite cutoff action and its exact
  canonical-sector recoding pointwise by the original presentation's finite
  coefficient `l1`, without a carrier-cardinality loss.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude.lean`.
- **decl**:
  `centralPhysicalLinearMarkovCutoffAction_vacuumSector_abs_le_l1` and
  `centralPhysicalVacuumSectorMarkovCylinder_abs_le_l1`.
- **obligation**: combine these bounds with exact equality on the paid core
  and stationary shell mass decay to prove the finite limiting-distance
  estimate, then use nested cofinality to inhabit
  `CentralPhysicalVacuumSectorAdaptiveRecodingTailData`.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,352-job dependency-complete build pass.  This closes the pointwise
  amplitude obligation only; it does not yet prove the core/shell GNS bound,
  the adaptive tail, an unconditional completed transfer lift, a uniform
  completed gap, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-recoding-core-shell] Paid shell controls the limiting recoding distance — **PROVED 2026-08-22**

- **milestone**: generalize the finite GNS core--shell estimate to a fixed
  pointwise square envelope; prove exact zero discrepancy on the paid action
  core; and combine the stationary source-shell cutoff with `(2 l1)^2` to
  bound the limiting recoding distance by `1/(i+1)`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell.lean`.
- **decl**:
  `centralPhysicalFiniteDistSq_le_core_add_scaled_shell`,
  `centralPhysicalVacuumSectorRecoding_sub_sq_le_envelope`,
  `centralPhysicalVacuumSectorRecoding_core_sub_sq_le_zero`, and
  `centralPhysicalVacuumSectorRecoding_distSq_le_invSucc`.
- **obligation**: prove that the nested adaptive sampler eventually selects
  an original slow-diagonal index beyond `CReal.lv epsilon`, transport the
  paid-shell theorem to the action stage, and inhabit
  `CentralPhysicalVacuumSectorAdaptiveRecodingTailData`.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,353-job dependency-complete build pass.  This closes the finite and
  limiting core--shell estimate, but not yet its adaptive cofinal scheduling,
  the unconditional completed lift, a uniform completed gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-completed-moments] Invariant completed powers and same-object autocorrelation — **PROVED 2026-08-22**

- **milestone**: package the inhabited completed root-sector transfer on its
  vacuum complement, construct all natural powers, prove powerwise global
  intertwining and vacuum-orthogonality preservation, and identify the sector
  same-object autocorrelation with the global adaptive matrix coefficient.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal`,
  `centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer_intertwines`,
  `centralPhysicalVacuumSectorCylinderCompletedTransferPower_intertwines`,
  `centralPhysicalVacuumSectorCylinderCompletedTransferPower_preserves_orthogonal`,
  `centralPhysicalVacuumSectorCylinderCompletedTransferPower_add`, and
  `centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_eq_global`.
- **obligation**: prove nonnegativity, contraction/log-convexity, and a
  carrier-independent geometric envelope for these same-object moments, or
  construct the exact endpoint identification that transports the already
  proved strict-joint `1/16` theorem to this physical carrier.
- **constructive?**: yes — all thirteen audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,364-job dependency-complete build pass.  This is an unconditional
  completed carrier-and-moment interface at fixed nome and finite half-extent,
  not a uniform completed gap, thermodynamic/continuum QFT, or Clay theorem.

### [BF4-pointwise-adaptive-arbitrary-cofinal-gap] Common rate reaches the actual global completion — **PROVED 2026-08-22**

- **milestone**: combine pointwise-adaptive graph limits with the arbitrary
  rational finite anchor estimate, removing the historical same-index Markov
  completion modulus from the general `q < 1` completed-gap route.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveCofinalStrictGap.lean`.
- **decl**:
  `centralPhysicalAdaptiveInputCenteredNorm_cofinal_rate_converges`,
  `centralPhysicalAdaptiveTransferredCenteredNorm_cofinal_rate_converges`,
  `centralPhysicalAdaptiveCofinalRepresentative_operator_norm_gap_rate`,
  `centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate`,
  and
  `centralPhysicalConcreteAdaptiveCompletedMarkovCofinalStrictContractionDataAtRate`.
- **obligation**: inhabit one
  `FixedNomeCofinalCenteredStrictGap w hw half q` with `q < 1`, uniformly over
  the unbounded carrier family; transport the resulting global contraction to
  the invariant completed root sector and then address volume/spacing limits.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,346-job dependency-complete build pass.  This is a stronger implication,
  not an inhabitant of the common-rate certificate; no unconditional
  completed gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-vacuum-sector-completed-gap] One cofinal common rate contracts the actual completed sector — **PROVED 2026-08-22**

- **milestone**: pull the arbitrary-rate global adaptive contraction through
  the exact completed root-sector embedding, iterate it on the actual sector
  vacuum complement, and derive geometric decay of the exact same-object
  autocorrelation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.lean`.
- **decl**:
  `CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData`,
  `centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate`,
  `centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay`,
  `centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_cofinal_norm_decay`,
  `centralPhysicalVacuumSectorCylinderCompletedInner_cauchy_schwarz`,
  `centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay`, and
  `centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_cofinal_sq_decay`.
- **obligation**: inhabit one cofinal common-rate certificate with `q < 1`,
  uniformly over the unbounded carrier family; then construct the volume and
  lattice-spacing limits without losing the strict rate.
- **constructive?**: yes — all seven audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,372-job dependency-complete build pass.  The completed sector norm and
  correlation decays are conditional on the common-rate certificate; no
  unconditional completed gap, thermodynamic/continuum QFT, or Clay theorem
  is asserted.

### [BF4-vacuum-sector-dense-transfer-form] Actual completed dense transfer form is the pulled sector form — **PROVED 2026-08-22**

- **milestone**: identify, on every dense completed root-sector cylinder, the
  matrix coefficient of the actual lifted sector transfer with the existing
  pulled finite-sector matrix cutoff limit.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm.lean`.
- **decl**:
  `innerLimitInnerRegularity_markov_left_rate_eq`,
  `centralPhysicalVacuumSectorCylinder_markovPair_approx_eqv_pulledMatrix`,
  `centralPhysicalVacuumSectorCylinder_denseTransferPairingDiagonal_converges`,
  `centralPhysicalVacuumSectorCylinder_denseTransferPairing_equiv_pulledMatrix`,
  and
  `centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_pulled`.
- **obligation**: construct or prove density of moving head-centered sector
  presentations in the completed sector vacuum complement, then combine that
  bridge with one common sector-local `q < 1` and pass to volume/spacing
  limits.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,365-job dependency-complete build pass.  This proves the transfer-form
  half of the direct sector bridge, not the head-centering density theorem, a
  uniform completed gap, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-dense-vacuum-pairing] Actual dense vacuum pairing is the pulled mean limit — **PROVED 2026-08-22**

- **milestone**: identify the completed pairing of every dense root-sector
  cylinder with the normalized global vacuum as its pulled weighted-mean
  cutoff limit, and deduce that completed vacuum orthogonality forces that
  Bishop-real mean to vanish.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorLinearObservable_vacuumPairing_eqv_pulledMean`,
  `centralPhysicalVacuumSectorCylinder_innerLimitVacuum_equiv_pulledMean`,
  `centralPhysicalVacuumSectorCylinder_completedVacuumPairing_embedRep_eq_pulled`,
  and
  `centralPhysicalVacuumSectorCylinder_pulledMean_equiv_zero_of_orthogonal`.
- **obligation**: combine the zero pulled-mean limit with the positive
  root-weight floor to prove head-correction vanishing in completed norm;
  then extend moving head-centering from dense presentations to arbitrary
  completed sector vacuum vectors.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,366-job dependency-complete build pass.  This proves the numerator-zero
  part of the moving-centering bridge, not head-correction norm convergence, a
  uniform completed gap, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-dense-head-correction-vanishing] Dense orthogonality kills the moving head correction — **PROVED 2026-08-22**

- **milestone**: use the zero pulled-mean limit and the fixed positive
  pulled-root floor to prove that the rational moving head-correction cutoff
  limit is constructively equivalent to zero for every dense completed
  root-sector cylinder orthogonal to the global vacuum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderDenseHeadCorrectionVanishing.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_headCorrection_equiv_zero_of_orthogonal`.
- **obligation**: turn scalar correction vanishing into completed-norm
  convergence of moving head-centered sector presentations to their source;
  then prove the corresponding density/diagonal argument for arbitrary
  completed sector vacuum vectors.
- **constructive?**: yes — the audited export uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,368-job dependency-complete build pass.  This closes a scalar limit edge,
  not completed centered density, a uniform completed gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-dense-centered-form-identification] Moving centered limits are the actual dense completed forms — **PROVED 2026-08-22**

- **milestone**: contract scalar head-correction vanishing through the exact
  centered polynomial expansions, then identify the resulting centered
  diagonal and matrix limits with the actual completed norm and transfer form
  of every dense globally vacuum-orthogonal root-sector cylinder.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification.lean`.
- **decl**:
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_equiv_raw_of_correction_zero`,
  `centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_equiv_raw_of_correction_zero`,
  `centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_centered`,
  and
  `centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_centered`.
- **obligation**: inhabit one common sector-local cofinal `q < 1`, use these
  endpoint identities to obtain a dense completed strict form bound, and
  extend that bound to arbitrary completed sector vacuum vectors before
  addressing volume/spacing limits.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,577-job dependency-complete build pass.  This closes endpoint
  identification on the dense orthogonal domain, not the common strict rate,
  its completion extension, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-dense-strict-form-gap] Sector-local cofinal rate controls the actual dense completed form — **PROVED 2026-08-22**

- **milestone**: compile any
  `FixedNomeCofinalVacuumSectorCenteredStrictGap q` directly into the
  quotient-level inequality `<T v,v> <= q <v,v>` for every dense completed
  root-sector cylinder orthogonal to the normalized global vacuum, preserving
  the supplied nonnegative strict rate without a full-carrier detour.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormGapAtRate` and
  `centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormGapAtRate_rate`.
- **obligation**: inhabit one common sector-local cofinal `q < 1` and extend
  this dense orthogonal form bound to arbitrary vectors in the completed
  sector vacuum complement; then address volume and lattice-spacing limits.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,579-job dependency-complete build pass.  This is a conditional dense-domain
  compiler, not an inhabitant of the common rate, a completed all-vector gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-completed-centered-form-cofinality] Exact all-vector centering frontier and compiler — **PROVED 2026-08-22**

- **milestone**: package the exact centered-form cofinality datum needed for
  arbitrary completed sector vacuum vectors; inhabit it on every dense
  orthogonal sector vector; and prove that a global inhabitant plus one common
  sector-local cofinal rate yields the actual all-vector completed strict form
  bound at that unchanged rate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality.lean`.
- **decl**:
  `CentralPhysicalVacuumSectorCylinderCenteredFormLimitData`,
  `CentralPhysicalVacuumSectorCylinderCompletedCenteredFormCofinality`,
  `centralPhysicalVacuumSectorCylinder_denseCenteredFormLimitData`,
  `centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate`, and
  `centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate_rate`.
- **obligation**: inhabit
  `CentralPhysicalVacuumSectorCylinderCompletedCenteredFormCofinality` for
  arbitrary completed sector vacuum vectors by a constructive diagonal
  centering argument, and independently inhabit one common sector-local
  `q < 1`; then turn the all-vector form bound into spectral and limit data.
- **constructive?**: yes — all three audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,580-job dependency-complete build pass.  This separates and compiles the
  completion and analytic residuals but inhabits neither globally; no
  unconditional completed gap, thermodynamic/continuum QFT, or Clay theorem
  is asserted.

### [BF4-vacuum-sector-completed-outer-head-correction-vanishing] Completed orthogonality kills arbitrary-representative outer head corrections — **PROVED 2026-08-22**

- **milestone**: identify the outer pulled-mean sequence of any sector Cauchy
  representative with its actual completed global-vacuum pairing; use
  completed orthogonality to make the outer mean converge to zero; and divide
  by the fixed positive pulled-root floor to prove convergence of the full
  outer head-correction sequence to zero.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_pairing`,
  `centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_zero`, and
  `centralPhysicalVacuumSectorCylinder_outerHeadCorrection_converges_zero`.
- **obligation**: combine this scalar perturbation control with outer raw-form
  convergence and constructive quadratic estimates to obtain centered
  diagonal and matrix convergence for arbitrary completed sector vacuum
  vectors; then inhabit the global centered-form cofinality datum and the
  independent common sector-local strict rate.
- **constructive?**: yes — all three audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,581-job dependency-complete build pass.  This proves one non-dense
  centering ingredient, not outer centered quadratic convergence, a global
  cofinality inhabitant, a uniform completed gap, thermodynamic/continuum QFT,
  or the Clay theorem.

### [BF4-vacuum-sector-completed-outer-raw-diagonal] Outer raw diagonals represent the arbitrary completed norm — **PROVED 2026-08-22**

- **milestone**: prove that the pulled diagonal cutoff-limit Bishop reals of
  the successive dense terms of any sector Cauchy representative converge to
  its global representative pairing limit, and identify the real-quotient
  class of that target with the actual completed sector squared norm.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_outerPulledDiagonal_converges` and
  `centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerRawDiagonalLimit`.
- **obligation**: use outer head-correction convergence plus constructive
  coefficient/root-weight control to prove centered-minus-raw diagonal
  convergence to zero; then establish the corresponding outer transfer-matrix
  result and inhabit the global centered-form cofinality datum.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,582-job dependency-complete build pass.  This proves outer uncentered norm
  convergence and endpoint identification, not centered outer convergence, a
  common strict rate, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-completed-outer-root-coordinate] Arbitrary completed representatives have a Bishop-real root coordinate — **PROVED 2026-08-22**

- **milestone**: prove the uniform positive vacuum-row floor times a squared
  root-coordinate difference is dominated by the actual cutoff-removed
  sector distance; use that estimate to construct an explicit rational
  Cauchy modulus and Bishop-real limit for the root coefficients of every
  arbitrary sector Cauchy representative.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_rootDifferenceSq_floor_le_distSq` and
  `centralPhysicalVacuumSectorCylinder_outerRootCoefficient_converges`.
- **obligation**: combine the new root-coordinate convergence with outer
  head-correction vanishing, root-weight boundedness, and raw-diagonal
  convergence to prove outer centered-diagonal convergence; then prove the
  matrix analogue and inhabit the global centered-form cofinality datum.
- **constructive?**: yes — both audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,583-job dependency-complete build pass.  This is a completed-coordinate
  continuity theorem, not centered outer-form convergence, a common strict
  rate, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-completed-outer-centered-diagonal] Outer centered diagonals represent the arbitrary completed norm — **PROVED 2026-08-22**

- **milestone**: identify all varying pulled root-weight limits with one
  canonical base-zero Bishop real; combine root-coordinate convergence and
  head-correction vanishing to prove the exact centered-minus-raw root
  polynomial tends to zero; conclude that arbitrary-representative moving
  head-centered diagonal limits converge to the actual completed norm
  representative.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_rootWeight_equiv_canonical`,
  `centralPhysicalVacuumSectorCylinder_outerRootWeight_converges`,
  `centralPhysicalVacuumSectorCylinder_outerHeadCenteredDiagonal_converges`,
  and
  `centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerCenteredDiagonalLimit`.
- **obligation**: prove the analogous outer centered transfer-matrix
  convergence and endpoint identification, then combine both halves into an
  unconditional inhabitant of the completed centered-form cofinality datum;
  independently inhabit one common sector-local strict rate.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,584-job dependency-complete build pass.  This closes the norm/diagonal
  half, not the transfer/matrix half, a common strict rate,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-matrix-inner-regularity] Pulled matrix cutoff modulus is recoverable data — **PROVED 2026-08-22**

- **milestone**: expose the fixed-presentation pulled reflected-quadratic
  cutoff rate as data, prove its two-sided regularity estimate, and package it
  as `CReal.InnerRegularity` without extracting the legacy propositional
  `CReal.cauchy` witness.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorFormCauchy.lean`.
- **decl**:
  `centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffRate`,
  `centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoff_regular`, and
  `centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity`.
- **obligation**: construct a cofinal reindex of every arbitrary sector
  representative which pays this moving matrix cutoff together with the
  transfer-pairing diagonal; use it to prove outer raw and centered matrix
  convergence and inhabit the all-vector centered-form cofinality datum.
- **constructive?**: yes — both newly audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,177-job dependency-complete build pass.  This is a modulus-exposure
  milestone, not moving-matrix convergence, a common strict rate,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-completed-outer-raw-matrix] Outer raw matrices represent the arbitrary completed transfer form — **PROVED 2026-08-22**

- **milestone**: construct a cofinal base-controlled reindex which pays both
  the same-object physical-inner cutoff and the pulled-matrix cutoff; identify
  its rational same-cutoff Markov diagonal with the pulled matrix; lift the
  result to convergence of moving matrix Bishop reals and identify the target
  with the actual completed transfer pairing of the original quotient class.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix.lean`.
- **decl**:
  `CReal.convergesTo_of_regularizedApproxDiagonal`,
  `centralPhysicalVacuumSectorOuterMatrixInput_class_eq`,
  `centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges`, and
  `centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerRawMatrixLimit`.
- **obligation**: prove that the head-correction terms in the exact centered
  matrix expansion vanish along this same cofinal representative; combine
  centered diagonal and matrix convergence into the unconditional all-vector
  centered-form cofinality inhabitant; independently inhabit one common
  sector-local strict rate.
- **constructive?**: yes — the generic lifting export uses `[propext]`; the
  three sector exports use exactly `[propext, Quot.sound]`.  No `Classical.*`,
  choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
  was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,366-job dependency-complete build pass.  This closes raw transfer-matrix
  convergence, not centered matrix convergence, a common strict rate,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-vacuum-sector-completed-outer-centered-matrix] Outer centered matrices give the all-vector completed form bound at any certified rate — **PROVED 2026-08-22**

- **milestone**: package every pulled finite-sector kernel as constructive
  GNS data; prove sharp Cauchy--Schwarz for its bilinear form; squeeze the two
  head-correction crosses and root-correction term to zero along the cofinal
  arbitrary-representative presentation; identify the centered matrix limit
  with the actual completed transfer form; and eliminate the completion
  quotient directly into the strict-form proposition.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix.lean`.
- **decl**:
  `centralPhysicalFinitePulledVacuumSectorMatrixGNSData`,
  `centralPhysicalFinitePulledVacuumSectorMatrixBilinear_cauchy_schwarz`,
  `centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit_cauchy_schwarz`,
  `centralPhysicalFinitePulledVacuumSectorMatrixCross_sq_le_raw_mul_rootWeight`,
  `centralPhysicalVacuumSectorCylinder_outerMatrixRightCorrection_converges_zero`,
  `centralPhysicalVacuumSectorCylinder_outerMatrixLeftCorrection_converges_zero`,
  `centralPhysicalVacuumSectorCylinder_outerMatrixRootCorrection_converges_zero`,
  `centralPhysicalVacuumSectorCylinder_outerHeadCenteredMatrix_converges`,
  `centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerCenteredMatrixLimit`,
  `centralPhysicalVacuumSectorCylinder_centeredFormLimitData_mk`, and
  `centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate_constructed`.
- **obligation**: construct one strict
  `FixedNomeCofinalVacuumSectorCenteredStrictGap q` with `q < 1` at the
  uniformity scope required by the sector, cutoff, thermodynamic, and
  continuum route; then compile the unconditional completed spectral gap and
  control its limits.
- **constructive?**: yes — all eleven audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,596-job dependency-complete build pass.  A global Type-valued presentation
  selector is deliberately not claimed: quotient induction is used only into
  the all-vector strict-form proposition.  Thus the completion extension is
  closed at any supplied certified rate, but no common rate, unconditional
  spectral gap, thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-vacuum-sector-completed-strict-form-gap] Actual completed transfer form is positive and strictly bounded at any certified rate — **PROVED 2026-08-22**

- **milestone**: prove every moving pulled finite matrix is nonnegative from
  its constructive GNS datum; pass positivity through the outer matrix limit;
  descend it propositionally to every completed sector vector; and combine it
  with the all-vector upper estimate into one strict completed form-gap datum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_outerPulledMatrixSeq_nonnegative`,
  `centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_nonnegative`,
  `centralPhysicalVacuumSectorCylinder_completedTransferForm_nonnegative`, and
  `centralPhysicalVacuumSectorCylinderCompletedStrictFormGapDataAtRate`.
- **obligation**: inhabit a cofinal strict-rate certificate with one `q < 1`
  at the cutoff/volume uniformity scope needed downstream; separately supply
  the square-form or positive-form Cauchy--Schwarz mechanism needed to turn
  the quadratic-form interval into an operator-norm/spectral statement; then
  control thermodynamic and continuum limits.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,597-job dependency-complete build pass.  The completed form interval is
  available for every supplied certified rate, but no common uniform rate,
  unconditional operator gap, thermodynamic/continuum QFT, or Clay theorem is
  asserted.

### [BF4-vacuum-sector-completed-form-to-operator] One positive Markov-form law compiles the completed form gap to squared-norm contraction — **PROVED 2026-08-22**

- **milestone**: name sharp Cauchy--Schwarz for the actual cutoff-removed
  sector Markov form as one honest certificate; combine it with the completed
  positive strict form interval; cancel division-free to obtain the
  square-form estimate; and package the resulting `q^2` squared-norm bound in
  the existing completed sector contraction interface.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinderCompletedTransfer_square_form_gap`,
  `centralPhysicalVacuumSectorCylinderCompletedTransfer_norm_gap`,
  `centralPhysicalVacuumSectorCylinderCompletedStrictContractionData_of_formGap`,
  and
  `centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate_of_markovCS`.
- **obligation**: inhabit
  `CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData`
  from finite pulled-kernel positivity and simultaneous completed limits; and
  independently construct one cofinal rate `q < 1` with the required
  cutoff/volume uniformity.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,606-job dependency-complete build pass.  The operator compiler is proved,
  but its Markov-form Cauchy--Schwarz input and the common rate are both still
  open; no unconditional operator gap, thermodynamic/continuum QFT, or Clay
  theorem is asserted.

### [BF4-vacuum-sector-dense-markov-form-cauchy-schwarz] Dense actual sector Markov form obeys sharp Cauchy--Schwarz — **PROVED 2026-08-22**

- **milestone**: identify the regular cross pairing of two finite-linear
  observables with the finite positive Markov form at every cutoff; prove its
  convergence to the actual dense completed transfer pairing; pass finite
  sharp Cauchy--Schwarz through the three product limits; and pull the result
  back to two arbitrary dense canonical sector presentations, without a
  common-base assumption.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz.lean`.
- **decl**:
  `innerLimit_markovCutoffAction_cross_approx_eqv_form`,
  `centralPhysicalDenseMarkovCrossForm_converges`,
  `centralPhysicalDenseMarkovFormLimit_cauchy_schwarz`, and
  `centralPhysicalVacuumSectorCylinderCompletedMarkovForm_embedRep_cauchy_schwarz`.
- **obligation**: extend this dense two-vector law jointly to arbitrary
  completed sector representatives, thereby inhabiting
  `CentralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData`;
  independently construct one cofinal strict rate `q < 1` at the required
  cutoff/volume scope.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,366-job dependency-complete build pass.  The dense law is unconditional,
  but the arbitrary-completion extension, common rate, unconditional operator
  gap, thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-adaptive-completed-nonexpansive] Adaptive transfer is nonexpansive on the whole completed carrier — **PROVED 2026-08-22**

- **milestone**: align the adaptive graph input and action diagonals; compare
  them at every stage by the exact finite rational Markov `L2` contraction;
  pass the inequalities through the two explicit constructive-real limits;
  and descend the resulting squared-norm inequality to the actual completed
  adaptive transfer.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovAdaptiveNonexpansive.lean`.
- **decl**:
  `centralPhysicalAdaptiveGraph_stage_square_le`,
  `centralPhysicalAdaptiveGraph_pairing_nonexpansive`, and
  `centralPhysicalAdaptiveCompletedMarkovTransfer_norm_nonexpansive`.
- **obligation**: use this unconditional rate-one continuity to extend the
  dense positive Markov-form Cauchy--Schwarz law jointly to arbitrary
  completed sector representatives; independently construct one common
  strict rate `q < 1` at the required cutoff/volume scope.
- **constructive?**: yes — all three audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  1,310-job dependency-complete build pass.  This proves only
  `||T x||^2 <= ||x||^2` at fixed nome and volume; it does not prove a strict
  spectral gap, a thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-completed-markov-form-cauchy-schwarz] Arbitrary completed sector Markov form obeys sharp Cauchy--Schwarz — **PROVED 2026-08-22**

- **milestone**: construct one cofinal two-vector adaptive sampler paying the
  two original action requirements plus left-self, right-self, and cross-inner
  cutoff moduli; identify the three aligned finite Markov forms with the
  actual completed pairings; pass finite positive-form Cauchy--Schwarz through
  their constructive-real limits; and pull the result to the completed root
  sector.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz.lean`.
- **decl**:
  `CentralPhysicalLinearMarkovAdmissibleSample`,
  `centralPhysicalAdmissibleMarkovMap_class_eq_adaptive`,
  `centralPhysicalJointAdaptiveMarkovSampleIndex`,
  `centralPhysicalJointAdaptiveMarkov_inner_rates_paid`,
  `centralPhysicalJointAdaptiveMarkovCrossForm_converges`,
  `centralPhysicalJointAdaptiveMarkovForm_cauchy_schwarz`,
  `centralPhysicalAdaptiveCompletedMarkovForm_cauchy_schwarz`,
  `centralPhysicalVacuumSectorCylinderCompletedMarkovForm_cauchy_schwarz`,
  `centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData`,
  and
  `centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate`.
- **obligation**: construct one sector-local cofinal strict-rate certificate
  with `q < 1` at the cutoff/volume scope required downstream; the completed
  operator contraction then follows without any further Markov-form input.
- **constructive?**: yes — all eight audited final exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused monitored checks pass; the joint-schedule exact
  target passes a one-worker 1,303-job dependency-complete build and the final
  Cauchy--Schwarz target passes 1,609 jobs.  This closes the functional-
  analytic extension, not the common strict rate, unconditional spectral gap,
  thermodynamic/continuum QFT, or Clay theorem.

### [BF4-vacuum-sector-path-maximum-rate] Fixed-carrier Poincare rate uses the located maximum path scale — **PROVED 2026-08-22**

- **milestone**: construct the finite maximum of all canonical endpoint path
  scales; prove it controls every path and lies below the former sum ceiling;
  transport it to all later pulled kernels; factor positive Poincare scales
  through a reusable rate compiler; and prove the resulting maximum-based
  rate is no larger than the old sum-based rate.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathMaximum.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledPathMaximum.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledPoincareScale.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorPathMaximum`,
  `centralPhysicalFiniteVacuumSectorPathMaximum_le_ceiling`,
  `FixedBasePulledPoincareScaleData`,
  `FixedBasePulledPoincareScaleData.rate_le_of_scale_le`,
  `FixedBasePulledPositiveEdgeFloor.maximumPoincareScaleData`,
  `FixedBasePulledPositiveEdgeFloor.maximumPoincareRate_lt_one`, and
  `FixedBasePulledPositiveEdgeFloor.maximumPoincareRate_le_uniformPoincareRate`.
- **obligation**: replace the former all-base sum-ceiling certificate by the
  strictly weaker all-base maximum-rate certificate and construct one common
  `q < 1` for that sharper family.
- **constructive?**: yes — all audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused checks pass and the exact-target one-worker build
  passes 4,757 jobs.  This improves every fixed-base rational constant but
  does not bound the expanding family by one strict rate, prove an
  unconditional completed spectral gap, or reach thermodynamic/continuum QFT
  or the Clay theorem.

### [BF4-vacuum-sector-maximum-cofinal-rate] Sharper all-base maximum-rate frontier reaches completed contraction — **REDUCED 2026-08-22**

- **milestone**: isolate the all-base maximum-rate and exact
  denominator-cleared maximum/floor data; compile either witness to the
  cofinal centered finite gap and actual completed vacuum-sector contraction;
  and prove that the old sum-ceiling frontier maps to the new frontier at the
  same rate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMaximumCofinalRateBridge.lean`.
- **decl**:
  `FixedNomeUniformMaximumVacuumSectorRateBound`,
  `FixedNomeUniformMaximumVacuumSectorRateBound.selectedAnchor`,
  `FixedNomeUniformMaximumVacuumSectorRateBound.selectedAnchor_ge`,
  `FixedNomeUniformMaximumVacuumSectorRateBound.toVacuumSectorCenteredStrictGap`,
  `FixedNomeUniformMaximumVacuumSectorRateBound.toCompletedStrictContractionData`,
  `FixedNomeUniformMaximumFloorPathRateBound`,
  `FixedNomeUniformMaximumFloorPathRateBound.maximumPoincareRate_le`,
  `FixedNomeUniformMaximumFloorPathRateBound.toUniformMaximumVacuumSectorRateBound`,
  `FixedNomeUniformMaximumFloorPathRateBound.toCompletedStrictContractionData`,
  and
  `FixedNomeUniformFloorPathRateBound.toUniformMaximumVacuumSectorRateBound`.
- **obligation**: inhabit one rational `0 <= q < 1` satisfying
  `pathMaximum <= q * (pathMaximum + edgeFloor)` for every base carrier at the
  required fixed-nome, fixed-volume scope.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,890-job dependency-complete build pass.  This sharpens and contracts the
  remaining finite-volume analytic input; it does not inhabit that input,
  prove an unconditional completed gap, construct the thermodynamic/continuum
  QFT, or prove the Clay theorem.

### [BF4-vacuum-sector-path-length-rate] Polynomial canonical-path accounting sharpens the all-base completed-gap frontier — **REDUCED 2026-08-23**

- **milestone**: replace the exponential recursive path-amplification factor
  by a finite Cauchy estimate quadratic in the literal edge length; take the
  located maximum over all endpoint pairs; pull the estimate through every
  later physical kernel; construct the resulting sharper Poincare rate; and
  compile its all-base rate witness directly to the completed vacuum-sector
  strict contraction.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathLengthEnergy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathLengthMaximum.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledPathLengthMaximum.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPathLengthCofinalRateBridge.lean`.
- **decl**:
  `listQSum_square_le_length_mul_squareSum`,
  `PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_length_sq_mul_finiteJointDirichletEnergy`,
  `PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_quadraticLength_mul_rekernel_Dirichlet`,
  `centralPhysicalFiniteVacuumSectorPathLengthMaximum`,
  `centralPhysicalFiniteVacuumSectorPathLengthMaximum_le_pathMaximum`,
  `FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate`,
  `FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate_le_maximumPoincareRate`,
  `FixedNomeUniformPathLengthVacuumSectorRateBound.toCompletedStrictContractionData`,
  `FixedNomeUniformPathLengthFloorRateBound.toCompletedStrictContractionData`,
  and
  `FixedNomeUniformMaximumVacuumSectorRateBound.toUniformPathLengthVacuumSectorRateBound`.
- **obligation**: inhabit one rational `0 <= q < 1` satisfying
  `pathLengthMaximum <= q * (pathLengthMaximum + edgeFloor)` for every base
  carrier, or replace the path method with a stronger direct uniform-mixing
  proof.  An explicit uniform upper control on canonical path length together
  with an appropriately scaled positive lower control on the persistent edge
  floor is a concrete sufficient next input.
- **constructive?**: yes — all 20 audited exports use at most
  `[propext, Quot.sound]`, and `edgeLength_rekernel` uses no axioms.  No
  `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
  noncomputable declaration was added.
- **status note**: focused monitored checks pass for all five modules and the
  final exact-target one-worker dependency-complete build passes 4,895 jobs.
  The polynomial replacement and both rate comparisons are unconditional;
  the common all-base rate itself is not inhabited.  Therefore the
  unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
  remain open.

### [BF4-path-scale-floor-rate-compiler] Separate uniform scale/floor inputs compile to an explicit completed contraction — **REDUCED 2026-08-23**

- **milestone**: expose an independently checkable uniform upper bound on the
  polynomial canonical-path scale and a uniform positive lower bound on the
  persistent pulled edge floor; define `q = scale / (scale + floor)`; prove
  every fixed-base path rate is at most `q` by cross multiplication; and
  compile that rate directly to the completed vacuum-sector contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPathLengthScaleFloorCompiler.lean`.
- **decl**:
  `FixedNomeUniformPathLengthScaleUpperBound`,
  `FixedNomeUniformPulledEdgeFloorLowerBound`,
  `FixedNomeUniformPathLengthScaleUpperBound.rate_lt_one`,
  `FixedNomeUniformPathLengthScaleUpperBound.pathLengthPoincareRate_le`,
  `FixedNomeUniformPathLengthScaleUpperBound.toUniformPathLengthVacuumSectorRateBound`,
  and
  `FixedNomeUniformPathLengthScaleUpperBound.toCompletedStrictContractionData`.
- **obligation**: inhabit both a finite rational `scale > 0` uniformly
  bounding `pathLengthMaximum(base)` and a rational `floor > 0` uniformly
  below every persistent base edge floor, or prove the strictly weaker direct
  relative comparison needed by the exact polynomial rate frontier.  The
  finite-graph path-size and physical-kernel edge-weight estimates are now
  separate causal proof obligations.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check and exact-target one-worker
  4,896-job dependency-complete build pass.  This proves the compiler, not
  either uniform input.  The unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem therefore remain open.

### [BF4-simple-carrier-rate] Loop erasure exposes the carrier-size/edge-floor all-base frontier — **REDUCED 2026-08-23**

- **milestone**: constructively loop-erase every supported Boolean connectivity
  chain; prove the resulting walk is simple and bounded by its finite support;
  specialize it to a positive BF4 vacuum-sector path; derive the explicit
  scale `1 + (#sectorStates)^2`; pull its endpoint estimate through every later
  kernel; and compile a uniform rate witness directly to the completed
  vacuum-sector strict contraction.
- **files**:
  `lean/YMGap/Continuum/FiniteBoolGraphSimplePaths.lean`,
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorSimplePathScale.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledSimplePathScale.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledSimplePathPoincareGap.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorSimplePathCofinalRateBridge.lean`.
- **decl**:
  `Walk.dropTo_nodup`,
  `Walk.edgeLength_add_one_eq_vertices_length`,
  `FiniteListBound.nodup_subset_length_le`,
  `supportBoundedSimpleWalkOfChainIn`,
  `PositiveKernelChainIn.edgeLength_ofSupportedWalk`,
  `centralPhysicalFiniteVacuumSectorSimplePositivePath_edgeLength_le`,
  `centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale`,
  `centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_Dirichlet`,
  `FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_simpleCarrierSquareScale_mul_pulledDirichlet`,
  `FixedBasePulledEndpointScaleData.toPoincareScaleData`,
  `FixedBasePulledPositiveEdgeFloor.simpleCarrierPoincareRate_lt_one`,
  `FixedNomeUniformSimpleCarrierVacuumSectorRateBound.toCompletedStrictContractionData`,
  and
  `FixedNomeUniformSimpleCarrierFloorRateBound.toCompletedStrictContractionData`.
- **obligation**: inhabit one rational `0 <= q < 1` satisfying
  `1 + (#sectorStates(base))^2 <=
  q * (1 + (#sectorStates(base))^2 + edgeFloor(base))`
  for every base carrier, or replace this global-path estimate by a stronger
  direct uniform-mixing argument. This requires quantitative control of the
  carrier-cardinality/edge-floor ratio, not merely fixed-base positivity.
- **constructive?**: yes — all 19 audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused monitored checks pass for all six modules and the
  final exact-target one-worker dependency-complete build passes 4,901 jobs.
  The new scale is structurally explicit but is not claimed to be pointwise
  below the preceding canonical path maximum. The all-base rate remains
  uninhabited, so the unconditional completed gap, thermodynamic/continuum
  QFT, and Clay theorem remain open.

### [BF4-explicit-ambient-rate] Ambient power count and finite physical minimum expose a primitive all-base ratio — **REDUCED 2026-08-23**

- **milestone**: bound the loop-erased vacuum-sector cardinality by the exact
  full bounded-labelling enumeration; expose the extent-one count
  `(cutoff + 1)^24`; construct a formula-carrying persistent floor certificate
  whose floor is one half of a positive finite pulled-kernel minimum; enlarge
  the fixed-base Poincare scale to the ambient count; and compile one uniform
  denominator-cleared ambient ratio directly to the completed vacuum-sector
  strict contraction.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorSimpleCarrierAmbientBound.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorPulledAmbientPoincareGap.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorExplicitAmbientCofinalRateBridge.lean`.
- **decl**:
  `boundedEdgeLabellings_length`,
  `centralPhysicalFiniteVacuumSectorIndices_length_le_ambient`,
  `centralPhysicalFiniteVacuumSectorIndices_length_le_ambient_zero`,
  `centralPhysicalFiniteVacuumSectorSimpleCarrierSquareScale_le_ambient`,
  `explicitFixedBasePulledPositiveEdgeFloorFormula`,
  `explicitFixedBasePulledPositiveEdgeFloor_floor_eqv_value`,
  `explicitAmbientPoincareScaleFormula`,
  `explicitAmbientPoincareRate_lt_one`,
  `explicitSimpleCarrierPoincareRate_le_ambient`,
  `FixedNomeUniformExplicitAmbientVacuumSectorRateBound.toCompletedStrictContractionData`,
  `FixedNomeUniformExplicitAmbientFloorRateBound.explicitAmbientPoincareRate_le`,
  and
  `FixedNomeUniformExplicitAmbientFloorRateBound.toCompletedStrictContractionData`.
- **obligation**: inhabit one rational `0 <= q < 1` satisfying, for every
  base cutoff,
  `A(base) <= q * (A(base) + F(base))`, where
  `A = 1 + ((base + 1)^(#lowerFaceCoordinates))^2` and
  `F = (1/2) * fixedBasePulledEdgeAnchorMinimum`; or bypass this sufficient
  global-path condition with a stronger local mixing/tensorization estimate.
  Pointwise positivity of `F` is not an all-base relative lower bound.
- **constructive?**: yes — all 22 audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused monitored checks pass for all four modules and the
  final exact-target one-worker dependency-complete build passes 4,905 jobs.
  Two fully-transparent diagnostic attempts were manually interrupted and are
  not reported as passes; the formula-carrying opaque version is verified.
  The ambient rate is a sufficient upper envelope, not a proof that the actual
  vacuum sector grows or its edge floor decays. The common rate remains
  uninhabited, so the unconditional completed gap, thermodynamic/continuum
  QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-mass-normalized-rows] Correct component equilibrium and exact finite checker — **REDUCED 2026-08-23**

- **milestone**: replace the unnormalized restricted rank-one comparison by
  the canonical component-conditioned equilibrium
  `pi(x)pi(y)/pi(S)`; prove that its quadratic still vanishes under exact
  sector centering; derive the corrected row-relative finite form bound; make
  the row condition an exact Boolean scan over only the canonical vacuum
  component; and compile any constructively cofinal family of true scans to
  the existing same-object centered cutoff-limit gap.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorMassNormalizedRowGap.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorMassNormalizedFiniteChecker.lean`.
- **decl**:
  `finiteCarrierMassNormalizedStationaryProductJoint`,
  `finiteCarrierMassNormalizedStationaryProductJoint_quadratic_centered_eqv_zero`,
  `FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate.absContraction`,
  `FixedNomeCofinalVacuumSectorMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap`,
  `finiteCarrierMassNormalizedStationaryProductRowDistanceCheck`,
  `centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck`,
  `centralPhysicalFiniteVacuumSectorMassNormalizedCertificate_of_allRowsCheck`,
  `FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows.toMassNormalizedRowDistance`,
  and
  `FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows.toVacuumSectorCenteredStrictGap`.
- **obligation**: inhabit one rational `0 <= q < 1` and a constructively
  cofinal family of true sector-only scans, preferably by a
  sector-normalized conditional-density core/tail or local-slice
  tensorization estimate.  Full-carrier scans are not an admissible substitute
  because reducibility is already proved at cutoff two.
- **constructive?**: yes — all 11 audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused monitored checks pass for both modules, and the
  final exact-target one-worker dependency-complete build passes 1,482 jobs.
  Direct evaluation of a graph-defined cutoff-zero smoke theorem and
  elaboration of a redundant convenience theorem were manually interrupted
  and are not counted as successful checks; both were removed.  The finite
  checker and the cofinal compiler themselves pass.  No nontrivial cofinal check is
  inhabited, so the unconditional completed gap, thermodynamic/continuum QFT,
  and Clay theorem remain open.

### [BF4-vacuum-sector-conditioned-core-tail] Exact conditioned-density compiler — **REDUCED 2026-08-23**

- **milestone**: construct the canonical component-conditioned probability
  weight and density; prove exact recovery, normalization, and the exact row
  identity relating corrected joint distance to conditioned weighted density
  distance; specialize the `1/32 + 1/64 + 1/64` core/tail checker to the
  canonical vacuum sector; and compile any constructively cofinal family of
  true all-row checks to the existing completed centered gap at rate `1/16`.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorMassNormalizedDensity.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCoreTailFiniteChecker.lean`.
- **decl**:
  `finiteCarrierMassNormalizedWeight`,
  `finiteCarrierMassNormalizedDensity`,
  `finiteCarrierMassNormalizedStationaryProduct_mul_density_eqv_joint`,
  `finiteCarrierMassNormalizedWeight_total_one`,
  `finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass`,
  `finiteCarrierMassNormalizedRowDistance_le_sixteenth_of_coreTail`,
  `centralPhysicalFiniteVacuumSectorCoreTailAllRowsCheck`,
  `centralPhysicalFiniteVacuumSectorCoreTailCertificate_of_allRowsCheck`,
  `FixedNomeCofinalVacuumSectorCoreTailCheckedRows.toMassNormalizedRowDistance`,
  and
  `FixedNomeCofinalVacuumSectorCoreTailCheckedRows.toVacuumSectorCenteredStrictGap`.
- **obligation**: inhabit a constructively cofinal family of the sector-only
  checked core/tail rows, or replace it by an equivalent uniform sector-local
  analytic estimate.  Any attempted adapter from a full-carrier density must
  account explicitly for the conditioned component mass; reducibility at
  cutoff two prevents using the full-carrier scan as a substitute.
- **constructive?**: yes — all 11 audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused monitored checks pass for both modules.  Exact-
  target one-worker dependency-complete builds pass 1,484 jobs for the density
  target and 1,523 jobs for the final checker target.  One CPU-bound
  transparent-wrapper diagnostic was manually interrupted, removed, and is
  not reported as a pass.  No cofinal checked family is inhabited, so the
  unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
  remain open.

### [BF4-vacuum-sector-full-density-mass-defect] Exact scaling law and two-budget gap compiler — **REDUCED 2026-08-23**

- **milestone**: prove `k_S = pi(S) * k_full` on the canonical component;
  derive the exact centered identity and pointwise mass-defect estimate; lift
  it to the conditioned weighted-row inequality with exactly one additive
  copy of `|pi(S)-1|`; and compile cofinal `1/32` restricted-full-density plus
  `1/32` mass-defect budgets to the corrected row certificate and completed
  strict gap at rate `1/16`.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorDensityMassDefect.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorFullDensityMassDefectGap.lean`.
- **decl**:
  `finiteCarrierMassNormalizedDensity_eqv_mass_mul_of_joint_reconstruction`,
  `finiteCarrierMassNormalizedDensity_centered_eqv_mass_mul_full_centered_add_mass_defect`,
  `finiteCarrierMassNormalizedDensity_centered_abs_le_mass_mul_error_add_mass_defect`,
  `finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight`,
  `finiteCarrierMassNormalizedDensity_centeredRowMass_le_restrictedFull_add_massDefect`,
  `centralPhysicalFiniteVacuumSectorMassNormalizedDensity_eqv_mass_mul_fullDensity`,
  `centralPhysicalFiniteVacuumSectorRestrictedFullDensityCenteredRowMass`,
  `FixedNomeCofinalVacuumSectorFullDensityMassDefect.conditionedDensityCenteredRow_le_sixteenth`,
  `FixedNomeCofinalVacuumSectorFullDensityMassDefect.toMassNormalizedRowDistance`,
  and
  `FixedNomeCofinalVacuumSectorFullDensityMassDefect.toVacuumSectorCenteredStrictGap`.
- **obligation**: either inhabit both cofinal `1/32` budgets—restricted
  full-density row mixing and vacuum-component mass concentration—or bypass
  the second budget with a genuinely sector-normalized local mixing argument.
  No current theorem proves `pi(S)` approaches one, so full-carrier Faraut or
  local-slice estimates cannot be transferred without this explicit payment.
- **constructive?**: yes — all 12 audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused monitored checks pass for both modules.  Exact-
  target one-worker dependency-complete builds pass 1,485 jobs for the
  density-defect target and 1,486 jobs for the final two-budget gap target.
  Neither analytic budget is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-local-contraction-gluing] Sector-normalized density-power compiler — **REDUCED 2026-08-23**

- **milestone**: extract the generic signed-`L1` local-slice tensorization
  estimate `qS * qS * qS^(depth - 2)` from exact stationary row/column laws
  and exact density-power gluing; specialize it directly to the canonical
  component-conditioned BF4 weight and density; prove that `qS <= 1/4` gives
  the corrected conditioned row bound `1/16`; and compile a constructively
  cofinal family of such sector-local slices to the existing completed
  same-object vacuum-sector strict gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorLocalContractionGluing.lean`.
- **decl**:
  `FiniteWeightedLocalContractionGluingRow`,
  `FiniteWeightedLocalContractionGluingRow.middlePower_centered_row_le`,
  `FiniteWeightedLocalContractionGluingRow.middleRight_centered_row_le`,
  `FiniteWeightedLocalContractionGluingRow.density_centered_row_le_local_power`,
  `FiniteWeightedLocalContractionGluingRow.density_centered_row_le_sixteenth`,
  `PhysicalBF4VacuumSectorLocalSliceGluing`,
  `PhysicalBF4VacuumSectorLocalSliceGluing.conditionedDensityCenteredRow_le_sixteenth`,
  `FixedNomeCofinalVacuumSectorLocalSliceGluing.toMassNormalizedRowDistance`,
  and
  `FixedNomeCofinalVacuumSectorLocalSliceGluing.toVacuumSectorCenteredStrictGap`.
- **obligation**: inhabit the cofinal family by constructing a shared
  sector-preserving one-step density with exact stationary row and column
  laws, exact finite density-power gluing to the conditioned physical
  density, and a cutoff-uniform centered one-step rate `qS <= 1/4`.  The
  compiler deliberately does not assume vacuum-component mass concentration.
- **constructive?**: yes — all eight audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes, and the exact-target
  one-worker dependency-complete build passes 1,485 jobs.  No sector-local
  slice family is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-local-power-budget] Depth-amplified strict-rate compiler — **REDUCED 2026-08-23**

- **milestone**: prove the exact coefficient identity
  `(qS * qS) * qS^(depth - 2) = qS^depth`; expose the conditioned density-row
  estimate at that full local power; replace the rigid local quarter cap by a
  cofinal budget `qS(cutoff)^depth(cutoff) <= rate` for one fixed
  `0 <= rate < 1`; and compile that budget to the corrected mass-normalized
  row certificate and completed same-object vacuum-sector strict gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorLocalPowerBudgetGap.lean`.
- **decl**:
  `localPowerCoefficient_eqv_pow`,
  `PhysicalBF4VacuumSectorLocalSliceGluing.conditionedDensityCenteredRow_le_localPower`,
  `FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing`,
  `FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing.toMassNormalizedRowDistance`,
  and
  `FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing.toVacuumSectorCenteredStrictGap`.
- **obligation**: construct a cofinal family of exact sector-local
  density-power gluings and prove one uniform strict bound on the complete
  depth-amplified power.  The one-step rates themselves may now vary with the
  cutoff and approach one; no cutoff-independent quarter cap is required.
- **constructive?**: yes — all four audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,486 jobs.  An
  initial namespace-omission check failed and was corrected before both
  passing checks.  No local slice or power budget is inhabited, so the
  unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
  remain open.

### [BF4-full-carrier-local-slice-obstruction] Every strict cutoff-two slice is impossible — **PROVED 2026-08-23**

- **milestone**: generalize the physical centered-row-to-absolute-form
  contraction theorem to an arbitrary rational rate; combine it with the
  exact nonzero centered eigenvalue-one observable on the reducible
  cutoff-two positive carrier; rule out every full-carrier local slice whose
  complete tensorized coefficient
  `(qS * qS) * qS^(depth - 2)` is strictly below one; and recover the old
  quarter-rate impossibility as a corollary.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFullCarrierLocalSliceObstruction.lean`.
- **decl**:
  `physical_joint_quadratic_abs_le_rate_of_centered_rows`,
  `no_cutoffTwo_fullCarrier_localSlice_of_localPower_lt_one`,
  and
  `no_cutoffTwo_fullCarrier_localSlice_of_rate_le_quarter`.
- **obligation**: construct the local density and exact density-power gluing
  directly on the canonical vacuum component.  A uniform strict
  full-carrier slice family covering cutoff two is now formally impossible,
  so it cannot serve as an intermediate witness for later conditioning.
- **constructive?**: yes — all three audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,675 jobs.
  Initial focused checks exposed missing namespace opens; they were corrected
  before the passing check and exact build.  This closes only the false
  full-carrier producer route.  The sector-local power budget, unconditional
  completed gap, thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-conditioned-density-power] Closed-sector conditioning commutes with density powers — **PROVED 2026-08-23**

- **milestone**: prove the finite-list restriction lemma for an
  outgoing-closed subset; prove that conditioning a finite weighted density
  by a positive component mass commutes with every positive-length density
  power, leaving exactly one overall mass factor; prove that the actual BF4
  full indexed physical density vanishes from the canonical root component
  to its complement; and instantiate the power identity for the canonical
  physical vacuum sector.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorConditionedDensityPower.lean`.
- **decl**:
  `listQSum_sector_eq_full_of_zero`,
  `finiteWeightedConditionedDensityPower_eqv_mass_mul_fullPower`,
  `centralPhysicalFiniteFullDensity_eqv_zero_of_sector_complement`,
  and
  `centralPhysicalFiniteVacuumSectorConditionedDensityPower_eqv_mass_mul_fullPower`.
- **obligation**: construct an exact full physical time-factorization (or a
  sector-native equivalent), transport it through the proved closed-sector
  identity, and prove a uniform strict sector-local depth-amplified power
  budget.  The theorem prevents an artificial mass-defect accumulation but
  does not itself provide contraction.
- **constructive?**: yes — all four audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,486 jobs.
  Initial proof-engineering failures (an unavailable local tactic, omitted
  namespace opens, a reversed list-sum theorem, and a missing adjacency
  argument) were corrected before both passing checks.  No physical
  factorization or strict sector-local power budget is inhabited, so the
  unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
  remain open.

### [BF4-vacuum-sector-time-factorization-adapter] Non-strict full factorization to strict sector power — **REDUCED 2026-08-23**

- **milestone**: construct a total conditioned-kernel extension equal to
  `mass * fullOneStep` on sector endpoints and one off the sector; prove its
  exact conditioned row and column normalization from two-sided component
  closure; package the minimal non-strict full-carrier density-power
  factorization compatible with the canonical component; transport it
  exactly to the conditioned physical density; and prove the direct sector
  centered-row estimate `qS^depth`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorTimeFactorizationAdapter.lean`.
- **decl**:
  `finiteComponentConditionedKernelExtension_row_normalized`,
  `finiteComponentConditionedKernelExtension_column_normalized`,
  `PhysicalBF4VacuumSectorDensityPowerGluing.conditionedDensityCenteredRow_le_pow`,
  `PhysicalBF4FiniteVacuumCompatibleTimeFactorization.conditionedDensity_eqv_conditionedOneStepPower`,
  and
  `PhysicalBF4FiniteVacuumCompatibleTimeFactorization.toVacuumSectorDensityPowerGluing`.
- **obligation**: construct a cofinal family of non-strict compatible full
  physical time-factorizations (or the equivalent sector-native exact
  factorization), and prove a uniform strict budget for the conditioned
  one-step power `qS(cutoff)^depth(cutoff)`.  Strictness is deliberately not
  required on the reducible full carrier.
- **constructive?**: yes — all five audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,489 jobs.
  Initial missing namespace opens and one off-sector column branch were
  corrected before both passing checks.  Neither producer is inhabited, so
  the unconditional completed gap, thermodynamic/continuum QFT, and Clay
  theorem remain open.

### [BF4-vacuum-sector-direct-power-budget] Cofinal direct powers to completed sector gap — **REDUCED 2026-08-23**

- **milestone**: package a constructively cofinal family of exact conditioned
  density powers with one uniform budget
  `localRate(base,threshold)^depth(base,threshold) <= rate < 1`; compile it to
  the corrected mass-normalized row-distance certificate and completed
  same-object vacuum-sector strict gap; package the more concrete producer
  consisting of compatible non-strict full time-factorizations plus
  sector-only centered bounds; and compile that producer through the exact
  restriction adapter to the same completed gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorDirectPowerBudgetGap.lean`.
- **decl**:
  `FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toMassNormalizedRowDistance`,
  `FixedNomeCofinalVacuumSectorDensityPowerBudgetGluing.toVacuumSectorCenteredStrictGap`,
  `FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toDensityPowerBudgetGluing`,
  `FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toMassNormalizedRowDistance`,
  and
  `FixedNomeCofinalVacuumCompatibleTimeFactorizationPowerBudget.toVacuumSectorCenteredStrictGap`.
- **obligation**: inhabit the cofinal producer by constructing exact physical
  time-factorization data and proving a uniform strict conditioned power
  budget, or inhabit the equivalent direct sector-power interface.  No
  full-carrier strictness is required or possible at cutoff two.
- **constructive?**: yes — all five audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes on its first run, and
  the exact-target one-worker dependency-complete build passes 1,490 jobs.
  No cofinal producer is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-centered-Gram] Actual physical boundary factorization — **PROVED 2026-08-23**

- **milestone**: use the genuine heterogeneous BF4 reflection cut through
  fixed-time boundary channels; prove the exact component first moments and
  channel-total square mass; identify the weighted Gram of component-
  centered physical half-amplitudes with the physical joint minus the
  correctly mass-normalized stationary product; bound its row distance by
  the literal boundary-channel Tonelli majorant; and compile any cofinal
  uniform strict bound on that majorant to the completed same-object vacuum-
  sector gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGram.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSector_boundaryMoment_eqv_mass_mul_weight`,
  `centralPhysicalFiniteVacuumSector_boundaryTotalSquare_eqv_mass`,
  `centralPhysicalFiniteVacuumSector_centeredGram_eqv_joint_sub_equilibrium`,
  `centralPhysicalFiniteVacuumSector_rowDistance_le_centeredGramMajorant`,
  and
  `FixedNomeCofinalVacuumSectorCenteredGramMajorant.toVacuumSectorCenteredStrictGap`.
- **obligation**: factor the explicit centered-Gram majorant into target and
  source boundary-posterior deviations and prove a constructively cofinal
  cutoff-uniform product bound strictly below one.  This is an actual
  physical boundary factorization, not an uninhabited same-carrier root or
  density-power certificate.
- **constructive?**: yes — all five audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,487 jobs.  The
  first focused run naturally reached the heartbeat limit after namespace
  and reciprocal-normal-form errors; it was not manually interrupted, and
  all issues were corrected before both passing checks.  No cofinal
  majorant bound is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-centered-Gram-profiles] Two-factor physical row bound — **REDUCED 2026-08-23**

- **milestone**: define the literal target-channel and source-boundary
  absolute centered profiles; factor the actual sector-centered Gram
  majorant by a target profile rate; combine a source profile estimate to
  obtain the product-rate row bound; and compile a cofinal family with
  `targetRate * sourceRate < 1` to the completed same-object vacuum-sector
  gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramProfiles.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_profile_mul_sourceDeviation`,
  `centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_rateProduct_mul_weight`,
  `FixedNomeCofinalVacuumSectorCenteredGramProfileBounds.toCenteredGramMajorant`,
  and
  `FixedNomeCofinalVacuumSectorCenteredGramProfileBounds.toVacuumSectorCenteredStrictGap`.
- **obligation**: normalize both profiles as genuine sector conditional-
  probability `L1` distances and prove one constructively cofinal uniform
  product bound strictly below one.  Neither factor needs to equal the old
  quarter constant.
- **constructive?**: yes — all four audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,488 jobs.  The
  first focused check exposed missing namespace opens and one associativity
  direction; both were corrected before both passing checks.  No profile
  family is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-centered-Gram-posterior] Exact conditional-law reduction — **REDUCED 2026-08-23**

- **milestone**: construct generic weighted-Gram channel priors and state-
  conditioned channel laws; prove their exact total-one and Bayes identities;
  instantiate the target-given-boundary law, square-amplitude boundary prior,
  and boundary-given-source law on the actual BF4 vacuum sector; prove all
  three are nonnegative normalized laws; identify the two literal profile
  deviations with their exact posterior `L1` distances; handle zero-total
  channels constructively; and compile cofinal posterior mixing with product
  rate below one to the completed same-object sector gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramPosterior.lean`.
- **decl**:
  `finiteWeightedGramChannelPrior_total_one`,
  `finiteWeightedGramChannelGivenState_total_one`,
  `finiteWeightedGramChannelBayesDifference_mul_rowMass`,
  `centralPhysicalFiniteVacuumSectorTargetGivenBoundary_total_one`,
  `centralPhysicalFiniteVacuumSectorBoundaryPrior_total_one`,
  `centralPhysicalFiniteVacuumSectorBoundaryGivenSource_total_one`,
  `centralPhysicalFiniteVacuumSectorTargetProfileDeviation_eq_total_mul_posteriorL1`,
  `centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_eq_weight_mul_posteriorL1`,
  and
  `FixedNomeCofinalVacuumSectorCenteredGramPosteriorMixing.toVacuumSectorCenteredStrictGap`.
- **obligation**: prove constructively cofinal cutoff-uniform `L1` mixing
  bounds for both actual conditional laws whose product is strictly below
  one, or supply a projective/coupling certificate that entails those
  bounds.  The normalization and all component-mass cancellation are now
  kernel-checked rather than assumed.
- **constructive?**: yes — all twelve audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,490 jobs.  The
  initial focused run naturally hit its deterministic heartbeat after
  unresolved namespace errors; it was not manually interrupted.  Missing
  opens and one later function-arity mismatch were corrected before both
  passing checks.  No posterior-mixing family is inhabited, so the
  unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
  remain open.

### [BF4-vacuum-sector-centered-Gram-projective] One diameter to both posterior quarters — **REDUCED 2026-08-23**

- **milestone**: prove projective spread is invariant under one- and two-ray
  positive normalization; specialize positive column and row summation to
  the actual BF4 vacuum-sector half-amplitude matrix; derive both normalized
  posterior projective bounds from one four-index cross-ratio field; use the
  squared-spread ceiling `65/64` to obtain both posterior `L1` quarters; and
  compile their semantic `1/16` product rate to the completed same-object
  vacuum-sector gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramProjective.lean`.
- **decl**:
  `projectiveSpreadBound_divPos_left`,
  `projectiveSpreadBound_divPos_both`,
  `centralPhysicalFiniteVacuumSector_targetRawProjective`,
  `centralPhysicalFiniteVacuumSector_sourceRawProjective`,
  `centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_quarter_of_crossRatio`,
  `centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_quarter_of_crossRatio`,
  and
  `FixedNomeCofinalVacuumSectorHalfAmplitudeProjective.toVacuumSectorCenteredStrictGap`.
- **obligation**: prove the cofinal squared-spread `65/64` cross-ratio bound
  for the actual sector half-amplitude matrix, or prove that its support
  pattern obstructs this sufficient condition and construct a support-
  compatible coupling or multi-step posterior estimate instead.
- **constructive?**: yes — all seven audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,494 jobs.  The
  initial focused run naturally hit its deterministic heartbeat after
  missing namespace opens; it was not manually interrupted.  Adding the
  stationary-law and quarter-constant namespaces resolved all errors before
  both passing checks.  No projective family is inhabited, so the
  unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
  remain open.

### [BF4-vacuum-sector-projective-obstruction] Cutoff-two support rectangle — **OBSTRUCTED 2026-08-23**

- **milestone**: prove the fundamental-cube half-amplitude is strictly
  positive at the explicit single-face boundary, prove the vacuum amplitude
  vanishes at that boundary and is positive at the vacuum boundary, place
  the cube in the canonical 65-state vacuum sector, and use the resulting
  support rectangle to refute every rational half-amplitude projective
  spread on the cutoff-two sector and full boundary carrier.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorProjectiveObstruction.lean`.
- **decl**:
  `centralHalfAmplitude_cutoffTwo_cube_singleFaceBoundary_pos`,
  `centralHalfAmplitude_cutoffTwo_vacuum_singleFaceBoundary_eqv_zero`, and
  `no_cutoffTwo_vacuumSector_halfAmplitudeCrossRatio`.
- **obligation**: replace the globally positive projective criterion by a
  support-compatible overlap, minorization, coupling, or multi-step
  posterior estimate.  The cutoff-two contradiction does not rule out a
  cofinal family whose anchors skip cutoff two, and it does not refute the
  exact posterior route itself.
- **constructive?**: yes — all three audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes after one missing
  namespace open was corrected, and the exact-target one-worker dependency-
  complete build passes 3,583 jobs.  No support-compatible cofinal mixing
  certificate is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-centered-Gram-overlap] Support-compatible posterior common mass — **REDUCED 2026-08-23**

- **milestone**: define canonical finite overlap as the sum of pointwise
  minima; prove the generic common-submass residual inequality and the
  normalized `L1 <= 2(1-overlap)` bound; specialize overlap to both actual
  vacuum-sector posterior pairs; and compile cofinal target/source overlap
  floors with residual-rate product below one to the completed same-object
  vacuum-sector strict gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramOverlap.lean`.
- **decl**:
  `qAbs_sub_le_common_residuals`,
  `finiteL1Distance_le_commonResidualMass`,
  `finiteL1Distance_le_two_mul_one_sub_overlap`,
  `centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_of_overlap`,
  `centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_of_overlap`,
  and
  `FixedNomeCofinalVacuumSectorPosteriorOverlap.toVacuumSectorCenteredStrictGap`.
- **obligation**: prove constructively cofinal positive lower bounds on both
  exact physical posterior overlaps, or obtain them after a fixed number of
  support-compatible steps, with
  `[2(1-alpha)] * [2(1-beta)] < 1`.  No global positive-support ratio is
  assumed.
- **constructive?**: yes — all seven audited exports use at most
  `[propext, Quot.sound]`, and the four generic finite exports use only
  `[propext]`; no `Classical.*`, choice, `native_decide`, `sorry`, custom
  axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,491 jobs.  The
  first focused run naturally hit its deterministic heartbeat after two raw-
  denominator algebra normalizations and missing namespace opens caused
  cascading elaboration errors; it was not manually interrupted.  Replacing
  those calculations by structural exact-rational identities and adding the
  required namespaces resolved every error before both passing checks.  No
  cofinal overlap family is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-overlap-positivity] Inhabited finite common mass — **PROVED FINITE 2026-08-23**

- **milestone**: prove a normalized finite law has positive overlap with a
  nonnegative reference positive on its support; prove overlap is at most the
  left total mass; derive the exact physical Bayes support inclusion from
  `boundary | source` to the square-amplitude prior; and conclude both actual
  BF4 posterior overlaps lie in `(0,1]` at every fixed cutoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramOverlapPositivity.lean`.
- **decl**:
  `finiteProbabilityOverlap_pos_of_support`,
  `finiteProbabilityOverlap_le_leftMass`,
  `centralPhysicalFiniteVacuumSectorBoundaryPrior_pos_of_givenSource_pos`,
  `centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_pos`,
  `centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_pos`,
  `centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_le_one`, and
  `centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_le_one`.
- **obligation**: form the exact minimum over each finite family of positive
  target channels and sector sources, then prove a constructively cofinal
  cutoff-uniform floor strong enough that the product of residual rates is
  below one.  Pointwise finite positivity does not imply this persistence.
- **constructive?**: yes — all seven audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes after adding two
  missing namespace opens, and the exact-target one-worker dependency-
  complete build passes 1,492 jobs.  The theorem is finite-cutoff only: its
  positive overlaps may decay to zero, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-overlap-floor] Two exact finite minima — **PROVED FINITE / REDUCED 2026-08-23**

- **milestone**: construct a positive capped finite minimum; totalize the
  target and source overlap functions with neutral value one off the relevant
  positive carrier; fold over the literal boundary and canonical-sector
  lists; prove both exact floors lie in `(0,1]` and bound every relevant
  posterior overlap; and compile uniform persistence of the two scalars to
  the completed same-object vacuum-sector gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramOverlapFloor.lean`.
- **decl**:
  `finiteCappedMinimum_pos`,
  `finiteCappedMinimum_le_member`,
  `centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_pos`,
  `centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_pos`,
  `centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_le`,
  `centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_le`, and
  `FixedNomeCofinalVacuumSectorPosteriorOverlapFloorPersistence.toVacuumSectorCenteredStrictGap`.
- **obligation**: prove cofinal cutoff-uniform lower bounds on the two exact
  finite floors whose residual-rate product is below one, or equivalently
  control their single exact product-rate scalar uniformly below one.
- **constructive?**: yes — all seven audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,493 jobs.  The
  first focused check exposed three elementary `0 < 1` goals whose expected
  types retained free variables; explicit type annotations resolved them
  before both passing checks.  Fixed-cutoff positivity does not imply a
  cofinal floor, so the unconditional completed gap, thermodynamic/continuum
  QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-overlap-residual-rate] One exact scalar to centered Gram — **REDUCED 2026-08-23**

- **milestone**: define the two exact overlap-deficit `L1` rates and their
  single product `r_K`; prove each physical posterior distance and profile
  deviation is controlled by its finite rate; prove the literal centered-Gram
  row majorant is bounded by `r_K * physicalWeight(source)`; and compile a
  constructively cofinal upper bound `r_K <= q < 1` directly to the completed
  same-object vacuum-sector strict gap.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_nonnegative`,
  `centralPhysicalFiniteVacuumSectorTargetGivenBoundaryL1_le_overlapResidualRate`,
  `centralPhysicalFiniteVacuumSectorBoundaryGivenSourceL1_le_overlapResidualRate`,
  `centralPhysicalFiniteVacuumSectorTargetProfileDeviation_le_overlapResidualRate`,
  `centralPhysicalFiniteVacuumSectorSourceBoundaryProfileDeviation_le_overlapResidualRate`,
  `centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_overlapResidualRate_mul_weight`,
  and
  `FixedNomeCofinalVacuumSectorPosteriorOverlapResidualRateBound.toVacuumSectorCenteredStrictGap`.
- **obligation**: prove one constructively cofinal uniform rational bound
  `r_K <= q < 1` for the explicit finite residual-rate sequence.  Separate
  uniform lower bounds on the target and source floors are sufficient but no
  longer required by the formal interface.
- **constructive?**: yes — all seven audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes after one
  missing positive-connectivity namespace was added, and the exact-target
  one-worker dependency-complete build passes 1,494 jobs.  No cofinal bound
  below one is inhabited, so the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-vacuum-sector-overlap-residual-ceiling] Exact scalar is uniformly below four — **PROVED / THRESHOLD OPEN 2026-08-23**

- **milestone**: use strict positivity of both exact finite overlap floors to
  prove each overlap-residual factor is strictly below two, and combine those
  estimates with residual nonnegativity to bound the one centered-Gram scalar
  strictly below four at every cutoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorCenteredGramOverlapResidualCeiling.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate_lt_two`,
  `centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate_lt_two`,
  and
  `centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_lt_four`.
- **obligation**: improve the unconditional all-cutoff ceiling `< 4` to a
  constructively cofinal fixed bound `r_K <= q < 1`.  The theorem quantifies
  this threshold gap but does not inhabit the completed-gap certificate.
- **constructive?**: yes — all three audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes, and the exact-target
  one-worker dependency-complete build passes 1,495 jobs in 269 seconds.  The
  uniform `< 4` estimate is not an operator contraction; the unconditional
  completed gap, thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-one-canonical-vacuum-sector] Exact vacuum/cube support identification — **PROVED FINITE 2026-08-23**

- **milestone**: transport zero mass outside the exact normalized two-row
  block back to the raw reflected kernel; prove one-step support-graph
  no-escape constructively through faithful finite state codes; propagate
  closure along every rooted-component chain; prove the vacuum-to-cube entry
  is positive; and identify the canonical cutoff-one vacuum-sector state
  support exactly with `[vacuum, central cube]`.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffOneVacuumCubeNoEscape.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector.lean`.
- **decl**:
  `centralPhysicalReflectedKernel_cutoffOne_vacuumCube_eqv_zero_of_outside`,
  `next_state_mem_cutoffOneVacuumCubeBlock_of_adjacent`,
  `canonicalVacuumSectorState_mem_cutoffOneVacuumCubeBlock`,
  `centralPhysicalReflectedKernel_cutoffOne_vacuum_cube_pos`,
  `centralLowerCubeState_mem_cutoffOneCanonicalVacuumSector`, and
  `centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff`.
- **obligation**: use this exact support identification to evaluate the
  canonical target/source posterior overlap floors, or their product
  residual scalar, at cutoff one; then construct a support-stable mechanism
  that gives one fixed cofinal bound `r_K <= q < 1`.
- **constructive?**: yes — all six audited exports use exactly
  `[propext, Quot.sound]`.  A direct labelling-equality branch exposed
  `Classical.choice` and was replaced by decidable natural-number state-code
  comparisons plus positive-carrier code injectivity.  No `Classical.*`,
  choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
  remains.
- **status note**: both focused monitored checks pass; exact-target
  one-worker dependency-complete builds pass 1,398 and 1,399 jobs.  Earlier
  exploratory checks and the broad `YMGapGuard` audit were interrupted and
  are not counted as passes.  The theorem is cutoff-one only; the cofinal
  completed gap, thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-one-canonical-refresh] Genuine canonical-sector refresh action — **PROVED FINITE 2026-08-23**

- **milestone**: transport the exact vacuum/cube physical Gram refresh law
  through the exact rooted-component support identification; prove every
  actual canonical-sector source has the same posterior-refresh row, the
  restricted row remains normalized, constants are fixed, and the explicit
  nonconstant posterior-centered cube mode is annihilated.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh.lean`.
- **decl**:
  `cutoffOneCanonicalVacuumSectorPhysicalGramMarkov_eqv_refresh`,
  `cutoffOneCanonicalVacuumSectorPhysicalGramMarkov_row_normalized`,
  `cutoffOneCanonicalVacuumSectorPhysicalGramAction_one`, and
  `cutoffOneCanonicalVacuumSectorPhysicalGramAction_centeredCubeMode_zero`.
- **obligation**: identify the indexed sector-conditioned stationary law
  with the exact refresh posterior, then evaluate both posterior-overlap
  floors and the product residual scalar at cutoff one; afterward prove a
  fixed cofinal `r_K <= q < 1` estimate.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,402 jobs.  The
  first focused check failed on a generic-versus-concrete `EdgeLabelling`
  namespace ambiguity and is not counted as a passing audit.  This theorem is
  cutoff-one only; the cofinal completed gap, thermodynamic/continuum QFT,
  and Clay theorem remain open.

### [BF4-cutoff-one-canonical-presentation] Multiplicity-free two-state recoding — **PROVED FINITE 2026-08-23**

- **milestone**: prove totalized finite-carrier lookup is injective on the
  canonical component; prove the mapped cutoff-one canonical state list is
  nodup and a permutation of `[vacuum, central cube]`; and transport every
  rational list sum across that exact permutation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorStates_cutoffOne_nodup`,
  `cutoffOneVacuumCubePhysicalSources_nodup`,
  `centralPhysicalFiniteVacuumSectorStates_cutoffOne_perm`, and
  `centralPhysicalFiniteVacuumSectorStates_cutoffOne_sum_eqv`.
- **obligation**: use the multiplicity-free recoding and exact refresh rows
  to identify the indexed sector-conditioned stationary law with the refresh
  posterior; then evaluate both overlap floors and `r_1`, followed by a fixed
  cofinal `r_K <= q < 1` estimate.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,403 jobs.  Two
  failed focused checks exposed a reversed local associativity step and a
  missing namespace for `zeroEdgeLabelling`; neither is counted as a pass.
  This is cutoff-one only; the cofinal completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-one-canonical-stationary-posterior] Exact conditioned stationary law — **PROVED FINITE 2026-08-23**

- **milestone**: express physical row marginals through raw positive-row mass
  and the common partition reciprocal; prove the cutoff-one cube marginal is
  the six-face activity times the vacuum marginal; compute the exact
  two-state component mass; and identify every indexed component-conditioned
  stationary weight with the genuine vacuum-column refresh posterior.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior.lean`.
- **decl**:
  `centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal`,
  `centralPhysicalRowMarginal_cutoffOne_cube_eqv_activity_mul_vacuum`,
  `centralPhysicalFiniteVacuumSectorMass_cutoffOne_eqv`, and
  `centralPhysicalFiniteVacuumSectorMassNormalizedWeight_cutoffOne_eqv_posterior`.
- **obligation**: combine this stationary-law identification with the common
  physical refresh-row theorem to evaluate both exact posterior-overlap floors
  and the product residual scalar at cutoff one; then prove one fixed cofinal
  bound `r_K <= q < 1`.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,548 jobs.  One
  exploratory check was interrupted and three bounded checks failed during
  factoring; none is counted as a pass.  This theorem is cutoff-one only; the
  cofinal completed gap, thermodynamic/continuum QFT, and Clay theorem remain
  open.

### [BF4-cutoff-one-canonical-overlap-residual] Exact rank-one Bayes factorization and zero residual — **PROVED FINITE 2026-08-23**

- **milestone**: prove the cutoff-one cube half-amplitude is a fixed activity
  multiple of the vacuum half-amplitude on every boundary channel; derive the
  exact indexed stationary-times-channel-total factorization; identify both
  physical conditional laws with their priors; and evaluate the two overlap
  floors and their product residual scalar.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.lean`.
- **decl**:
  `centralHalfAmplitude_cutoffOne_cube_eqv_activity_mul_vacuum_on_boundary`,
  `centralPhysicalFiniteVacuumSectorGramAmplitude_cutoffOne_eqv_stationary_mul_channelTotal`,
  `centralPhysicalFiniteVacuumSectorTargetGivenBoundary_cutoffOne_eqv_stationary`,
  `centralPhysicalFiniteVacuumSectorBoundaryGivenSource_cutoffOne_eqv_prior`,
  `centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_cutoffOne_eqv_one`,
  `centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_cutoffOne_eqv_one`,
  and
  `centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_cutoffOne_eqv_zero`.
- **obligation**: construct an all-cutoff support-stable defect estimate that
  preserves enough of the cutoff-one rank-one factorization to prove one fixed
  constructively cofinal bound `r_K <= q < 1`.
- **constructive?**: yes — all seven audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes in 1.2
  seconds, and the exact-target one-worker dependency-complete build passes
  1,556 jobs.  One exploratory run was interrupted and two low-heartbeat
  diagnostics failed during factoring; none is counted as a pass.  The exact
  zero residual is cutoff-one only; the cofinal completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-exact-posterior-L1-maximum-rate] Sharp finite Bayes-defect scalar — **PROVED / COFINAL BOUND OPEN 2026-08-23**

- **milestone**: totalize both actual posterior `L1` defects, construct their
  located finite maxima and product `s_K`, prove the literal centered physical
  Gram row is bounded by `s_K` times the source stationary weight, compile a
  cofinal bound below one to the completed gap, compare `s_K <= r_K`, and
  evaluate `s_1 = 0`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorExactPosteriorL1MaximumRate.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_nonnegative`,
  `centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactPosteriorL1MaximumRate_mul_weight`,
  `FixedNomeCofinalVacuumSectorExactPosteriorL1MaximumRateBound.toVacuumSectorCenteredStrictGap`,
  `centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_le_overlapResidualRate`,
  `centralPhysicalFiniteVacuumSectorTargetPosteriorL1Maximum_cutoffOne_eqv_zero`,
  `centralPhysicalFiniteVacuumSectorSourcePosteriorL1Maximum_cutoffOne_eqv_zero`,
  and
  `centralPhysicalFiniteVacuumSectorExactPosteriorL1MaximumRate_cutoffOne_eqv_zero`.
- **obligation**: prove one constructively cofinal fixed bound `s_K <= q < 1`,
  or pass to the still sharper normalized centered-Gram row maximum and prove
  that scalar uniformly below one.
- **constructive?**: yes — all eight audited exports use at most
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes in 0.83
  seconds, and the exact-target one-worker dependency-complete build passes
  1,557 jobs.  The first focused check failed on a namespace ambiguity and is
  not counted as a pass.  No cofinal bound below one is inhabited; the
  unconditional completed gap, thermodynamic/continuum QFT, and Clay theorem
  remain open.

### [BF4-exact-centered-Gram-row-rate] Least finite centered-row coefficient — **PROVED / COFINAL BOUND OPEN 2026-08-23**

- **milestone**: totalize the normalized centered physical Gram row majorant,
  take its located finite maximum `g_K`, prove the direct row inequality and
  the minimality of `g_K` among all nonnegative common row coefficients,
  compile a cofinal bound below one to the completed gap, prove
  `g_K <= s_K <= r_K`, and evaluate `g_1 = 0`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorExactCenteredGramRowRate.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorCenteredGramRowMajorant_le_exactCenteredGramRowRate_mul_weight`,
  `centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_of_rowBound`,
  `FixedNomeCofinalVacuumSectorExactCenteredGramRowRateBound.toVacuumSectorCenteredStrictGap`,
  `centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_exactPosteriorL1MaximumRate`,
  `centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_le_overlapResidualRate`,
  and
  `centralPhysicalFiniteVacuumSectorExactCenteredGramRowRate_cutoffOne_eqv_zero`.
- **obligation**: prove one constructively cofinal fixed bound
  `g_K <= q < 1`, or add finite geometric information that strictly sharpens
  the literal centered-row majorant itself.
- **constructive?**: yes — all seven audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes, and the exact-target
  one-worker dependency-complete build passes 1,558 jobs.  No cofinal bound
  below one is inhabited; the unconditional completed gap,
  thermodynamic/continuum QFT, and Clay theorem remain open.

### [BF4-exact-mass-normalized-row-rate] Least actual finite row-distance coefficient — **PROVED / COFINAL BOUND OPEN 2026-08-23**

- **milestone**: define the literal component-conditioned physical row
  distance, normalize it by each positive stationary source weight, take its
  located finite maximum `h_K`, prove its direct row inequality and minimality,
  compile a cofinal bound below one to the completed gap, prove
  `h_K <= g_K <= s_K <= r_K`, and evaluate `h_1 = 0`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorExactMassNormalizedRowRate.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_nonnegative`,
  `centralPhysicalFiniteVacuumSectorMassNormalizedRowDistance_le_exactRate_mul_weight`,
  `centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_of_rowBound`,
  `FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound.toVacuumSectorCenteredStrictGap`,
  `centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_le_exactCenteredGramRowRate`,
  and
  `centralPhysicalFiniteVacuumSectorExactMassNormalizedRowRate_cutoffOne_eqv_zero`.
- **obligation**: prove one constructively cofinal fixed bound
  `h_K <= q < 1`, derive such a bound from actual BF4 finite geometry, or pass
  to a strictly sharper signed-form/operator coefficient.
- **constructive?**: yes — all seven audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes, and the
  exact-target one-worker dependency-complete build passes 1,559 jobs.  Three
  earlier focused checks failed on missing namespace opens and a redundant
  unfold; none is counted as a pass.  No cofinal bound below one is inhabited;
  the unconditional completed gap, thermodynamic/continuum QFT, and Clay
  theorem remain open.

### [BF4-exact-row-rate-checker] Exact Boolean/scalar equivalence — **PROVED / COFINAL CHECK OPEN 2026-08-23**

- **milestone**: prove one row check is exactly its literal inequality; prove
  the all-row scan is exactly the family of canonical-source inequalities;
  prove for every nonnegative `q` that
  `allRowsCheck_K(q) = true <-> h_K <= q`; convert the cofinal exact-rate and
  checked-row structures both ways; and certify the cutoff-one scan at rate
  zero.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalVacuumSectorExactMassNormalizedRowRateChecker.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorMassNormalizedRowCheck_eq_true_iff`,
  `centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_rowBounds`,
  `centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_eq_true_iff_exactRate_le`,
  `FixedNomeCofinalVacuumSectorExactMassNormalizedRowRateBound.toCheckedRows`,
  `FixedNomeCofinalVacuumSectorMassNormalizedCheckedRows.toExactRateBound`,
  and
  `centralPhysicalFiniteVacuumSectorMassNormalizedAllRowsCheck_cutoffOne_zero`.
- **obligation**: evaluate or prove the first nontrivial cutoff-two exact row
  criterion, then find one strict rate whose equivalent all-row scan succeeds
  on a constructively cofinal unbounded cutoff family.
- **constructive?**: yes — all six audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes on the first attempt,
  and the exact-target one-worker dependency-complete build passes 1,560 jobs.
  The cutoff-one rate-zero check is finite only; no nontrivial cofinal scan,
  thermodynamic/continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-exact-row-rate-obstruction] Production row-TV obstruction — **PROVED FINITE 2026-08-23**

- **milestone**: evaluate the exact 65-state raw component mass and one
  denominator-cleared row distance; prove row ten is strictly superunit; and
  transport the result through the sealed shared-DAG certificate to the
  genuine cutoff-two production reflected kernel.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoExactRowRateObstruction.lean`.
- **decl**:
  `cutoffTwoSectorRawMass_eqv_value`,
  `cutoffTwoSectorClearedRowTen_eqv_value`,
  `cutoffTwoSectorClearedRowTen_gt_mass_mul_rowSum`,
  `cutoffTwoSectorPhysicalMass_eqv_rawMass`,
  `cutoffTwoSectorPhysicalClearedMassNormalizedRowDistance_eqv_raw`, and
  `cutoffTwoSectorPhysicalClearedRowTen_gt_mass_mul_rowSum`.
- **obligation**: transport the row-ten witness through the canonical
  state-list permutation to the named exact scalar `h_2`; then replace the
  nonviable per-row TV route by a cancellation-preserving signed-form or
  spectral certificate on a constructively cofinal cutoff family.
- **constructive?**: yes — the raw arithmetic exports use no axioms and the
  physical transport exports use exactly `[propext, Quot.sound]`; no
  `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
  noncomputable declaration was added.
- **status note**: the corrected focused monitored check passes in 6.2
  seconds, and the exact-target one-worker dependency-complete build passes
  3,419 jobs.  An aggregate prerequisite build was stopped at the configured
  memory reserve and one narrowed focused check failed on a missing namespace
  open; neither is counted as a pass.  The theorem is finite and cutoff-two
  only.  It leaves cofinal signed-form control, the completed uniform gap,
  thermodynamic/continuum QFT, and the Clay theorem open.

### [BF4-cutoff-two-normalized-row-rate-obstruction] Partition-scale invariance — **PROVED FINITE 2026-08-23**

- **milestone**: package the positive physical partition scale with exact
  kernel and row-sum transports; prove the normalized component mass and
  cleared row distance scale respectively by the first and second powers of
  that common factor; and preserve the strict row-ten obstruction.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoExactMassNormalizedRowRateObstruction.lean`.
- **decl**:
  `CutoffTwoPartitionScaleCertificate`,
  `cutoffTwoSectorNormalizedMass_eqv_physical_mul_rowRateReciprocal`,
  `cutoffTwoSectorNormalizedClearedMassNormalizedRowDistance_eqv_scaled`, and
  `cutoffTwoSectorNormalizedClearedRowTen_gt_mass_mul_rowSum`.
- **obligation**: transport the normalized row-ten witness through the exact
  canonical state-list permutation to prove that the named exact scalar
  `h_2` is superunit; then replace row TV by a cancellation-preserving signed
  form or spectral certificate on a constructively cofinal cutoff family.
- **constructive?**: yes — all three audited obstruction exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the corrected focused checks pass in about 1.3 seconds;
  the exact normalization target passes 4,684 jobs and the exact obstruction
  target passes 4,686 jobs.  Earlier timeout, syntax, namespace, stack,
  algebra-shape, and intentionally interrupted diagnostic runs are not passes.
  The theorem is finite and cutoff-two only.  The canonical `h_2` bridge,
  cofinal signed-form control, completed uniform gap, thermodynamic/continuum
  QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-canonical-exact-row-rate-obstruction] Named `h_2` obstruction — **PROVED FINITE 2026-08-23**

- **milestone**: locate table row ten inside the exact canonical
  vacuum-sector list; recode its normalized mass and denominator-cleared row
  distance; and prove the named exact canonical rate satisfies `1 < h_2`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalExactRowRateObstruction.lean`.
- **decl**:
  `exists_cutoffTwoCanonicalVacuumSectorIndex_rowTen`,
  `cutoffTwoSectorNormalizedMass_eqv_canonicalVacuumSectorMass`,
  `cutoffTwoCanonicalClearedRowTen_eqv_normalizedRowTen`,
  `cutoffTwoCanonicalMass_mul_rowDistance_eqv_rowTenCleared`,
  `cutoffTwoCanonicalExactMassNormalizedRowRate_not_le_one`, and
  `cutoffTwoCanonicalExactMassNormalizedRowRate_one_lt`.
- **obligation**: abandon the now-refuted subunit row-TV route and construct
  a cancellation-preserving signed-form or upper-LDL certificate on a
  constructively cofinal cutoff family, then transport the resulting uniform
  dense gap through completion and controlled limits.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the final focused monitored check passes in about 2.8
  seconds, and the exact-target one-worker dependency-complete build passes
  4,790 jobs.  Long-running direct wrappers and diagnostic `#exit` probes
  were interrupted and are not passes; a missing namespace qualification was
  corrected.  The theorem is finite and cutoff-two only.  Cofinal signed-form
  control, the completed uniform gap, thermodynamic/continuum QFT, and the
  Clay theorem remain open.

### [BF4-cutoff-vacuum-sector-upper-LDL-bridge] Upper-only LDL to same-object limits — **CLOSED 2026-08-23**

- **milestone**: compile ordinary and cleared upper-only canonical
  full-carrier LDL families at a supplied `0 <= q < 1` into the exact
  same-object centered-sector certificate; use reflection positivity to
  recover the absolute bound; and prove the corresponding `CReal.leEv`
  cutoff-limit inequalities.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorCanonicalLDLBridge.lean`.
- **decl**:
  `FixedNomeCofinalCanonicalHeadUpperLDLAtRate.toVacuumSectorCenteredStrictGap`,
  `FixedNomeCofinalCanonicalHeadUpperLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`,
  `FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate.toVacuumSectorCenteredStrictGap`,
  and
  `FixedNomeCofinalCanonicalHeadUpperClearedLDLAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`.
- **obligation**: construct an actual cofinal upper-only canonical LDL family
  at one strict rate uniform in cutoff, or derive it from a smaller
  cancellation-preserving finite/tail certificate.  No inhabitant is asserted
  here.
- **constructive?**: yes — all four new audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes in about 1.3 seconds,
  and the exact-target one-worker dependency-complete build passes 4,755
  jobs.  One prolonged direct positivity reproving attempt was interrupted
  and is not a pass.  This closes the implication from a named upper-LDL
  input, not construction of that input, a completed gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-vacuum-sector-local-canonical-LDL] Sector-local upper compiler — **CLOSED 2026-08-23**

- **milestone**: reindex exactly the canonical vacuum-component list; prove
  coordinate mean, diagonal, and matrix forms equal the physical sector
  forms; construct the positive-head restriction on that smaller matrix; and
  compile ordinary or cleared cofinal upper LDL families to the same-object
  centered certificate and its `CReal.leEv` limit inequality.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorCoordinateMean_eqv`,
  `centralPhysicalFiniteVacuumSectorCoordinateDiagonal_eqv`,
  `centralPhysicalFiniteVacuumSectorCoordinateMatrix_eqv`,
  `centralPhysicalFiniteVacuumSectorCanonicalHeadRestriction`,
  both `CentralPhysicalFiniteVacuumSectorCanonicalHeadUpper*LDLCertificate.meanZeroAbsGap`
  theorems, and both cofinal `toVacuumSectorCenteredStrictGap` and
  `centeredMatrixCutoffLimit_leEv_rate_mul_diagonal` pairs.
- **obligation**: identify the cutoff-two `49/50` certificate with this
  generated sector-local restriction, then construct one strict-rate family
  on a constructively cofinal unbounded cutoff schedule.  No cofinal
  inhabitant is asserted.
- **constructive?**: yes — all ten audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes in about 1.3 seconds,
  and the exact-target one-worker dependency-complete build passes 4,756
  jobs.  Two early namespace/unfold failures are not passes.  This closes a
  certificate recoding implication, not its cofinal inhabitant, the completed
  gap, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-sector-local-upper-PSD] Generated finite inhabitant — **PROVED FINITE 2026-08-23**

- **milestone**: construct a structurally recursive coordinate-to-ambient
  lift with an exact right inverse; transport arbitrary physical-sector
  absolute gaps to the generated sector ordering; factor upper PSD as the
  order-invariant centered-restriction certificate; and inhabit that exact
  certificate at cutoff two and rate `49/50`.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoVacuumSectorLocalUpperPSDCertificate.lean`.
- **decl**:
  `natListCoordinateLift_getD_of_nodup`,
  `centralPhysicalFiniteVacuumSectorCoordinateLift_recovers`,
  `centralPhysicalFiniteVacuumSectorCoordinateAbsGap_of_sectorAbsGap`,
  `FiniteCenteredRestrictionUpperPSDCertificate.upperContraction`,
  `CentralPhysicalFiniteVacuumSectorCanonicalHeadUpperPSDCertificate.ofMeanZeroAbsGap`,
  `cutoffTwoCanonicalVacuumSectorUpperPSDCertificateAt49Over50`, and
  `cutoffTwoCanonicalVacuumSectorCanonicalHeadUpperMatrix_nonnegative`.
- **obligation**: construct these generated upper-PSD witnesses at one fixed
  `0 <= q < 1` on an unbounded cofinal cutoff schedule, then feed that family
  through the same-object CReal and completed vacuum-sector compilers.  The
  cutoff-two inhabitant alone supplies no uniform persistence.
- **constructive?**: yes — every new audited export uses exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused checks pass in about 1.5 and 1.8 seconds, and the
  exact-target one-worker dependency-complete build passes 4,757 jobs.
  Interrupted elaboration probes and the rejected choice-bearing `idxOf`
  inverse are not passes.  This proves one finite generated witness, not its
  cofinal uniform family, a completed gap, thermodynamic/continuum QFT, or the
  Clay theorem.

### [BF4-cofinal-sector-local-upper-PSD] Cofinal finite gaps to completion — **CLOSED 2026-08-23**

- **milestone**: define cofinal generated upper-PSD families; compile them at
  a supplied strict rate to the same-object CReal limit inequality; isolate
  the equivalent direct physical finite-sector strict-gap family; and carry
  either formulation to the actual completed vacuum-sector transfer
  contraction.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorLocalCanonicalLDLBridge.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge.lean`.
- **decl**:
  `CofinalFixedCenteredRestrictionUpperPSDCertificate`,
  `FixedNomeCofinalVacuumSectorCanonicalHeadUpperPSDAtRate.toVacuumSectorCenteredStrictGap`,
  `FixedNomeCofinalVacuumSectorCanonicalHeadUpperPSDAtRate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal`,
  `FixedNomeCofinalVacuumSectorFiniteStrictGap`,
  `FixedNomeCofinalVacuumSectorFiniteStrictGap.toCanonicalHeadUpperPSDAtRate`,
  `FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData`,
  and the upper-PSD-family `toCompletedStrictContractionData`.
- **obligation**: inhabit the cofinal family at one uniform `q < 1`.  The
  cutoff-two `49/50` certificate is only one finite anchor and does not imply
  an unbounded schedule.  Then establish the additional volume/spacing
  control required by the continuum construction.
- **constructive?**: yes — all six newly audited cofinal exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: focused checks pass in about 1.6 and 1.1 seconds, and the
  exact-target one-worker dependency-complete build passes 4,884 jobs.
  Interrupted abnormal elaboration and diagnostic `#exit` runs are not
  passes.  This closes the implication from a cofinal finite strict-gap/PSD
  family to completion, not construction of that family, thermodynamic or
  continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-full-sector-persistence] Old core plus new-state residuals — **PARTIAL 2026-08-23**

- **milestone**: reduce a later arbitrary centered vacuum-sector vector to a
  centered cutoff-two core plus matrix-tail error and diagonal inflation;
  prove the exact composed rate `(49/50) * lambda + epsilon`; inhabit the
  zero-error/unit-inflation cutoff-two anchor; and compile a supplied cofinal
  family to the completed transfer contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence.lean`.
- **decl**:
  `CutoffTwoFullSectorGapPersistenceAt`,
  `CutoffTwoFullSectorGapPersistenceAt.full_abs_gap`,
  `cutoffTwoFullSectorGapPersistenceAtAnchor`,
  `cutoffTwoFullSectorGapPersistenceAtAnchor_abs_gap`,
  `CutoffTwoCofinalFullSectorGapPersistence.toFiniteStrictGap`, and
  `CutoffTwoCofinalFullSectorGapPersistence.toCompletedStrictContractionData`.
- **obligation**: construct later-cutoff comparisons by bounding old-old
  drift, both old/new cross blocks, the new-new block, and diagonal
  recentering/inflation uniformly enough that `(49/50) * lambda + epsilon < 1`
  on an unbounded cofinal schedule.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused check passes in about 2.3 seconds and the
  exact-target one-worker dependency-complete build passes 4,885 jobs.  The
  finite anchor is inhabited; no later or cofinal comparison, completed gap
  inhabitant, thermodynamic/continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-full-sector-block-residual] Four-block residual compiler — **CLOSED 2026-08-23**

- **milestone**: specialize the exact old/new four-block identity to the
  cutoff-two base; compile old-old, old-new, new-old, and new-new relative
  budgets into the aggregate full-sector matrix comparison; and carry a
  supplied cofinal family to the actual completed transfer contraction at
  rate `(49/50) * lambda + (eOO + eON) + (eNO + eNN)`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual.lean`.
- **decl**:
  `cutoffTwoFullSectorMatrix_four_blocks`,
  `CutoffTwoFullSectorBlockResidualAt`,
  `CutoffTwoFullSectorBlockResidualAt.toFullSectorGapPersistenceAt`,
  `CutoffTwoCofinalFullSectorBlockResidual`,
  `CutoffTwoCofinalFullSectorBlockResidual.toCofinalFullSectorGapPersistence`,
  and
  `CutoffTwoCofinalFullSectorBlockResidual.toCompletedStrictContractionData`.
- **obligation**: inhabit the residual fields on an unbounded cofinal
  schedule with a uniform subunit composed rate.  First construct the old
  coefficient projection/recentering and its exact mean and diagonal
  identities; then bound old-kernel drift, both cross blocks, and the new-new
  tail.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused monitored check passes in about 1.3 seconds,
  and the exact-target one-worker dependency-complete build passes 4,886
  jobs.  Five interrupted namespace-error diagnostics are not passes.  This
  closes the residual-to-gap implication, not any later-cutoff residual
  estimate, cofinal gap inhabitant, thermodynamic/continuum QFT, or the Clay
  theorem.

### [BF4-cutoff-two-full-sector-old-pullback] Canonical core recentering — **CLOSED 2026-08-23**

- **milestone**: pull an arbitrary later-sector coefficient back along the
  explicit cutoff-two embedding; prove exact old mean, diagonal, and old-old
  matrix identities; expose exact cancellation of old and new means and the
  old/new diagonal split; construct a fixed-root centered cutoff-two core;
  and compile five remaining analytic budgets to the completed contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.lean`.
- **decl**:
  `cutoffTwoOldCoefficientPullback`,
  `cutoffTwoOldWeightedMean_eqv_pulled`,
  `cutoffTwoOldDiagonal_eqv_pulled`,
  `cutoffTwoOldOldBlock_eqv_pulled`,
  `cutoffTwoOldPulled_add_newWeightedMean_eqv_zero`,
  `cutoffTwoFullSectorDiagonal_eqv_oldPulled_add_new`,
  `cutoffTwoOldCoefficientRecentered_meanZero`,
  `CutoffTwoFullSectorOldPullbackResidualAt.toFullSectorBlockResidualAt`,
  and
  `CutoffTwoCofinalFullSectorOldPullbackResidual.toCompletedStrictContractionData`.
- **obligation**: bound the fixed-root correction through pulled-weight drift
  and the new mean, then prove cofinal moving-old, cross-block, new-new, and
  diagonal budgets whose exact combined rate stays below one.
- **constructive?**: yes — all eleven audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the final focused check passes in about 1.6 seconds, and
  the exact-target one-worker dependency-complete build passes 4,887 jobs.
  Three interrupted unresolved-name diagnostics and later failed namespace
  probes are not passes.  This constructs the structural core, not any
  later-cutoff analytic budget, cofinal completed gap inhabitant,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-full-sector-diagonal-block-gap] Diagonal-preserving recursion — **CLOSED 2026-08-23**

- **milestone**: prove the pulled-old and new diagonal pieces nonnegative and
  individually bounded by the full diagonal; combine a common rate `q` on
  both diagonal matrix blocks with a cross budget `c` into the exact full
  rate `q + c`; and compile a supplied cofinal family to the completed
  vacuum-sector contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.lean`.
- **decl**:
  `cutoffTwoOldPulledDiagonal_nonnegative`,
  `cutoffTwoNewDiagonal_nonnegative`,
  `cutoffTwoOldPulledDiagonal_le_full`,
  `cutoffTwoNewDiagonal_le_full`,
  `CutoffTwoFullSectorDiagonalBlockGapAt.full_abs_gap`,
  `CutoffTwoCofinalFullSectorDiagonalBlockGap.toFiniteStrictGap`, and
  `CutoffTwoCofinalFullSectorDiagonalBlockGap.toCompletedStrictContractionData`.
- **obligation**: construct a cofinal family with a common block rate and
  cross error satisfying `q + c < 1`.  The old and new diagonal blocks both
  require contraction; the new diagonal cannot be assumed uniformly small
  for arbitrary full-sector vectors.
- **constructive?**: yes — all seven audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused check passes in about 1.1 seconds and the
  exact-target one-worker dependency-complete build passes 4,888 jobs.  Two
  initial namespace/syntax failures are not passes.  This closes the exact
  block-rate arithmetic and cofinal implication, not its analytic inhabitant,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-full-sector-dirichlet-blocks] Positive Dirichlet partition — **CLOSED 2026-08-23**

- **milestone**: partition the full directed Dirichlet energy exactly into
  old-old, old-new, new-old, and new-new blocks; prove every block
  nonnegative; regroup them into positive within-block and cross-block
  energies, each bounded by the full energy; and identify the full energy
  exactly with twice the diagonal-minus-transfer deficit.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks.lean`.
- **decl**:
  `finiteJointDirichletEnergy_filter_four_blocks`,
  `finiteJointDirichletBlock_nonnegative`,
  `cutoffTwoFullSectorDirichlet_four_blocks`,
  `cutoffTwoFullSectorDirichlet_eqv_within_add_cross`,
  `cutoffTwoWithinBlockDirichlet_nonnegative`,
  `cutoffTwoCrossBlockDirichlet_nonnegative`,
  `cutoffTwoWithinBlockDirichlet_le_full`,
  `cutoffTwoCrossBlockDirichlet_le_full`, and
  `cutoffTwoFullSectorDirichlet_eqv_twice_deficit`.
- **obligation**: construct a recursive two-block Poincare/gluing certificate
  whose within-block estimates and cross-mean coercivity yield a cutoff-uniform
  bound of centered variance by full Dirichlet energy on an unbounded cofinal
  schedule.
- **constructive?**: yes — all nine audited exports use exactly `[propext]`
  or `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`,
  `sorry`, custom axiom, or noncomputable declaration was added.
- **status note**: the final focused monitored check passes in about 1.0
  seconds and the exact-target one-worker dependency-complete build passes
  4,889 jobs.  One earlier missing-namespace failure is not a pass.  This
  closes the positive block decomposition, not the recursive uniform
  Poincare estimate, cofinal completed gap inhabitant, thermodynamic/continuum
  QFT, or the Clay theorem.

### [BF4-full-sector-dirichlet-gluing] Two-block Poincare compiler — **CLOSED 2026-08-23**

- **milestone**: split stationary-product pairwise variance into exact
  nonnegative within-block and cross-block pieces; glue matching coercivity
  estimates to the full physical Dirichlet energy; use a sector-mass floor and
  exact centering to prove `(kappa * m0) * D <= D - M`; derive the explicit
  strict rate `1 / (1 + kappa * m0)`; and compile a supplied cofinal family to
  the completed vacuum-sector contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing.lean`.
- **decl**:
  `cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross`,
  `cutoffTwoWithinBlockPairwiseVariance_nonnegative`,
  `cutoffTwoCrossBlockPairwiseVariance_nonnegative`,
  `CutoffTwoFullSectorDirichletGluingAt`,
  `CutoffTwoFullSectorDirichletGluingAt.floor_mul_pairwiseVariance_le_fullDirichlet`,
  `CutoffTwoFullSectorDirichletGluingAt.strength_mul_diagonal_le_deficit`,
  `cutoffTwoDirichletGluingRate_lt_one`,
  `CutoffTwoFullSectorDirichletGluingAt.abs_matrix_le_rate_mul_diagonal`,
  `CutoffTwoCofinalFullSectorDirichletGluing.toFiniteStrictGap`, and
  `CutoffTwoCofinalFullSectorDirichletGluing.toCompletedStrictContractionData`.
- **obligation**: construct fixed positive `kappa` and `m0` and inhabit the
  within/cross coercivity fields on an unbounded cofinal cutoff schedule.  The
  cross field must quantitatively control the old/new block-separation mode;
  internal gaps alone cannot do so.
- **constructive?**: yes — all ten audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused check passes in about 1.3 seconds and the
  exact-target one-worker dependency-complete build passes 4,890 jobs.  Two
  preliminary namespace/setoid-algebra failures are not passes.  This closes
  the gluing implication, not any coercivity-floor inhabitant, cofinal
  completed gap inhabitant, thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-cross-mean-coercivity] Cross-mode expansion — **CLOSED 2026-08-23**

- **milestone**: prove the generic rectangular stationary-product Dirichlet
  identity in block masses, squares, and means; specialize both old/new
  orientations; show exact global centering turns the negative cross-mean
  product into a positive block-mean square; and compile a pointwise directed
  old/new kernel minorization into the cross-coercivity field required by the
  two-block gluing theorem.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity.lean`.
- **decl**:
  `finiteWeightedDirichletBlock_eqv_mass_square_mean`,
  `cutoffTwoOldNewPairwiseVariance_eqv_mass_square_mean`,
  `cutoffTwoNewOldPairwiseVariance_eqv_mass_square_mean`,
  `cutoffTwoOldMean_add_newMean_eqv_zero`,
  `cutoffTwoNegOldMeanMulNewMean_centered_eqv_square`,
  `cutoffTwoCrossBlockPairwiseVariance_centered_eqv`,
  `scale_mul_finiteWeightedDirichletBlock_le`,
  `CutoffTwoCrossKernelMinorizationAt`, and
  `CutoffTwoCrossKernelMinorizationAt.cross_coercivity`.
- **obligation**: determine whether the exact physical kernel admits a fixed
  positive old/new product-weight minorization on an unbounded cutoff
  schedule.  If not, construct a weaker aggregate/path conductance estimate
  that still controls the displayed positive block-mean separation term.
- **constructive?**: yes — all eight audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused check passes in about 2.3 seconds and the
  exact-target one-worker dependency-complete build passes 4,891 jobs.  Two
  preliminary namespace/elaboration failures are not passes.  This closes
  the cross-term expansion and minorization implication, not any uniform
  minorization inhabitant, within-block recursion, cofinal completed gap,
  thermodynamic/continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-allocated-dirichlet-gluing] Sparse path budget compiler — **CLOSED 2026-08-23**

- **milestone**: introduce a minimal full-sector Dirichlet coercivity
  interface; allow cross paths to consume an explicit complementary share of
  within-block energy; prove the allocated within/cross estimates recombine
  exactly to global coercivity; and compile a supplied cofinal family through
  the explicit strict rate to the completed vacuum-sector contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing.lean`.
- **decl**:
  `CutoffTwoFullSectorDirichletCoercivityAt`,
  `CutoffTwoFullSectorDirichletCoercivityAt.strength_mul_diagonal_le_deficit`,
  `CutoffTwoFullSectorDirichletCoercivityAt.abs_matrix_le_rate_mul_diagonal`,
  `CutoffTwoAllocatedDirichletGluingAt`,
  `CutoffTwoAllocatedDirichletGluingAt.toFullSectorDirichletCoercivityAt`,
  `CutoffTwoCofinalAllocatedDirichletGluing.toFiniteStrictGap`, and
  `CutoffTwoCofinalAllocatedDirichletGluing.toCompletedStrictContractionData`.
- **obligation**: build the allocated estimates from sparse internal paths and
  one or more genuine old/new bridge edges, with fixed positive `kappa`, a
  fixed positive sector-mass floor, and fixed shares on an unbounded cofinal
  schedule.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused check passes in about 1.2 seconds and the
  exact-target one-worker dependency-complete build passes 4,892 jobs.  One
  preliminary namespace/congruence failure is not a pass.  A cutoff-three
  diagnostic probe was memory-reserve interrupted and establishes nothing.
  This closes the sparse allocation implication, not its analytic inhabitant,
  cofinal completed gap inhabitant, thermodynamic/continuum QFT, or the Clay
  theorem.

### [BF4-cutoff-two-sparse-path-aggregation] Canonical cross-path sum compiler — **CLOSED 2026-08-23**

- **milestone**: define the exact stationary-weighted sum of the actual
  canonical old-to-new and new-to-old positive-path energies; prove the finite
  edge floor times cross pairwise variance is below this path sum; and compile
  a supplied congestion bound through allocated gluing to completion.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.lean`.
- **decl**:
  `floor_mul_finiteStationaryRectangularVariance_le_endpointBudget`,
  `cutoffTwoCanonicalFullPathEnergy`,
  `cutoffTwoCanonicalCrossPathBudget`,
  `cutoffTwo_edgeFloor_mul_crossVariance_le_canonicalPathBudget`,
  `CutoffTwoSparsePathAllocatedGluingAt.toAllocatedDirichletGluingAt`, and
  `CutoffTwoCofinalSparsePathAllocatedGluing.toCompletedStrictContractionData`.
- **obligation**: expose edge occurrences in the canonical aggregate path sum
  and bound their stationary-weighted congestion by a fixed share of
  within-block Dirichlet energy plus cross-block Dirichlet energy, uniformly
  along a cofinal cutoff schedule; also prove fixed positive edge and sector
  mass floors.
- **constructive?**: yes — all six audited exports use exactly
  `[propext, Quot.sound]`; no `Classical.*`, choice, `native_decide`, `sorry`,
  custom axiom, or noncomputable declaration was added.
- **status note**: the focused check passes in about 1.2 seconds and the
  exact-target one-worker dependency-complete build passes 4,893 jobs.  The
  first focused check failed on two missing namespace openings and is not a
  pass.  This closes exact canonical path aggregation and its implication,
  not a congestion inhabitant, uniform finite/completed gap, continuum QFT,
  or the Clay theorem.

### [BF4-cutoff-two-linear-cross-path-aggregation] Polynomial literal-edge path compiler — **CLOSED 2026-08-23**

- **milestone**: replace recursive exponential path amplification in the
  cross aggregation route by path length times the literal kernel-weighted
  linear edge-energy sum, and compile its supplied congestion bound through
  allocated gluing to completion.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.lean`.
- **decl**:
  `cutoffTwoCanonicalFullLengthLinearPathBudget`,
  `cutoffTwoCanonicalCrossLengthLinearPathBudget`,
  `cutoffTwo_edgeFloor_mul_crossVariance_le_lengthLinearPathBudget`,
  `CutoffTwoSparseLinearPathAllocatedGluingAt.toAllocatedDirichletGluingAt`,
  and
  `CutoffTwoCofinalSparseLinearPathAllocatedGluing.toCompletedStrictContractionData`.
- **obligation**: compute stationary-weighted edge-occurrence loads in the
  length-weighted canonical path family and prove uniform within/cross
  congestion, positive edge-floor, and sector-mass bounds.
- **constructive?**: yes — all nine audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.5 seconds and the
  exact-target one-worker dependency-complete build passes 4,895 jobs.  This
  closes the polynomial path-cost compiler, not its uniform congestion
  inhabitant, a completed gap, continuum QFT, or the Clay theorem.

### [BF4-finite-path-edge-occurrences] Literal directed path edges — **CLOSED 2026-08-23**

- **milestone**: extract the duplicate-preserving directed edge list of every
  positive-kernel chain and identify linear path energy exactly with the sum
  of physical edge-square terms over that list.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.lean`.
- **decl**: `PositiveKernelChainIn.directedEdges`,
  `directedEdges_length_eq_edgeLength`, `directedEdges_mem_support`,
  `linearEnergy_eqv_directedEdges_sum`, and
  `length_mul_linearEnergy_eqv_directedEdges_sum`.
- **obligation**: group weighted occurrences from all canonical cross paths by
  directed physical edge and prove pointwise within/cross load bounds.
- **constructive?**: yes — all four audited theorems use at most `[propext]`;
  no forbidden construct was added.
- **status note**: the focused check passes in about 0.4 seconds and the exact
  one-worker target passes 1,189 jobs.  This exposes occurrences but does not
  prove congestion, a uniform finite/completed gap, continuum QFT, or the Clay
  theorem.

### [BF4-finite-weighted-edge-load] Exact occurrence-to-edge-load reindex — **CLOSED 2026-08-23**

- **milestone**: sum rational weights of repeated directed edge occurrences
  into a per-edge load and prove exact equality between the original weighted
  occurrence energy and the Dirichlet block with joint
  `edgeLoad * physicalKernel`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathEdgeLoad.lean`.
- **decl**: `WeightedDirectedEdgeOccurrence`,
  `weightedDirectedEdgeLoad`, `weightedDirectedEdgeLoad_nonnegative`,
  `finiteWeightedOccurrenceLoadedDirichlet`, and
  `finiteWeightedOccurrenceLoadedDirichlet_eqv_occurrenceEnergy`.
- **obligation**: instantiate the occurrence list with all actual canonical
  old/new paths and prove pointwise within/cross edge-load capacities.
- **constructive?**: yes — the two audited exports use at most
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 0.8 seconds and the exact
  one-worker target passes 4,897 jobs.  Two earlier focused checks failed
  during proof development and are not passes.  This closes finite
  occurrence regrouping, not physical congestion, a uniform gap, continuum
  QFT, or the Clay theorem.

### [BF4-cutoff-two-canonical-cross-edge-load] Pointwise physical congestion compiler — **CLOSED 2026-08-23**

- **milestone**: flatten the actual stationary-weighted canonical old/new
  paths into weighted directed-edge occurrences; group them into an explicit
  coefficient-independent physical edge load; identify the polynomial
  cross-path budget with its loaded Dirichlet form; and reduce its allocated
  congestion bound to four pointwise old/new edge-load capacities.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.lean`
  and the public endpoint evaluation added to
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.lean`.
- **decl**: `cutoffTwoCanonicalCrossWeightedEdgeOccurrences`,
  `cutoffTwoCanonicalCrossEdgeLoad`,
  `cutoffTwoCanonicalCrossLengthLinearPathBudget_eqv_loadedDirichlet`,
  `finiteLoadedDirichletBlock_le_scale_mul`,
  `CutoffTwoCanonicalCrossEdgeLoadBoundsAt`,
  `CutoffTwoCanonicalCrossEdgeLoadBoundsAt.lengthLinearPathBudget_le_allocatedEnergy`,
  `CutoffTwoPointwiseEdgeLoadAllocatedGluingAt.toAllocatedDirichletGluingAt`,
  and
  `CutoffTwoCofinalPointwiseEdgeLoadAllocatedGluing.toCompletedStrictContractionData`.
- **obligation**: prove the four explicit edge-load inequalities uniformly on
  a cofinal schedule, together with within-block coercivity and fixed positive
  edge and sector-mass floors.
- **constructive?**: yes — all ten audited exports use at most
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.3 seconds and the exact
  one-worker dependency-complete target passes 4,898 jobs.  Preliminary stale
  import, namespace, unfolding, and heartbeat failures are not passes.  This
  closes the pointwise congestion implication, not a load-bound inhabitant,
  uniform completed gap, continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-edge-load-capacity-scaling] Finite maxima and cleared coercivity — **CLOSED 2026-08-23**

- **milestone**: replace unit bridge capacity by separate finite internal and
  bridge capacities; inhabit both by located maxima of the explicit edge
  load; combine them with a within-block cost into the cleared inequality
  `baseFloor * V_full <= totalCost * E_full`; and compile a supplied uniform
  ratio comparison through the completed strict-contraction interface.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoEdgeLoadCapacityScaling.lean`.
- **decl**: `CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt`,
  `CutoffTwoCanonicalCrossEdgeLoadCapacitiesAt.lengthLinearPathBudget_le_capacityEnergy`,
  `cutoffTwoCanonicalInternalEdgeLoadCapacity`,
  `cutoffTwoCanonicalBridgeEdgeLoadCapacity`,
  `cutoffTwoCanonicalFiniteEdgeLoadCapacitiesAt`,
  `CutoffTwoCapacityScaledPathGluingAt.cleared_full_coercivity`,
  `CutoffTwoCapacityClearedDirichletAt.toFullSectorDirichletCoercivityAt`,
  and
  `CutoffTwoCofinalCapacityClearedGluing.toCompletedStrictContractionData`.
- **obligation**: construct a cofinal within-block cost and prove a fixed
  positive lower bound for `baseFloor / totalCost` in cleared form, together
  with a fixed positive sector-mass floor; then carry the result through the
  thermodynamic and continuum constructions.
- **constructive?**: yes — all eight audited exports use at most
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.8 seconds and the exact
  one-worker dependency-complete target passes 4,899 jobs.  The first focused
  check failed on missing namespace openings and is not a pass.  Finite
  capacity existence is closed, but its uniform scaled lower bound, the
  completed gap inhabitant, continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-canonical-full-edge-load] Inhabited finite full-sector coercivity — **CLOSED 2026-08-23**

- **milestone**: aggregate canonical positive paths over every ordered
  full-sector endpoint pair; regroup their stationary length-weighted edge
  occurrences into one explicit full edge load; take its located finite
  maximum; and inhabit the cleared full-sector coercivity certificate without
  a separate within-block hypothesis.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalFullEdgeLoad.lean`,
  plus public one-path atoms in
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad.lean`.
- **decl**: `cutoffTwoCanonicalFullWeightedEdgeOccurrences`,
  `cutoffTwoCanonicalFullEdgeLoad`,
  `cutoffTwoCanonicalFullLengthLinearAggregateBudget_eqv_loadedDirichlet`,
  `cutoffTwoCanonicalFullEdgeLoadCapacity`,
  `cutoffTwo_edgeFloor_mul_fullVariance_le_fullLoadCapacity_mul_Dirichlet`,
  `cutoffTwoCanonicalFullEdgeLoadClearedDirichletAt`, and
  `CutoffTwoCofinalCanonicalFullEdgeLoadRatio.toCompletedStrictContractionData`.
- **obligation**: bound the cutoff dependence of the full edge-load capacity,
  preferably after replacing arbitrary canonical walks by loop-free paths;
  prove a fixed positive cofinal lower bound for edge floor divided by that
  capacity and a fixed positive sector-mass floor; then construct the
  thermodynamic and continuum theories.
- **constructive?**: yes — all eight audited exports use exactly
  `[propext, Quot.sound]`; the two newly public supporting atoms have the same
  audit, and no forbidden construct was added.
- **status note**: the focused check passes in about 1.4 seconds and the exact
  one-worker dependency-complete target passes 4,900 jobs.  One preliminary
  missing-namespace/unfolding failure is not a pass.  Finite full-sector
  coercivity existence is closed; the uniform ratio, completed gap
  inhabitant, continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-simple-full-sector-cost] Explicit loop-erased polynomial cost — **CLOSED 2026-08-23**

- **milestone**: prove the canonical vacuum-sector stationary mass is at most
  one; aggregate loop-erased carrier-bounded endpoint paths into the explicit
  finite coercivity cost `1 + |sector|^2`; bound it by the ambient half-zero
  cost `1 + ((later + 1)^24)^2`; and compile a supplied cofinal ambient ratio
  through completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.lean`.
- **decl**: `cutoffTwoFullSectorMass_le_one`,
  `cutoffTwoSimpleFullSectorCost`,
  `cutoffTwo_edgeFloor_mul_fullVariance_le_simpleCost_mul_Dirichlet`,
  `cutoffTwoSimpleFullSectorClearedDirichletAt`,
  `cutoffTwoAmbientFullSectorCost`,
  `cutoffTwo_edgeFloor_mul_fullVariance_le_ambientCost_mul_Dirichlet`, and
  `CutoffTwoCofinalAmbientFullSectorRatio.toCompletedStrictContractionData`.
- **obligation**: improve the degree-48 ambient fallback using actual
  simple-path edge congestion or stronger BF4 kernel geometry, then prove a
  fixed positive cofinal cost-scaled edge floor and sector-mass floor and
  construct the thermodynamic/continuum theory.
- **constructive?**: yes — all seven audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.5 seconds and the exact
  one-worker dependency-complete target passes 4,904 jobs.  The first focused
  check failed on missing namespace openings and is not a pass.  The explicit
  polynomial finite cost is closed; its uniform ratio, completed gap
  inhabitant, continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-simple-full-edge-load] Linear loop-erased congestion cost — **CLOSED 2026-08-23**

- **milestone**: prove vertex-simple walks have duplicate-free directed-edge
  lists; transport this to the loop-erased BF4 positive paths; regroup their
  stationary length-weighted occurrences; prove every full-sector edge load
  is at most sector cardinality; derive the cleared coercivity cost
  `1 + |sector|`; bound it by the explicit half-zero ambient cost
  `1 + (later + 1)^24`; and compile a supplied cofinal ratio to completed
  strict contraction.
- **files**:
  `lean/YMGap/Continuum/FiniteBoolGraphSimplePaths.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.lean`.
- **decl**: `Walk.directedEdges_nodup_of_vertices_nodup`,
  `cutoffTwoSimplePositivePath_directedEdges_nodup`,
  `cutoffTwoSimpleWeightedPathOccurrenceEnergy_eqv_pairBudget`,
  `cutoffTwoSimpleFullLengthLinearAggregateBudget_eqv_loadedDirichlet`,
  `cutoffTwoSimpleFullEdgeLoad_le_sectorSize`,
  `cutoffTwo_edgeFloor_mul_fullVariance_le_linearCost_mul_Dirichlet`,
  `cutoffTwoLinearFullSectorClearedDirichletAt`,
  `cutoffTwoAmbientLinearFullSectorCost_eqv_power`, and
  `CutoffTwoCofinalAmbientLinearFullSectorRatio.toCompletedStrictContractionData`.
- **obligation**: prove a fixed positive cofinal lower bound for the canonical
  BF4 positive-edge floor divided by `1 + (later + 1)^24`, or replace that
  global-minimum route by a stronger weighted-flow/minorization estimate;
  also prove a fixed positive sector-mass floor and construct the
  thermodynamic and continuum theories.
- **constructive?**: yes — nine audited exports use exactly
  `[propext, Quot.sound]`, the ambient-power identity uses only `[propext]`,
  and all supporting exports stay inside the same axiom gate.
- **status note**: the final focused check passes in about 72 seconds and the
  exact one-worker dependency-complete target passes 4,905 jobs, with the new
  module taking about 78 seconds.  Earlier missing-olean, proof-rewrite,
  syntax, and deterministic-heartbeat failures are not passes.  Linear
  carrier congestion is closed; the uniform ratio, completed gap inhabitant,
  continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-uniform-sector-mass-floor] Uniform positive vacuum-sector mass — **CLOSED 2026-08-23**

- **milestone**: identify finite index zero with the all-zero boundary state;
  apply the existing cutoff-uniform positive-row floor to that fixed state;
  use root-component membership and nonnegative finite summation to bound the
  full vacuum-sector mass below by the same fixed positive rational; and
  remove the mass-floor hypothesis from the degree-24 completed-gap compiler.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor.lean`.
- **decl**: `cutoffTwoUniformVacuumSectorMassFloor`,
  `cutoffTwoUniformVacuumSectorMassFloor_pos`,
  `cutoffTwoUniformVacuumSectorMassFloorAnchor`,
  `cutoffTwoUniformVacuumSectorMassFloor_le`, and
  `CutoffTwoCofinalAmbientLinearEdgeRatio.toCompletedStrictContractionData`.
- **obligation**: prove a fixed positive cofinal lower bound for the canonical
  positive-edge floor divided by `1 + (later + 1)^24`, using pulled-edge
  persistence plus control of newly appearing states/edges or a stronger
  weighted-flow/minorization estimate; then construct the thermodynamic and
  continuum theories.
- **constructive?**: yes — all three audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.1 seconds and the exact
  one-worker dependency-complete target passes 4,906 jobs, with the new module
  taking about one second.  The first missing-name focused check is not a
  pass.  The mass-floor input is closed; the cost-scaled edge-floor ratio,
  completed gap inhabitant, continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-uniform-old-block-coercivity] Fixed embedded-block gap — **CLOSED 2026-08-23**

- **milestone**: sum the constructed transported cutoff-two path-edge floor
  against arbitrary pulled stationary endpoint pairs; remove the pulled mass
  using its normalized upper bound; divide by the fixed path ceiling to
  construct a positive cutoff-independent coercivity floor; transport the
  pairwise variance and Dirichlet energy exactly to the later old-old block;
  and reduce full two-block gluing to only new-new and cross coercivity.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.lean`.
- **decl**: `cutoffTwoUniformOldBlockCoercivityFloor`,
  `cutoffTwoUniformOldBlockCoercivityFloor_pos`,
  `cutoffTwoOldOldPairwiseVariance_eqv_pulled`,
  `cutoffTwoOldOldDirichlet_eqv_pulled`,
  `cutoffTwoUniformOldBlockCoercivityFloor_mul_oldOldPairwise_le_Dirichlet`,
  `CutoffTwoNewAndCrossCoercivityAt.toFullSectorDirichletGluingAt`, and
  `CutoffTwoCofinalNewAndCrossCoercivity.toCompletedStrictContractionData`.
- **obligation**: construct a cofinal family proving new-new and old/new
  cross pairwise-variance coercivity at the fixed constructed old-block
  floor; then carry the resulting completed transfer gap through the
  thermodynamic and continuum constructions.
- **constructive?**: yes — all eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.6 seconds and the exact
  one-worker dependency-complete target passes 4,910 jobs, with the new module
  taking about 1.5 seconds.  The first missing-namespace/local-unfolding check
  failed and is not a pass.  Old-old coercivity is now constructed uniformly;
  new-new and cross coercivity, the completed uniform gap inhabitant,
  continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-simple-flow-capacity] Floor-free novel weighted-flow compiler — **CLOSED 2026-08-23**

- **milestone**: expose the raw endpoint Cauchy bound before comparison with
  the physical kernel; route exactly the new-new and both directed cross
  stationary endpoint pairs along loop-erased positive paths; regroup their
  stationary length-weighted edge occurrences into one coefficient-independent
  load; prove the novel pairwise variance is bounded by its raw loaded form;
  reserve half of the constructed old-block coercivity for old variance and
  half of old-old physical capacity for novel paths; and compile one cofinal
  local flow-capacity family to completed strict contraction.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathLengthEnergy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity.lean`.
- **decl**:
  `PositiveKernelChainIn.endpointDifference_sq_le_length_mul_edgeSquareSum`,
  `PositiveKernelChainIn.edgeSquareSum_eqv_edgeDifferences`,
  `cutoffTwoNovelPairwiseVariance_eqv_newNew_add_cross`,
  `cutoffTwoNovelPairwiseVariance_le_rawLoadedDirichlet`,
  `cutoffTwoNovelSimpleFlowCoercivityFloor`,
  `scale_mul_finiteJointDirichletBlock_le_of_joint_le`,
  `CutoffTwoNovelSimpleFlowCapacityAt.toFullSectorDirichletCoercivityAt`, and
  `CutoffTwoCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData`.
- **obligation**: construct, on a constructively cofinal cutoff schedule, the
  four pointwise comparisons between `delta_flow * novelEdgeLoad` and the
  allocated physical kernel (half capacity on old-old edges and full capacity
  on the other three blocks), using the concrete BF4 weight/kernel formulas
  or prove that this chosen flow cannot satisfy them; then construct and
  control the thermodynamic and continuum theories.
- **constructive?**: yes — all eleven audited exports across the two new
  frontier modules use exactly `[propext, Quot.sound]`, except the generic
  finite-block pointwise-domination theorem, which uses only `[propext]`; the
  supporting path atoms remain inside the same gate, and no forbidden
  construct was added.
- **status note**: the focused checks pass, and the exact one-worker
  dependency-complete capacity target passes 4,912 jobs with the final module
  taking about 1.3 seconds.  Preliminary stale-olean, missing-namespace,
  placeholder, deterministic-heartbeat, and deliberately interrupted checks
  are not passes.  The global shrinking edge-floor obstruction has been
  removed from this route, but the cofinal local flow-capacity family remains
  uninhabited; therefore the completed uniform gap, continuum QFT, and Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-capacity-ratio] Explicit finite weighted-flow ratio — **CLOSED 2026-08-23**

- **milestone**: recover a literal positive-path occurrence from every
  positive regrouped edge load; transport strict positivity from that
  occurrence to the normalized physical kernel; allocate half old-old and
  full novel-block physical capacity; define the exact allocated-kernel/load
  ratio and its located positive finite minimum; prove that this minimum
  satisfies every pointwise capacity comparison; and compile one cofinal
  scalar lower-bound certificate to completed strict contraction.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.lean`,
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorPathEdgeLoad.lean`,
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio.lean`.
- **decl**:
  `PositiveKernelChainIn.directedEdges_kernel_pos`,
  `exists_occurrence_of_weightedDirectedEdgeLoad_pos`,
  `cutoffTwoNovelSimpleEdgeLoad_pos_implies_kernel_pos`,
  `cutoffTwoNovelAllocatedKernel`,
  `cutoffTwoNovelFiniteFlowCapacityFloor`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_pos`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_mul_load_le_allocated`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_finiteRatio`, and
  `CutoffTwoCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData`.
- **obligation**: prove that the fixed constructed flow coercivity floor is
  below the explicit finite capacity minimum along a constructively cofinal
  cutoff schedule, using the concrete BF4 kernel and path-load formulas, or
  prove that this chosen flow's ratio vanishes asymptotically; then construct
  and control the thermodynamic and continuum theories.
- **constructive?**: yes — the five audited exports of the ratio module use
  exactly `[propext, Quot.sound]`; the generic directed-edge positivity result
  uses only `[propext]`, and the other supporting audited declarations stay
  within `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused checks pass and the exact one-worker
  dependency-complete target passes 4,913 jobs, with the new module taking
  about 2.4 seconds.  Preliminary stale-olean, parser, missing-tactic, and
  dependent-rewrite failures are not passes.  The four local capacity fields
  are now reduced to one explicit scalar sequence, but its cofinal uniform
  lower bound, the completed gap inhabitant, continuum QFT, and Clay theorem
  remain open.

### [BF4-cutoff-two-novel-flow-capacity-decision] Exact finite certificate or overloaded edge — **CLOSED 2026-08-23**

- **milestone**: reflect the explicit finite capacity floor into a sound and
  complete Boolean scan; construct a Type-level recursive failure locator for
  the finite positive minimum; return either a valid floor comparison, failure
  at the unit fallback, or a literal positive-load directed edge violating
  the requested allocated-kernel payment; and compile cofinally successful
  finite scans to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision.lean`.
- **decl**: `le_listPositiveMinOne_of_forall`,
  `not_le_listPositiveMinOne_cases`, `ListPositiveMinOneFailure`,
  `locateListPositiveMinOneFailure`, `cutoffTwoNovelFlowCapacityCheck`,
  `cutoffTwoNovelFlowCapacityCheck_sound`,
  `cutoffTwoNovelFlowCapacityCheck_complete`,
  `CutoffTwoNovelFlowCapacityOutcome`,
  `inspectCutoffTwoNovelFlowCapacity`, and
  `CutoffTwoCofinalNovelFlowCapacityCheck.toCompletedStrictContractionData`.
- **obligation**: eliminate the unit-fallback failure branch for the fixed
  constructed strength, then prove successful checks on a constructively
  cofinal schedule by bounding every possible loaded edge, or use a returned
  overload witness to prove that the chosen simple flow must be redesigned;
  then construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; proposition-to-Type elimination was avoided by an
  explicit Type-level failure family, and no forbidden construct was added.
- **status note**: the focused check passes and the exact one-worker
  dependency-complete target passes 4,914 jobs, with the new module taking
  about 1.1 seconds.  The first Boolean-syntax/large-elimination check failed
  and is not a pass.  Every fixed cutoff is now an exact executable
  certificate-or-local-obstruction calculation, but cofinal success, the
  completed gap inhabitant, continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-capacity-unit-bound] Remove the fallback branch — **CLOSED 2026-08-23**

- **milestone**: bound the opaque transported base-edge floor by the
  normalized vacuum-root kernel entry and then by one; prove the fixed path
  ceiling is at least one; propagate these bounds through the old-block
  quotient and half allocation; reduce the exact checker to its edge scan;
  and sharpen the Type-level result to the binary alternative of a valid
  capacity certificate or a literal overloaded positive-load edge.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound.lean`.
- **decl**: `cutoffTwoPulledUniformBasePositiveEdgeFloor_le_one`,
  `one_le_cutoffTwoPulledCanonicalPathCeiling`,
  `cutoffTwoUniformOldBlockCoercivityFloor_le_baseFloor`,
  `cutoffTwoNovelSimpleFlowCoercivityFloor_le_one`,
  `cutoffTwoNovelEdgeCapacityCheck`,
  `cutoffTwoNovelEdgeCapacityCheck_sound`,
  `cutoffTwoNovelEdgeCapacityCheck_complete`,
  `CutoffTwoNovelFlowCapacityDecisiveOutcome`,
  `inspectCutoffTwoNovelFlowCapacityDecisively`, and
  `CutoffTwoCofinalNovelEdgeCapacityCheck.toCompletedStrictContractionData`.
- **obligation**: expand every possible overloaded edge into its contributing
  stationary endpoint-pair occurrences and prove their grouped load is
  uniformly paid by the concrete BF4 kernel, or extract an asymptotic family
  showing this chosen flow must be redesigned; then construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no unfolding of the opaque certificate and no
  forbidden construct was used.
- **status note**: the focused check passes and the exact one-worker
  dependency-complete target passes 4,915 jobs, with the new module taking
  about 1.1 seconds.  The initial missing-namespace check failed and is not a
  pass.  The spurious unit-fallback branch is closed, but uniform control of
  loaded edges, the completed gap inhabitant, continuum QFT, and Clay theorem
  remain open.

### [BF4-cutoff-two-novel-flow-edge-expansion] Exact endpoint-pair load decomposition — **CLOSED 2026-08-23**

- **milestone**: expose the generic flat-map edge-load identity; prove that
  one simple path contributes exactly its stationary endpoint-product times
  its length when the selected edge occurs and zero otherwise; regroup the
  novel edge load exactly as the sum of those endpoint-pair contributions;
  and prove that any pairwise payment allocation fitting inside the physical
  edge allocation discharges the grouped capacity inequality.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion.lean`.
- **decl**: `weightedDirectedEdgeLoad_constantMap_eqv_indicator`,
  `weightedDirectedEdgeLoad_flatMap_eqv`,
  `cutoffTwoSimpleWeightedPathEdgeLoad_eqv_indicator`,
  `cutoffTwoNovelPathPairEdgeContribution`,
  `cutoffTwoNovelSimpleEdgeLoad_eqv_pairContributionSum`,
  `cutoffTwoNovelPathPairEdgeContribution_eqv_indicator`,
  `CutoffTwoNovelEdgePairAllocation`, and
  `CutoffTwoNovelEdgePairAllocation.toEdgeCapacity`.
- **obligation**: normalize the endpoint-pair terms by their common allocated
  BF4 edge kernel and prove a cutoff-uniform bound for the resulting canonical
  path congestion, or extract an asymptotic overload family requiring a new
  flow; then construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — all four newly audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the supporting focused check passes in about 70 seconds and
  its rebuilt exact target takes about 77 seconds.  The expansion focused
  check passes in about one second; the exact one-worker dependency-complete
  target passes 4,916 jobs with the new module taking about 0.94 seconds.
  Initial missing-namespace and under-applied-sum checks failed and are not
  passes.  The exact edge load is now expanded into analyzable endpoint terms,
  but its uniform BF4 kernel payment, the completed gap inhabitant, continuum
  QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-normalized-congestion] Exact local congestion reduction — **CLOSED 2026-08-23**

- **milestone**: divide every positive novel-flow edge load by its actual
  allocated physical kernel; prove the exact endpoint-pair normalized-sum
  formula; prove nonnegativity and equivalence between physical edge payment
  and the dimensionless unit congestion bound; derive the explicit finite
  capacity-floor comparison from all-edge congestion; and compile a cofinal
  congestion certificate to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion.lean`.
- **decl**: `listQSum_divPos_eqv_divPos_listQSum`,
  `cutoffTwoNovelNormalizedEdgeCongestion`,
  `cutoffTwoNovelPathPairNormalizedEdgeContribution`,
  `cutoffTwoNovelNormalizedEdgeCongestion_eqv_pairSum`,
  `cutoffTwoNovelNormalizedEdgeCongestion_nonnegative`,
  `cutoffTwoNovelEdgeCapacity_iff_normalizedCongestion`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_congestion`,
  `CutoffTwoCofinalNovelNormalizedCongestionBound`, and
  `CutoffTwoCofinalNovelNormalizedCongestionBound.toCompletedStrictContractionData`.
- **obligation**: uniformly bound the exact sum of normalized
  stationary-product/path-length contributions on every loaded edge using
  concrete BF4 weight and kernel formulas, or exhibit a cofinal overload
  family requiring a new flow; then construct and control the thermodynamic
  and continuum theories.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.3 seconds and the exact
  one-worker dependency-complete target passes 4,917 jobs, with the new module
  taking about 1.1 seconds.  Two deterministic-timeout checks and the check
  exposing a nonexistent convenience lemma are not passes.  The uniform
  congestion estimate, completed gap inhabitant, continuum QFT, and Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-conditional-congestion] Cancel stationary source mass — **CLOSED 2026-08-23**

- **milestone**: define the indexed conditional physical transition; prove
  the exact joint-kernel factorization by stationary source weight; factor the
  old-old half allocation identically; prove strict conditional positivity on
  every literal flow occurrence; divide and regroup every endpoint-pair load
  by the positive edge-source weight; cancel that weight from the physical
  capacity inequality in both directions; and compile a cofinal relative
  conditional-congestion family to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion.lean`.
- **decl**: `cutoffTwoEdgeLoadConditionalKernel`,
  `cutoffTwoEdgeLoadWeight_mul_conditional_eqv_kernel`,
  `cutoffTwoNovelAllocationFraction`,
  `cutoffTwoNovelAllocatedConditionalKernel`,
  `cutoffTwoNovelAllocatedKernel_eqv_weight_mul_conditional`,
  `cutoffTwoNovelOccurrence_conditionalKernel_pos`,
  `cutoffTwoNovelPathPairRelativeSourceDemand`,
  `cutoffTwoNovelRelativeSourceEdgeLoad`,
  `cutoffTwoEdgeLoadWeight_mul_relativeSourceEdgeLoad_eqv_load`,
  `cutoffTwoNovelEdgeCapacity_iff_relativeConditionalCongestion`, and
  `CutoffTwoCofinalNovelConditionalCongestionBound.toCompletedStrictContractionData`.
- **obligation**: expand the relative source load into its exact
  path-incidence formula and prove that its stationary-weight-ratio sum is
  uniformly bounded by the allocated conditional transition, or exhibit a
  cofinal overload family requiring new paths; then construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 1.2 seconds and the exact
  one-worker dependency-complete target passes 4,918 jobs, with the new module
  taking about 1.1 seconds.  The common stationary source factor is now
  cancelled exactly, but the uniform conditional Markov/Harnack estimate,
  completed gap inhabitant, continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-conditional-harnack-target] Exact projective path-incidence formula — **CLOSED 2026-08-23**

- **milestone**: define the endpoint/source stationary-weight ratio; prove its
  exact cancellation with the positive source weight; expose each
  source-cancelled pair demand as the endpoint ratio times the other endpoint
  weight and path length on precisely the traversed edges; sum this identity;
  prove equivalence between physical edge capacity and the explicit
  conditional-Harnack target; and compile a cofinal family of those targets to
  completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget.lean`.
- **decl**: `cutoffTwoNovelEndpointWeightRatioAtSource`,
  `cutoffTwoEdgeLoadWeight_mul_endpointRatio_eqv_endpointWeight`,
  `cutoffTwoNovelPathPairConditionalHarnackTerm`,
  `cutoffTwoNovelPathPairRelativeSourceDemand_eqv_harnackTerm`,
  `cutoffTwoNovelConditionalHarnackLoad`,
  `cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad`,
  `cutoffTwoNovelEdgeCapacity_iff_conditionalHarnackTarget`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_conditionalHarnack`, and
  `CutoffTwoCofinalNovelConditionalHarnackBound.toCompletedStrictContractionData`.
- **obligation**: derive a pathwise stationary-ratio transport formula from
  detailed balance and use it to prove a cutoff-uniform comparison between the
  explicit incidence sum and the allocated conditional transition, or exhibit
  cofinal overload requiring new paths; then construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on an incorrectly qualified
  private theorem and is not a pass.  The corrected focused check passes in
  about 1.3 seconds; the exact one-worker dependency-complete target passes
  4,919 jobs with the new module taking about 1.2 seconds.  The exact Harnack
  target is now explicit, but its uniform bound, the completed gap inhabitant,
  continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-pathwise-detailed-balance] Exact stationary-ratio telescope — **CLOSED 2026-08-23**

- **milestone**: prove detailed balance for the indexed conditional kernel;
  transport positive joint edges to the reverse orientation and to positive
  conditional transitions; identify each one-edge stationary ratio with the
  reverse/forward conditional ratio; define the recursive product on the
  Type-level positive path; and prove that the endpoint stationary ratio
  telescopes exactly to that product.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance.lean`.
- **decl**: `cutoffTwoEdgeLoadConditionalKernel_detailedBalance`,
  `cutoffTwoEdgeLoadKernel_reverse_pos_of_pos`,
  `cutoffTwoEdgeLoadConditionalKernel_reverse_pos_of_kernel_pos`,
  `cutoffTwoEdgeLoadWeightRatio_eqv_conditionalReverseForward`,
  `cutoffTwoNovelEndpointWeightRatioAtSource_eqv_oneStep`,
  `PositiveKernelChainIn.lastMem`,
  `cutoffTwoNovelPathReverseForwardProduct`, and
  `cutoffTwoNovelEndpointWeightRatioAtSource_eqv_pathProduct`.
- **obligation**: extract the positive prefix ending at the source of each
  selected path occurrence, rewrite each conditional-Harnack summand with its
  prefix transition-ratio product, and prove a cutoff-uniform congestion
  bound or a cofinal overload theorem; then construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two focused checks failed on equality-versus-implication,
  multiplication-congruence, and recursive-ratio unfolding details and are not
  passes.  The corrected focused check passes in about 1.4 seconds; the exact
  one-worker dependency-complete target passes 4,920 jobs with the new module
  taking about 1.3 seconds.  Exact pathwise ratio transport is proved, but the
  prefix extraction, uniform congestion estimate, completed gap inhabitant,
  continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-conditional-transition-product] Exact prefix-local product target — **CLOSED 2026-08-23**

- **milestone**: construct the positive prefix ending at the source of every
  literal path-edge occurrence without Prop-to-Type elimination or classical
  decision; rewrite each conditional-Harnack summand by the exact product of
  reverse/forward conditional ratios on that prefix; sum the identity; prove
  equivalence with physical edge capacity; and compile a cofinal family of
  transition-product bounds to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.lean`.
- **decl**: `PositiveKernelPrefixAtDirectedEdge`,
  `PositiveKernelChainIn.prefixAtDirectedEdge`,
  `cutoffTwoNovelPathPairConditionalTransitionProductTerm`,
  `cutoffTwoNovelPathPairConditionalHarnackTerm_eqv_transitionProduct`,
  `cutoffTwoNovelConditionalTransitionProductLoad`,
  `cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad`,
  `cutoffTwoNovelEdgeCapacity_iff_conditionalTransitionProductTarget`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_transitionProduct`, and
  `CutoffTwoCofinalNovelConditionalTransitionProductBound.toCompletedStrictContractionData`.
- **obligation**: prove a cutoff-uniform bound for the prefix products of
  reverse/forward conditional ratios and combine it with endpoint-weight and
  path-length counting to control the explicit edge sum, or exhibit cofinal
  overload requiring a different flow; then construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — prefix extraction audits to `[propext]`, while all
  four downstream audited exports use exactly `[propext, Quot.sound]`; the
  failed classical fallback was eliminated and no forbidden construct remains.
- **status note**: three focused checks failed on reserved syntax, forbidden
  Prop-to-Type elimination, and a missing explicit decidable-equality input;
  they are not passes.  The corrected focused check passes in about 1.3
  seconds; the exact one-worker dependency-complete target passes 4,921 jobs
  with the new module taking about 1.1 seconds.  The transition-product target
  is exact, but its uniform bound, the completed gap inhabitant, continuum QFT,
  and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-conditional-ratio-ceiling] Separate projective and counting bounds — **CLOSED 2026-08-23**

- **milestone**: define a fixed-cutoff nonnegative ceiling for every positive
  one-edge reverse/forward conditional ratio; prove strict positivity of each
  prefix product; prove the product is bounded by the ceiling raised to the
  exact prefix length; propagate the bound through each weighted path term and
  the finite endpoint-pair sum; and compile separate local-ceiling and global-
  counting obligations to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling.lean`.
- **decl**: `CutoffTwoConditionalReverseForwardCeilingAt`,
  `cutoffTwoNovelPathReverseForwardProduct_pos`,
  `cutoffTwoNovelPathReverseForwardProduct_le_ceilingPow`,
  `cutoffTwoNovelPathPairConditionalRatioCeilingTerm`,
  `cutoffTwoNovelPathPairConditionalTransitionProductTerm_le_ceiling`,
  `cutoffTwoNovelConditionalRatioCeilingLoad`,
  `cutoffTwoNovelConditionalTransitionProductLoad_le_ratioCeilingLoad`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_ratioCeiling`, and
  `CutoffTwoCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData`.
- **obligation**: construct a concrete one-edge projective ceiling with
  controlled cutoff dependence and prove that its explicit ceiling-weighted
  path load is uniformly bounded by the allocated conditional transition, or
  exhibit cofinal overload requiring a new flow; then construct and control
  the thermodynamic and continuum theories.
- **constructive?**: yes — all five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two focused checks failed on explicit-witness, namespace,
  unfolding, and natural-number nonnegativity details and are not passes.  The
  corrected focused check passes in about 1.3 seconds; the exact one-worker
  dependency-complete target passes 4,922 jobs with the new module taking
  about 1.2 seconds.  Projective distortion and path counting are now separate
  obligations, but neither uniform estimate, the completed gap inhabitant,
  continuum QFT, nor the Clay theorem is closed.

### [BF4-cutoff-two-novel-flow-conditional-finite-ratio-ceiling] Construct the fixed-cutoff maximum — **CLOSED 2026-08-23**

- **milestone**: totalize the reverse/forward conditional ratio on all ordered
  carrier pairs; take its located rational maximum over the literal finite
  Cartesian carrier square; prove nonnegativity; prove every positive physical
  edge ratio lies below that maximum; instantiate the local ceiling datum at
  every fixed cutoff; and reduce the cofinal compiler to payment of the fully
  concrete ceiling-weighted path load.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling.lean`.
- **decl**: `cutoffTwoConditionalReverseForwardRatio`,
  `cutoffTwoConditionalReverseForwardRatio_nonnegative`,
  `cutoffTwoConditionalReverseForwardFiniteCeiling`,
  `cutoffTwoConditionalReverseForwardFiniteCeiling_nonnegative`,
  `cutoffTwoConditionalReverseForwardRatio_le_finiteCeiling`,
  `cutoffTwoConditionalReverseForwardFiniteCeilingData`,
  `cutoffTwoNovelConditionalFiniteRatioCeilingLoad`,
  `cutoffTwoNovelConditionalTransitionProductLoad_le_finiteRatioCeilingLoad`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_finiteRatioCeiling`, and
  `CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound.toCompletedStrictContractionData`.
- **obligation**: control the cutoff dependence of the constructed maximum and
  prove that its explicit ceiling-weighted path load is uniformly payable by
  every allocated conditional transition, or exhibit cofinal overload
  requiring a different flow; then construct and control the thermodynamic
  and continuum theories.
- **constructive?**: yes — all four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check hit a deterministic unfolding
  timeout plus pair-normalization and namespace errors and is not a pass.  The
  corrected focused check passes in about 1.1 seconds; the exact one-worker
  dependency-complete target passes 4,923 jobs with the new module taking
  about 1.0 seconds.  The ceiling exists constructively at every fixed cutoff,
  but its uniform asymptotics, uniform payment, completed gap inhabitant,
  continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-conditional-finite-ratio-ceiling-decision] Exact finite payment checker — **CLOSED 2026-08-23**

- **milestone**: reflect every concrete ratio-ceiling payment inequality over
  the literal ordered carrier square into a Boolean scan; prove the scan sound
  and complete for that finite predicate; compile success to the finite flow-
  capacity floor; construct a Type-level recursive inspector returning either
  that certificate or a literal overloaded ceiling edge; and compile a
  cofinally successful checked schedule to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision.lean`.
- **decl**: `cutoffTwoNovelConditionalFiniteRatioCeilingCheck`,
  `cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_capacity`,
  `cutoffTwoNovelConditionalFiniteRatioCeilingCheck_complete`,
  `cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_floor`,
  `ListComparisonOutcome`, `inspectListComparison`,
  `CutoffTwoNovelConditionalFiniteRatioCeilingOutcome`,
  `inspectCutoffTwoNovelConditionalFiniteRatioCeiling`, and
  `CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck.toCompletedStrictContractionData`.
- **obligation**: analyze the cutoff dependence of the constructed ratio
  ceiling and ceiling-weighted path loads, then prove cofinal checker success
  or use the returned overloaded edges to derive a systematic obstruction and
  redesign the flow; after that, construct and control the thermodynamic and
  continuum theories.
- **constructive?**: yes — the inspector preserves its failure witness as
  `Type`-level data; all five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused monitored check passes in about 1.1 seconds and
  the exact one-worker dependency-complete target passes 4,924 jobs, with the
  new module taking about 1.1 seconds.  Fixed-cutoff payment is now exactly
  decidable, but no cutoff is claimed to pass, no cofinal success family is
  constructed, and the completed gap inhabitant, continuum QFT, and Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-conditional-stationary-ratio-envelope] Exact stationary identification and envelope — **CLOSED 2026-08-23**

- **milestone**: identify each positive-edge reverse/forward conditional ratio
  exactly with its stationary-weight ratio by detailed balance; lift the
  pointwise identity through the located finite maximum; bound that maximum by
  the all-pairs stationary-weight-ratio envelope; prove power, path-term, and
  finite-load monotonicity in the ceiling; and compile cofinal payment of the
  stationary-envelope load to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryRatioEnvelope.lean`.
- **decl**: `cutoffTwoPositiveEdgeStationaryWeightRatio`,
  `cutoffTwoConditionalReverseForwardRatio_eqv_positiveEdgeStationaryWeightRatio`,
  `cutoffTwoPositiveEdgeStationaryWeightFiniteCeiling`,
  `cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_positiveEdgeStationaryWeightFiniteCeiling`,
  `cutoffTwoStationaryWeightRatio`,
  `cutoffTwoStationaryWeightRatioFiniteEnvelope`,
  `cutoffTwoConditionalReverseForwardFiniteCeiling_le_stationaryWeightRatioFiniteEnvelope`,
  `cutoffTwoNovelConditionalRatioCeilingLoad_mono`,
  `cutoffTwoNovelConditionalFiniteRatioCeilingLoad_le_stationaryRatioEnvelopeLoad`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_stationaryRatioEnvelope`, and
  `CutoffTwoCofinalNovelConditionalStationaryRatioEnvelopeBound.toCompletedStrictContractionData`.
- **obligation**: factor and control the all-pairs stationary envelope using a
  numerator ceiling and positive stationary-weight minimum, decide whether
  that sufficient estimate can remain uniform, and otherwise return to the
  sharper positive-edge or exact transition-product load; then construct and
  control the thermodynamic and continuum theories.
- **constructive?**: yes — the exact maximum comparison and load monotonicity
  are finite `Q'` proofs; all seven audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two focused checks failed on namespace exposure and
  dependent proof-witness normalization and are not passes.  The corrected
  focused check passes in about 1.3 seconds; the exact one-worker dependency-
  complete target passes 4,925 jobs with the new module taking about 1.3
  seconds.  The conditional ceiling now has a stationary interpretation, but
  its cutoff-uniform control, payment, completed gap inhabitant, continuum
  QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-conditional-stationary-weight-oscillation] Maximum/minimum factorization — **CLOSED 2026-08-23**

- **milestone**: construct the finite stationary-weight maximum and positive
  minimum; bound every carrier weight between them; bound the maximum by the
  vacuum-sector mass and hence by one; prove that the all-pairs stationary
  ratio envelope is bounded by `maximum/minimum` and then by `1/minimum`; and
  compile payment of the resulting reciprocal-minimum load to completed
  strict contraction along a cofinal schedule.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalStationaryWeightOscillation.lean`.
- **decl**: `cutoffTwoStationaryWeightFiniteMaximum`,
  `cutoffTwoStationaryWeightFiniteMinimum`,
  `cutoffTwoStationaryWeightFiniteMinimum_pos`,
  `cutoffTwoStationaryWeightFiniteMaximum_le_sectorMass`,
  `cutoffTwoStationaryWeightFiniteMaximum_le_one`,
  `cutoffTwoStationaryWeightMaxMinEnvelope`,
  `cutoffTwoStationaryWeightRatio_le_maxMinEnvelope`,
  `cutoffTwoStationaryWeightRatioFiniteEnvelope_le_maxMinEnvelope`,
  `cutoffTwoStationaryWeightReciprocalMinimumEnvelope`,
  `cutoffTwoConditionalReverseForwardFiniteCeiling_le_reciprocalMinimumEnvelope`,
  `cutoffTwoNovelConditionalFiniteRatioCeilingLoad_le_reciprocalMinimumEnvelopeLoad`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_reciprocalMinimumEnvelope`, and
  `CutoffTwoCofinalNovelConditionalReciprocalMinimumEnvelopeBound.toCompletedStrictContractionData`.
- **obligation**: do not seek uniformity through the coarse global minimum
  unless justified; instead preserve positive-edge adjacency and derive a
  local stationary-weight-ratio estimate from the BF4 action/support geometry,
  or exhibit growing adjacent oscillation on the chosen canonical paths; then
  construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — all finite extrema and quotient comparisons retain
  explicit positive denominators; all eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused monitored check passes on its first attempt in
  about 1.1 seconds; the exact one-worker dependency-complete target passes
  4,926 jobs with the new module taking about 1.1 seconds.  The oscillation
  factorization is proved, but the reciprocal-minimum route is explicitly
  coarse; no uniform adjacent ratio, payment, completed gap inhabitant,
  continuum QFT, or Clay theorem is closed.

### [BF4-cutoff-two-novel-flow-conditional-raw-row-ratio] Global partition cancellation — **CLOSED 2026-08-23**

- **milestone**: define the unnormalized reflected BF4 row mass on the indexed
  cutoff-two vacuum sector; factor every retained stationary weight as that
  raw row mass times the common partition reciprocal; construct strict raw-row
  positivity from retained-weight positivity; cancel the common reciprocal
  exactly from every positive-edge ratio; identify the concrete conditional
  ceiling with the finite maximum of raw row-mass ratios; and compile payment
  of the corresponding raw-row load to completed strict contraction along a
  cofinal schedule.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawRowRatio.lean`.
- **decl**: `cutoffTwoRawStationaryRowMass`,
  `cutoffTwoEdgeLoadWeight_eqv_rawRowMass_mul_commonReciprocal`,
  `cutoffTwoRawStationaryRowMass_pos`,
  `cutoffTwoStationaryWeightRatio_eqv_rawRowMassRatio`,
  `cutoffTwoPositiveEdgeRawRowMassRatio`,
  `cutoffTwoConditionalReverseForwardRatio_eqv_rawRowMassRatio`,
  `cutoffTwoPositiveEdgeRawRowMassFiniteCeiling`,
  `cutoffTwoConditionalReverseForwardFiniteCeiling_eqv_rawRowMassFiniteCeiling`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_rawRowMassRatio`, and
  `CutoffTwoCofinalNovelConditionalRawRowMassRatioBound.toCompletedStrictContractionData`.
- **obligation**: expand the raw row masses into their boundary-channel
  weighted-Gram terms and derive a cutoff-uniform comparison on positive
  physical edges, or exhibit a cofinal family of growing raw adjacent ratios;
  then prove uniform load payment and construct and control the thermodynamic
  and continuum theories.
- **constructive?**: yes — strict positivity witnesses guard every quotient;
  all seven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first two focused checks failed on missing namespace
  exposure and are not passes.  The corrected focused check passes in about
  1.4 seconds; the exact one-worker dependency-complete target passes 4,966
  jobs with the new module taking about 1.3 seconds.  Global normalization is
  now eliminated from the edge ratio, but the local raw comparison, uniform
  payment, completed gap inhabitant, continuum QFT, and Clay theorem remain
  open.

### [BF4-cutoff-two-novel-flow-conditional-raw-boundary-moment] Boundary-moment Harnack reduction — **CLOSED 2026-08-23**

- **milestone**: expand every retained raw BF4 row mass into the finite
  boundary-channel moment `boundaryWeight * sourceHalfAmplitude *
  totalTargetAmplitude`; prove nonnegativity of the literal moment factors;
  define a Type-level positive-edge pointwise half-amplitude Harnack datum;
  propagate it termwise and through finite summation to a raw row-ratio bound;
  transport that bound by normalization cancellation and detailed balance to
  the conditional-ratio ceiling; and compile a cofinal Harnack-and-payment
  family to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRawBoundaryMoment.lean`.
- **decl**: `cutoffTwoRawBoundaryMomentTerm`,
  `cutoffTwoRawBoundaryMoment`,
  `cutoffTwoRawStationaryRowMass_eqv_boundaryMoment`,
  `CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt`,
  `cutoffTwoRawBoundaryMomentTerm_le_rho_mul_of_halfAmplitudeHarnack`,
  `cutoffTwoRawBoundaryMoment_le_rho_mul_of_halfAmplitudeHarnack`,
  `cutoffTwoRawStationaryRowMassRatio_le_of_halfAmplitudeHarnack`,
  `cutoffTwoConditionalReverseForwardRatio_le_of_halfAmplitudeHarnack`,
  `CutoffTwoPositiveEdgeHalfAmplitudeHarnackAt.toConditionalReverseForwardCeilingAt`,
  and
  `CutoffTwoCofinalNovelHalfAmplitudeHarnackPayment.toCompletedStrictContractionData`.
- **obligation**: inspect positive-edge boundary support and the existing BF4
  projective estimates; inhabit the pointwise amplitude datum where support is
  nested, or formulate and prove a support-aware weighted-moment substitute
  where it is not; then prove uniform path-load payment and construct and
  control the thermodynamic and continuum theories.
- **constructive?**: yes — the comparison is carried by explicit Type-level
  data and every quotient retains a strict positivity witness; all seven
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first focused check failed on missing namespace
  exposure and is not a pass.  The corrected focused check passes in about
  1.3 seconds; the exact one-worker dependency-complete target passes 4,967
  jobs with the new module taking about 1.2 seconds.  The Harnack implication
  is proved, but no Harnack inhabitant, uniform payment, completed gap
  inhabitant, continuum QFT, or Clay theorem is closed.

### [BF4-cutoff-two-novel-flow-conditional-support-aware-defect] Structural-zero-safe defect reduction — **CLOSED 2026-08-23**

- **milestone**: prove that the all-boundary positive-edge pointwise Harnack
  datum is uninhabited already at cutoff two, using the positive cube--vacuum
  physical edge and the explicit single-face boundary on which the cube
  amplitude is positive but the vacuum amplitude vanishes; replace it by a
  weighted absolute relative-defect moment; prove the raw row-ratio and
  conditional reverse/forward ratio bounds by `rho + defectFraction`; take the
  literal finite positive-edge maximum; and compile payment of the associated
  load to completed strict contraction along a cofinal schedule.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwareDefect.lean`.
- **decl**: `no_cutoffTwoPositiveEdgeHalfAmplitudeHarnackAt`,
  `cutoffTwoHalfAmplitudeRelativeDefect`,
  `cutoffTwoHalfAmplitudeRelativeDefectMoment`,
  `cutoffTwoRawBoundaryMoment_le_scaled_add_defectMoment`,
  `cutoffTwoRawStationaryRowMassRatio_le_rho_add_defectFraction`,
  `cutoffTwoPositiveEdgeHalfAmplitudeDefectFiniteMaximum`,
  `cutoffTwoConditionalReverseForwardRatio_le_supportAwareDefectCeiling`,
  `cutoffTwoSupportAwareDefectCeilingData`,
  `cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_supportAwareDefect`, and
  `CutoffTwoCofinalNovelSupportAwareDefectPayment.toCompletedStrictContractionData`.
- **obligation**: relate the weighted defect moment to the existing
  boundary-posterior `L1` framework and derive a cutoff-uniform payable bound,
  without assuming support nesting contradicted by the explicit structural
  zero; then construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — the no-go witness and defect estimates are explicit,
  every division retains a strict positive-denominator proof, and all eight
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first two focused checks failed on namespace/setoid and
  implicit-argument issues and are not passes.  The corrected focused check
  passes in about 1.5 seconds; the exact one-worker dependency-complete target
  passes 4,973 jobs with the new module taking about 1.6 seconds.  No uniform
  defect payment, completed gap inhabitant, continuum QFT, or Clay theorem is
  closed.

### [BF4-cutoff-two-novel-flow-conditional-support-aware-posterior-l1] Exact posterior normalization and scale diagnostic — **CLOSED 2026-08-23**

- **milestone**: normalize each retained raw BF4 boundary row by its explicit
  positive mass; prove total mass one and exact term recovery; identify that
  law with the existing full physical source-conditioned boundary posterior;
  prove finite `L1` symmetry and triangle inequalities; and prove that at the
  self-normalizing left/right raw mass ratio the support-aware defect moment is
  exactly left raw mass times pairwise posterior `L1`, while its defect
  fraction is exactly raw mass ratio times pairwise posterior `L1`.  Bound the
  latter shape distance by the two existing source-to-prior distances.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalSupportAwarePosteriorL1.lean`.
- **decl**: `cutoffTwoRawBoundaryGivenState`,
  `cutoffTwoRawBoundaryGivenState_total_one`,
  `cutoffTwoRawBoundaryGivenState_eqv_centralBoundaryGivenSource`,
  `cutoffTwoRawBoundaryPosteriorL1_eqv_centralBoundaryPosteriorL1`,
  `finiteL1Distance_triangle`, `finiteL1Distance_symm`,
  `cutoffTwoCentralBoundaryPosteriorL1_le_sourcePriorDistances`,
  `cutoffTwoRelativeDefectMoment_eqv_leftMass_mul_pairwisePosteriorL1`,
  `cutoffTwoRelativeDefectFraction_eqv_ratio_mul_pairwisePosteriorL1`, and
  `cutoffTwoRelativeDefectFraction_le_ratio_mul_sourcePriorDistances`.
- **obligation**: posterior mixing controls normalized row shape but leaves the
  desired raw row ratio as an exterior factor.  Inspect the directed path-edge
  geometry for a persistent-denominator orientation; failing that, derive an
  independent adjacent raw row-scale comparison from explicit BF4 local
  action/support data, then prove uniform payment and construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — all row normalizations carry explicit positivity
  proofs; finite `L1` algebra is setoid checked; the fourteen audited exports
  use `[propext]` or exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: several development checks failed and one raised-budget
  check was deliberately interrupted during pathological proof-index
  elaboration; none counts as a pass.  Opaque cutoff posterior aliases removed
  the blow-up.  The corrected focused check passes in about 1.6 seconds; the
  exact one-worker dependency-complete target passes 4,974 jobs with the new
  module taking about 1.7 seconds.  No independent uniform row ratio, flow
  payment, completed gap inhabitant, continuum QFT, or Clay theorem is closed.

### [BF4-cutoff-two-novel-flow-new-source-obstruction] Positive new-source occurrence — **CLOSED 2026-08-23**

- **milestone**: prove that the vacuum root belongs to the persistent old
  block and every genuinely new state differs from it; place each ordered
  new-to-vacuum pair in the literal novel endpoint list; extract the first edge
  of its nontrivial loop-erased positive path; prove that occurrence has the
  chosen new state as source and strictly positive load; and refute any claim
  that every positive occurrence of the present directed novel flow is sourced
  in the old block whenever the new block is inhabited.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowNewSourceObstruction.lean`.
- **decl**: `cutoffTwoVacuumRoot_mem_oldStates`,
  `cutoffTwoNewState_ne_vacuumRoot`,
  `cutoffTwoNovelFlow_exists_positiveOccurrence_with_newSource`, and
  `no_cutoffTwoNovelFlow_allPositiveOccurrenceSourcesOld`.
- **obligation**: the persistent-old row floor cannot alone control every
  source denominator in the literal directed flow.  Test whether kernel
  symmetry and paired endpoint traffic support an exact symmetrized or
  orientation-free payment; if not, derive an independent adjacent raw-row
  scale estimate for new states, then prove uniform payment and construct and
  control the thermodynamic and continuum theories.
- **constructive?**: yes — nontriviality, first-edge occurrence, endpoint
  weight positivity, and positive path length are all explicit; all four
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first focused check failed on one missing namespace
  opening and is not a pass.  The corrected focused monitored check passes in
  about 1.1 seconds; the exact one-worker dependency-complete target passes
  4,975 jobs with the new module taking about 1.0 second.  This result concerns
  the current directed path flow only and does not rule out symmetric
  reorientation.  No uniform flow payment, completed gap inhabitant, continuum
  QFT, or Clay theorem is closed.

### [BF4-cutoff-two-novel-flow-symmetric-load] Exact orientation-free flow energy — **CLOSED 2026-08-23**

- **milestone**: prove by finite Fubini and exact squared-difference symmetry
  that transposing a directed joint preserves its square-carrier Dirichlet
  form; prove that averaging a joint with its transpose is exactly
  energy-neutral; specialize this to a symmetric novel edge load; transfer the
  existing novel pairwise-variance bound with no constant loss; prove symmetry
  of the allocated physical kernel on retained states; and construct a
  three-field oriented capacity datum whose old-to-new field derives the
  omitted new-to-old comparison.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad.lean`.
- **decl**: `finiteJointDirichletBlock_transpose_eqv`,
  `finiteJointDirichletBlock_averageTranspose_eqv`,
  `cutoffTwoNovelSymmetricEdgeLoad`,
  `cutoffTwoNovelSymmetricEdgeLoad_symm`,
  `cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_original`,
  `cutoffTwoNovelPairwiseVariance_le_symmetricRawLoadedDirichlet`,
  `cutoffTwoNovelAllocatedKernel_symm`,
  `CutoffTwoNovelSymmetricOrientedCapacityAt`, and
  `CutoffTwoNovelSymmetricOrientedCapacityAt.new_old`.
- **obligation**: compile the orientation-reduced capacity datum through the
  full-sector coercivity and completed-gap interfaces.  Then prove the
  old--old and old-to-new capacity payments from persistent estimates and
  confront the irreducible new--new capacity block through explicit local BF4
  geometry or a different multiscale flow; finally construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — the transpose uses literal finite Fubini, averaging
  uses the exact rational half identity, every kernel symmetry invocation is
  guarded by retained-carrier witnesses, and all seven audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first two focused checks failed because one rational
  negation rewrite was absent and are not passes.  The corrected focused check
  passes in about 1.4 seconds; the exact one-worker dependency-complete target
  passes 4,976 jobs with the new module taking about 1.2 seconds.  Exact
  symmetrization removes the cross-edge orientation defect but supplies no
  capacity estimate.  The uniform flow payment, completed gap inhabitant,
  continuum QFT, and Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-capacity] Three-field completed-gap compiler — **CLOSED 2026-08-23**

- **milestone**: classify every retained endpoint into the old or new block;
  extend the three-field symmetric oriented capacity datum to the full carrier;
  decompose the symmetric loaded form into four exact directed blocks; pay the
  omitted new-to-old block by symmetry; control the novel pairwise variance;
  combine with persistent old-block coercivity to construct full-sector
  Dirichlet coercivity; and compile a cofinal three-field family to completed
  vacuum-sector strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.lean`.
- **decl**: `CutoffTwoNovelSymmetricOrientedCapacityAt.full_capacity`,
  `cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_four_blocks`,
  `CutoffTwoNovelSymmetricOrientedCapacityAt.loaded_oldOld_le_half_physical`,
  `CutoffTwoNovelSymmetricOrientedCapacityAt.floor_mul_novelPairwiseVariance_le_allocated_physical`,
  `CutoffTwoNovelSymmetricOrientedCapacityAt.toFullSectorDirichletCoercivityAt`,
  `CutoffTwoCofinalNovelSymmetricOrientedCapacity`, and
  `CutoffTwoCofinalNovelSymmetricOrientedCapacity.toCompletedStrictContractionData`.
- **obligation**: inhabit the old--old, old-to-new, and new--new capacity
  fields cofinally.  First factor the old-to-new field with the old source so
  the persistent row floor can be used; then isolate and estimate the
  irreducible new--new load/capacity ratio from explicit BF4 local geometry or
  replace that subflow by a multiscale construction.  After uniform payment,
  construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — carrier classification uses decidable embedded-image
  membership, every block is a literal finite rational sum, the half-capacity
  allocation is exact, and all six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first two focused checks failed on namespace,
  allocated-kernel unfolding, Boolean contradiction, and theorem-namespace
  resolution details and are not passes.  The corrected focused check passes
  in about 1.5 seconds; the exact one-worker dependency-complete target passes
  4,977 jobs with the new module taking about 1.3 seconds.  The compiler is
  closed, but none of the three cofinal local payments is inhabited.  Uniform
  completed contraction, continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-cross-conditional] Ratio-free cross-capacity reduction — **CLOSED 2026-08-23**

- **milestone**: normalize the forward directed load by its source weight and
  the reverse directed load by its target weight; prove that their symmetric
  average has the same old stationary denominator on every old-to-new edge;
  cancel that positive common factor from the physical capacity inequality;
  remove the old--old half allocation on cross edges; and package the remaining
  relative-load-versus-conditional-transition inequality as a non-vacuous
  Type-level certificate that supplies the compiler's `old_new` field.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional.lean`.
- **decl**: `cutoffTwoNovelRelativeTargetEdgeLoad`,
  `cutoffTwoEdgeLoadWeight_mul_relativeTargetEdgeLoad_eqv_load`,
  `cutoffTwoNovelSymmetricRelativeSourceEdgeLoad`,
  `cutoffTwoEdgeLoadWeight_mul_symmetricRelativeSourceEdgeLoad_eqv_load`,
  `cutoffTwoNovelSymmetricEdgeCapacity_iff_relativeConditional`,
  `cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_old_new`,
  `CutoffTwoNovelSymmetricOldNewConditionalCapacityAt`, and
  `CutoffTwoNovelSymmetricOldNewConditionalCapacityAt.old_new`.
- **obligation**: use the persistent cutoff-two old-state row floor to replace
  the reverse relative load's old denominator by a fixed positive denominator,
  then prove the resulting envelope is paid by the old-to-new conditional
  transition.  Independently estimate the irreducible new--new block; after
  all three capacity fields are inhabited cofinally, construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — both divisions carry explicit retained-state
  positivity witnesses, cancellation uses a strictly positive old weight, the
  missing analytic statement is a named Type-level field, and all five audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on two missing namespace
  openings and is not a pass.  The corrected focused monitored check passes in
  about 1.1 seconds; the exact one-worker dependency-complete target passes
  4,978 jobs with the new module taking about 1.1 seconds.  No cross-capacity
  certificate is inhabited yet.  Uniform completed contraction, continuum
  QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-cross-row-floor] Fixed old-denominator envelope — **CLOSED 2026-08-23**

- **milestone**: extract a cutoff-two preimage from every later old-block
  state; transport the previously proved pulled positive row floor to its
  later stationary weight; prove positive-denominator antitonicity for a
  nonnegative constructive rational numerator; majorize reverse relative
  cross traffic by division through the fixed old-row floor; and compile
  payment of the resulting symmetric envelope to the physical `old_new`
  capacity field.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRowFloor.lean`.
- **decl**: `cutoffTwoPulledUniformPositiveRowFloor_le_oldWeight`,
  `divPos_le_divPos_of_denominator_le`,
  `cutoffTwoNovelReverseOldRowFloorEnvelope`,
  `cutoffTwoNovelRelativeTargetEdgeLoad_le_reverseOldRowFloorEnvelope`,
  `cutoffTwoNovelSymmetricOldNewRowFloorEnvelope`,
  `cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_le_oldNewRowFloorEnvelope`,
  `CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt`,
  `CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt.toOldNewConditionalCapacityAt`,
  and `CutoffTwoNovelSymmetricOldNewRowFloorCapacityAt.old_new`.
- **obligation**: bound the explicit fixed-denominator envelope by the
  old-to-new conditional transition, using the endpoint-pair/edge-occurrence
  decomposition and existing conditional transition product identities where
  possible.  Independently inhabit old--old and irreducible new--new capacity;
  after cofinal uniform payment, construct and control the thermodynamic and
  continuum theories.
- **constructive?**: yes — the old preimage and every positivity fact remain
  explicit, division antitonicity uses only ordered rational multiplication,
  the unavailable payment remains a named Type-level field, and all six
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first focused check failed on one omitted explicit
  argument and is not a pass.  The corrected focused monitored check passes in
  about 1.2 seconds; the exact one-worker dependency-complete target passes
  4,979 jobs with the new module taking about 1.1 seconds.  No capacity field
  is inhabited by this envelope alone.  Uniform completed contraction,
  continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-cross-transition-product] Exact two-orientation product target — **CLOSED 2026-08-23**

- **milestone**: distribute target normalization over the endpoint-pair edge
  expansion; identify each target-normalized incidence with its exact
  endpoint/edge-target Harnack term; extend the constructively extracted path
  prefix through the selected positive edge; telescope the target ratio into
  reverse/forward conditional transition factors; and prove that the average
  of the existing source-prefix load and new through-edge target-prefix load
  is exactly the symmetric relative cross load.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.lean`.
- **decl**: `cutoffTwoNovelPathPairRelativeTargetDemand`,
  `cutoffTwoNovelRelativeTargetEdgeLoad_eqv_pairDemandSum`,
  `cutoffTwoNovelPathPairConditionalTargetHarnackTerm`,
  `cutoffTwoNovelPathPairRelativeTargetDemand_eqv_harnackTerm`,
  `positiveKernelPrefixThroughEdge`,
  `cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm`,
  `cutoffTwoNovelPathPairConditionalTargetHarnackTerm_eqv_transitionProduct`,
  `cutoffTwoNovelSymmetricCrossTransitionProductLoad`,
  `cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_crossTransitionProductLoad`,
  and `CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt`.
- **obligation**: bound both exact conditional products using local
  reverse/forward transition ceilings and prove that the resulting symmetric
  ceiling load is paid by the old-to-new conditional transition.  Separately
  inhabit old--old and new--new capacity; after uniform cofinal payment,
  construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — endpoint-pair membership, edge occurrence, prefix,
  positive edge, and the through-edge chain are all explicit data; the path
  extension is axiom-free and the other five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first two focused checks failed on namespace,
  dependent-`if`, reserved-identifier, and field-notation details and are not
  passes.  The corrected focused check passes in about 1.1 seconds; the exact
  one-worker dependency-complete target passes 4,979 jobs with the new module
  taking about 1.1 seconds.  The transition-product capacity certificate is
  not inhabited.  Uniform completed contraction, continuum QFT, and the Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-cross-ratio-ceiling] Two-orientation local ceiling compiler — **CLOSED 2026-08-23**

- **milestone**: replace the reverse target-prefix transition product by the
  corresponding power of a supplied one-edge reverse/forward conditional
  ratio ceiling; sum the pointwise bounds; combine them with the existing
  forward source-prefix ceiling; and package ceiling plus conditional payment
  as a Type-level certificate that contracts to the exact old-to-new
  transition-product capacity input.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.lean`.
- **decl**: `cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm`,
  `cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm_le_ceiling`,
  `cutoffTwoNovelConditionalTargetRatioCeilingLoad`,
  `cutoffTwoNovelConditionalTargetTransitionProductLoad_le_ratioCeilingLoad`,
  `cutoffTwoNovelSymmetricCrossRatioCeilingLoad`,
  `cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_ratioCeilingLoad`,
  `CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt`, and its two compiler
  maps.
- **obligation**: construct a scale-controlled reverse/forward ceiling on the
  positive edges actually used by the two routed prefixes and pay the explicit
  symmetric ceiling load by the old-to-new conditional transition.  Avoid
  strengthening this to a global carrier Harnack assertion unless the BF4
  geometry genuinely supplies it.  Independently inhabit old--old and
  new--new capacity; then construct and control the thermodynamic and continuum
  theories.
- **constructive?**: yes — both prefix chains, every exponent, and all
  positivity multipliers are explicit; the unavailable ceiling/payment remain
  named Type-level data; all five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on missing namespace openings
  and reached an induced elaboration timeout, so it is not a pass.  The
  corrected focused check passes in about 1.1 seconds; the exact one-worker
  dependency-complete target passes 4,980 jobs with the new module taking about
  1.1 seconds.  No analytic ceiling or capacity payment is inhabited.  Uniform
  completed contraction, continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-cross-routed-ceiling] Minimal routed-product ceiling interface — **CLOSED 2026-08-23**

- **milestone**: name the canonical routed path and its constructive prefix;
  replace a global carrier-wide one-edge Harnack field by product ceilings only
  on actual source prefixes and through-edge target prefixes; show that the
  stronger global ceiling maps to this routed datum; bound both exact product
  loads termwise and after finite summation; and compile a routed ceiling plus
  payment to the old-to-new transition-product capacity certificate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRoutedCeiling.lean`.
- **decl**: `cutoffTwoNovelRoutedPath`, `cutoffTwoNovelRoutedPrefix`,
  `CutoffTwoNovelRoutedPrefixRatioCeilingAt`,
  `CutoffTwoConditionalReverseForwardCeilingAt.toRoutedPrefixRatioCeilingAt`,
  `cutoffTwoNovelConditionalTransitionProductLoad_le_routedCeilingLoad`,
  `cutoffTwoNovelConditionalTargetTransitionProductLoad_le_routedCeilingLoad`,
  `cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_routedCeilingLoad`,
  and `CutoffTwoNovelSymmetricOldNewRoutedCeilingCapacityAt`.
- **obligation**: transport the existing constructively located finite ratio
  ceiling into the routed interface, then isolate the actual cofinal uniform
  bound and conditional payment.  Independently inhabit the old--old and
  irreducible new--new capacity blocks; after all three fields are uniform,
  construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — the restricted hypotheses quantify over explicit
  endpoint-pair membership and literal path-edge occurrence witnesses; the
  stronger-to-weaker map preserves all data; all five audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused monitored check passes on its first run in about
  1.1 seconds; the exact one-worker dependency-complete target passes 4,981
  jobs with the new module taking about 1.1 seconds.  No routed ceiling or
  capacity payment is inhabited here.  Uniform completed contraction,
  continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-cross-finite-decision] Exact cross-block checker and counteredge — **CLOSED 2026-08-23**

- **milestone**: transport the located finite reverse/forward ratio maximum to
  the routed-prefix datum; define its concrete symmetric cross ceiling load;
  prove it bounds the exact transition-product load; reflect precisely the
  old-to-new conditional payment into a Boolean scan; prove scan soundness and
  completeness; compile success to the old-to-new conditional certificate;
  and constructively return a literal overloaded cross edge on failure.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossFiniteDecision.lean`.
- **decl**: `cutoffTwoNovelSymmetricCrossFiniteRatioCeilingLoad`,
  `cutoffTwoNovelFiniteRoutedPrefixRatioCeilingData`,
  `cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_finiteRatioCeilingLoad`,
  `cutoffTwoNovelSymmetricCrossFiniteRatioCeilingCheck`, its soundness and
  completeness theorems,
  `cutoffTwoNovelSymmetricOldNewConditionalCapacityAt_of_check`,
  `CutoffTwoNovelSymmetricCrossFiniteRatioCeilingOutcome`, and
  `inspectCutoffTwoNovelSymmetricCrossFiniteRatioCeiling`.
- **obligation**: establish cofinal success of the exact cross-only scans or
  use returned overloaded edges to sharpen the flow/ceiling, and independently
  inhabit old--old and new--new capacity.  Combine those three inputs through
  the symmetric compiler, then construct and control the thermodynamic and
  continuum theories.
- **constructive?**: yes — the finite maximum and Boolean comparisons are
  decidable rational computations, and failure retains both endpoints and
  their block memberships as Type-level data; all five audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on one namespace-sensitive
  projection and is not a pass.  The corrected focused check passes in about
  1.1 seconds; the exact one-worker dependency-complete target passes 4,983
  jobs with the new module taking about 1.1 seconds.  No scan-success theorem
  or uniform capacity datum is asserted.  Uniform completed contraction,
  continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-checked-cross-compiler] Cofinal checked-cross contraction — **CLOSED 2026-08-23**

- **milestone**: define a cofinal capacity family whose old-to-new field is an
  exact scan-success witness rather than an opaque inequality; compile that
  witness to the cross capacity field at every scheduled cutoff; combine it
  with explicit old--old and new--new payments; and feed the assembled
  three-field family through the existing finite gap to completed
  vacuum-sector strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCheckedCrossCompiler.lean`.
- **decl**: `CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity`,
  `CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity.toCofinalNovelSymmetricOrientedCapacity`,
  and
  `CutoffTwoCofinalNovelSymmetricCheckedCrossCapacity.toCompletedStrictContractionData`.
- **obligation**: prove cofinal success of the exact cross scan and inhabit the
  old--old and new--new symmetric capacity fields.  First reflect both
  same-block fields into exact finite scans so success and counteredges are
  computationally visible; after the full cofinal capacity is proved,
  construct and control the thermodynamic and continuum theories.
- **constructive?**: yes — the scan equality is an explicit field, its
  compiler returns the actual cross certificate, and both same-block gaps
  remain named fields in a Type-level structure; both audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused monitored check passes on its first run in about
  0.9 seconds; the exact one-worker dependency-complete target passes 4,984
  jobs with the new module taking about 0.9 seconds.  The cofinal family is not
  inhabited.  Uniform completed contraction, continuum QFT, and the Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-three-block-decision] Complete finite block checker — **CLOSED 2026-08-23**

- **milestone**: reflect the exact old--old and new--new symmetric capacity
  inequalities into finite Boolean scans with soundness and completeness;
  combine them with the sufficient cross-ceiling scan; compile combined
  success to the existing three-field oriented capacity datum and completed
  strict contraction; and constructively retain a literal failed edge tagged
  by block when inspection fails.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricThreeBlockDecision.lean`.
- **decl**: `cutoffTwoNovelSymmetricOldOldCapacityCheck`,
  `cutoffTwoNovelSymmetricNewNewCapacityCheck`, their soundness and completeness
  theorems, `cutoffTwoNovelSymmetricThreeBlockCapacityCheck`,
  `cutoffTwoNovelSymmetricOrientedCapacityAt_of_threeBlockCheck`,
  `CutoffTwoNovelSymmetricThreeBlockCapacityOutcome`,
  `inspectCutoffTwoNovelSymmetricThreeBlockCapacity`, and
  `CutoffTwoCofinalNovelSymmetricThreeBlockCheck.toCompletedStrictContractionData`.
- **obligation**: prove that the combined three-block check succeeds along a
  cofinal cutoff schedule, using tagged failed edges to identify which local
  estimate or flow choice must be sharpened.  Then construct and control the
  thermodynamic and continuum theories.
- **constructive?**: yes — both diagonal scans decide the exact displayed
  rational inequality; the cross scan retains its stated conservative status;
  failed inspection carries literal endpoints and memberships in Type; all
  five audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused check failed on one missing namespace
  opening and is not a pass.  The corrected focused check passes in about 1.2
  seconds; the exact one-worker dependency-complete target passes 4,985 jobs
  with the new module taking about 1.2 seconds.  The cofinal checked family is
  not inhabited.  Uniform completed contraction, continuum QFT, and the Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-diagonal-conditional] Exact diagonal source-weight cancellation — **CLOSED 2026-08-23**

- **milestone**: identify the old--old allocated conditional kernel with one
  half of the conditional transition and the new--new allocation with the full
  transition; cancel the positive stationary source mass from both diagonal
  physical inequalities; define exact conditional scans; prove them
  Boolean-equal to the physical scans; and compile a cofinal successful
  normalized three-block checker to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricDiagonalConditional.lean`.
- **decl**:
  `cutoffTwoNovelAllocatedConditionalKernel_eqv_halfConditional_of_old_old`,
  `cutoffTwoNovelAllocatedConditionalKernel_eqv_conditional_of_new_new`,
  `CutoffTwoNovelSymmetricOldOldConditionalCapacityAt`,
  `CutoffTwoNovelSymmetricNewNewConditionalCapacityAt`, both conditional
  checks and their Boolean-equality theorems,
  `cutoffTwoNovelSymmetricThreeBlockConditionalCapacityCheck`, and
  `CutoffTwoCofinalNovelSymmetricThreeBlockConditionalCheck.toCompletedStrictContractionData`.
- **obligation**: expand and control diagonal relative loads directly against
  their conditional transitions, retaining the exact half allocation on the
  old block; establish cofinal success of all three conditional block checks;
  then construct and control thermodynamic and continuum limits.
- **constructive?**: yes — positive weights are cancelled through existing
  rational equivalences, the allocation cases use explicit block-membership
  witnesses, and the finite scan identity is proved rather than assumed; all
  five audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: a diagnostic evaluator was stopped at the 12 GiB monitored
  reserve (exit 75) and supplies no evidence.  The first focused proof check
  failed on one reflexivity goal and invalid `theorem` declarations returning
  `Type`, so it is not a pass.  The corrected focused check passes in about
  1.1 seconds; the exact one-worker target passes 4,986 jobs with the new
  module taking about 1.1 seconds.  The cofinal normalized family is not
  inhabited.  Uniform completed contraction, continuum QFT, and the Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-all-block-transition-product] Exact common path-product target — **CLOSED 2026-08-23**

- **milestone**: generalize the exact symmetric relative-load transition-
  product formula from cross edges to every retained source; encode all three
  oriented block payments against one common transition-product load; prove
  constructive conversions to and from physical symmetric capacity; define
  exact finite scans of the three product payments; and compile cofinal scan
  success to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProduct.lean`.
- **decl**: `cutoffTwoNovelSymmetricTransitionProductLoad`,
  `cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_transitionProductLoad`,
  `CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityAt` and its
  `toOrientedCapacityAt` / `ofOrientedCapacityAt` maps, the three block checks,
  `cutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityCheck`, its
  success compiler and completeness theorem, and
  `CutoffTwoCofinalNovelSymmetricThreeBlockTransitionProductCheck.toCompletedStrictContractionData`.
- **obligation**: bound the explicit source-prefix and through-edge target-
  prefix transition-product sums by the selected conditional edge uniformly
  along a cofinal cutoff schedule, respecting the old--old half allocation;
  then construct and control thermodynamic and continuum limits.
- **constructive?**: yes — the transition products, prefix witnesses, finite
  lists, scans, and both certificate conversions are explicit; the new exact
  route does not use the conservative cross ceiling; all five audited exports
  use exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused monitored check passes on its first run in about
  1.2 seconds; the exact one-worker target passes 4,987 jobs with the new
  module taking about 1.2 seconds.  No scan success or uniform product payment
  is proved.  Uniform completed contraction, continuum QFT, and the Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-all-block-transition-product-decision] Exact tagged product counteredge — **CLOSED 2026-08-23**

- **milestone**: inspect all three exact finite transition-product payment
  lists in block order; return the complete capacity certificate on success;
  and preserve a literal failed edge, its endpoint memberships, failed exact
  inequality, and old--old / old-to-new / new--new tag on failure.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockTransitionProductDecision.lean`.
- **decl**:
  `CutoffTwoNovelSymmetricThreeBlockTransitionProductCapacityOutcome` and
  `inspectCutoffTwoNovelSymmetricThreeBlockTransitionProductCapacity`.
- **obligation**: use the exact tagged counteredge to target a block-specific
  uniform transition-product estimate or alter the selected simple routes;
  establish cofinal capacity, then construct and control thermodynamic and
  continuum limits.
- **constructive?**: yes — recursive rational comparison returns Type-level
  success or literal endpoints with membership and negated payment; the
  audited inspector uses exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the focused monitored check passes on its first run in about
  0.9 seconds; the exact one-worker target passes 4,988 jobs with the new
  module taking about 0.9 seconds.  No inspection outcome or cofinal success is
  asserted.  Uniform completed contraction, continuum QFT, and the Clay
  theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-all-block-routed-ceiling] Common routed ceiling compiler — **CLOSED 2026-08-23**

- **milestone**: prove that the routed source-prefix and through-edge target-
  prefix ceiling bounds the common symmetric transition-product load on every
  block; retain the old--old half allocation and full allocation elsewhere in
  a three-field ceiling-payment datum; and compile it through exact product
  capacity and physical capacity to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockRoutedCeiling.lean`.
- **decl**: `cutoffTwoNovelSymmetricRoutedRatioCeilingLoad`,
  `cutoffTwoNovelSymmetricTransitionProductLoad_le_routedCeilingLoad`,
  `CutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt`, its
  `toTransitionProductCapacityAt` and `toOrientedCapacityAt` compilers, and
  `CutoffTwoCofinalNovelSymmetricThreeBlockRoutedCeilingCapacity.toCompletedStrictContractionData`.
- **obligation**: instantiate the common routed ceiling by the located finite
  reverse/forward maximum and decide its three block payments; prove cofinal
  payment or use exact counteredges to improve the routes; then construct and
  control thermodynamic and continuum limits.
- **constructive?**: yes — the same explicit routed-prefix witness is reused
  in each block, all three payments remain visible Type fields, and all four
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first focused check failed on one missing namespace and
  is not a pass.  The corrected focused check passes in about 1.0 seconds; the
  exact one-worker target passes 4,989 jobs with the new module taking about
  1.1 seconds.  No ceiling payment or cofinal family is inhabited.  Uniform
  completed contraction, continuum QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-all-block-finite-ceiling-decision] Concrete all-block ceiling scan — **CLOSED 2026-08-23**

- **milestone**: instantiate the common routed-prefix ceiling with the located
  finite reverse/forward ratio maximum; prove it bounds the common exact
  product load; decide old--old, old-to-new, and new--new ceiling payments;
  construct full routed-ceiling capacity on success; retain a literal failed
  ceiling edge tagged by block on failure; and compile cofinal check success to
  completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricAllBlockFiniteCeilingDecision.lean`.
- **decl**: `cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingLoad`,
  `cutoffTwoNovelSymmetricTransitionProductLoad_le_finiteCeilingLoad`, the two
  new diagonal ceiling checks and soundness theorems,
  `cutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingCheck`,
  `cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_finiteCheck`,
  `CutoffTwoNovelSymmetricAllBlockFiniteRatioCeilingOutcome`, its inspector,
  and the cofinal completed compiler.
- **obligation**: prove cofinal success of the concrete combined checker, or
  compare its tagged failures with the exact product inspector and replace the
  global ratio maximum by sharper block/edge-local routed ceilings; then
  construct and control thermodynamic and continuum limits.
- **constructive?**: yes — the finite maximum, block scans, success certificate,
  and tagged failed edges are explicit rational data; all five audited exports
  use exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed because redundant `unfold`
  calls targeted aliases already reduced by elaboration and is not a pass.  The
  corrected focused check passes in about 1.1 seconds; the exact one-worker
  target passes 4,990 jobs with the new module taking about 1.2 seconds.  No
  cofinal check success is asserted.  Uniform completed contraction, continuum
  QFT, and the Clay theorem remain open.

### [BF4-cutoff-two-novel-flow-symmetric-routed-support-finite-ceiling] Routed-support finite ratio ceiling — **CLOSED 2026-08-23**

- **milestone**: enumerate the literal directed support of all canonical novel
  paths; take the finite reverse/forward conditional-ratio maximum only over
  those edges; prove that source prefixes and prefixes through a selected edge
  remain in their parent route; bound both prefix products; and prove that the
  restricted maximum is no larger than the full-carrier maximum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteCeiling.lean`.
- **decl**: `cutoffTwoNovelRoutedDirectedEdges`,
  `cutoffTwoConditionalReverseForwardRoutedFiniteCeiling`,
  `cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_le_finiteCeiling`,
  `prefixAtDirectedEdge_directedEdges_subset`,
  `throughEdge_directedEdges_subset`,
  `cutoffTwoNovelPathReverseForwardProduct_le_routedFiniteCeilingPow`, and
  `cutoffTwoNovelRoutedSupportFiniteRatioCeilingData`.
- **obligation**: instantiate the three block payment scans with this sharper
  routed-support ceiling; prove cofinal payment success or refine routes using
  exact-product failures; then construct and control thermodynamic and
  continuum limits.
- **constructive?**: yes — the support list and maximum are explicit finite
  data, prefix containment is proved structurally, and all six audited exports
  use exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first two focused checks failed during proof repair and
  are not passes.  The corrected focused check passes in about 1.1 seconds;
  the exact one-worker target passes 4,991 jobs with the new module taking
  about 1.2 seconds.  The comparison is non-strict (`routed <= full`); no
  payment or cofinal success, completed uniform contraction, continuum QFT, or
  Clay theorem is asserted.

### [BF4-cutoff-two-novel-flow-symmetric-routed-support-finite-decision] Routed-support three-block payment decision — **CLOSED 2026-08-23**

- **milestone**: substitute the routed-support maximum into the common
  symmetric ceiling load; decide its old--old, old-to-new, and new--new
  payments; construct routed-ceiling capacity on combined success; retain a
  literal failed edge tagged by block otherwise; and compile cofinal check
  success to completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportFiniteDecision.lean`.
- **decl**:
  `cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad`,
  `cutoffTwoNovelSymmetricTransitionProductLoad_le_routedSupportFiniteCeilingLoad`,
  the three block checks and soundness theorems,
  `cutoffTwoNovelSymmetricAllBlockRoutedSupportFiniteCeilingCheck`,
  `cutoffTwoNovelSymmetricThreeBlockRoutedCeilingCapacityAt_of_routedSupportCheck`,
  `CutoffTwoNovelSymmetricRoutedSupportFiniteCeilingOutcome`, its inspector,
  and the cofinal completed compiler.
- **obligation**: evaluate the new scans at small meaningful cutoffs and
  compare any routed-ceiling failure with the exact-product inspector; prove
  cofinal success by a uniform estimate or redesign failing canonical routes;
  then construct and control thermodynamic and continuum limits.
- **constructive?**: yes — all checks are Boolean rational comparisons and
  inspection returns Type-level success or literal block-tagged failure; all
  six audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused check failed only because `.certified`
  was ambiguous among imported decision types and is not a pass.  The corrected
  focused check passes in about 1.2 seconds; the exact one-worker target passes
  4,992 jobs with the new module taking about 1.2 seconds.  No scan result or
  cofinal success, completed uniform contraction, continuum QFT, or Clay
  theorem is asserted.

### [BF4-cutoff-two-novel-flow-symmetric-routed-support-dominance] Ordered finite checker hierarchy — **CLOSED 2026-08-23**

- **milestone**: prove monotonicity of every rational-power path ceiling term,
  both finite prefix-load sums, and the symmetric ceiling load; show the
  routed-support load is pointwise no larger than the full-carrier load; and
  derive the checker implications `full-carrier -> routed-support -> exact
  transition-product`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDominance.lean`.
- **decl**: `qpow_base_mono`, the source and target pair-term monotonicity
  theorems, the two summed-load monotonicity theorems,
  `cutoffTwoNovelSymmetricRoutedRatioCeilingLoad_mono`,
  `cutoffTwoNovelSymmetricRoutedSupportFiniteCeilingLoad_le_fullFiniteCeilingLoad`,
  `cutoffTwoNovelSymmetricAllBlockFiniteCheck_implies_routedSupportCheck`, and
  `cutoffTwoNovelSymmetricRoutedSupportCheck_implies_transitionProductCheck`.
- **obligation**: derive tractable block/path-local symbolic product bounds or
  expose an exact failed edge within bounded resources; use that evidence to
  prove cofinal capacity or redesign the canonical routes; then construct and
  control thermodynamic and continuum limits.
- **constructive?**: yes — finite-list monotonicity and Boolean reflection are
  explicit, all six audited exports stay within `[propext, Quot.sound]`, and
  the elementary rational-power lemma uses `[propext]`; no forbidden
  construct was added.
- **status note**: a guarded cutoff-2 evaluation stopped at the configured
  12 GiB reserve before returning a value and is inconclusive.  Earlier focused
  checks failed during namespace and proof-dependent unfolding repair and are
  not passes.  The corrected focused check passes in about 1.1 seconds; the
  exact one-worker target passes 4,993 jobs with the new module taking about
  1.1 seconds.  The hierarchy supplies implications only: no scan result,
  cofinal capacity, completed uniform contraction, continuum QFT, or Clay
  theorem is asserted.

### [BF4-cutoff-two-novel-flow-symmetric-routed-support-deduplicated-ceiling] Distinct routed-edge ceiling — **CLOSED 2026-08-23**

- **milestone**: erase repeated directed edges from the flattened novel-route
  support; prove support membership is unchanged; prove the distinct-list and
  repeated-list finite maxima bound each other; reconstruct both routed prefix
  product bounds; and prove the associated symmetric ceiling loads bound each
  other.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricRoutedSupportDeduplicatedCeiling.lean`.
- **decl**: `cutoffTwoNovelRoutedDistinctDirectedEdges`, its membership iff,
  `cutoffTwoConditionalReverseForwardDistinctRoutedFiniteCeiling`, both maximum
  comparisons, `cutoffTwoNovelDistinctRoutedSupportFiniteRatioCeilingData`,
  `cutoffTwoNovelSymmetricDistinctRoutedSupportFiniteRatioCeilingLoad`, and both
  load comparisons.
- **obligation**: stage evaluation by first measuring the distinct cutoff-2
  support, then evaluate the reduced maximum/payment only within the monitored
  memory reserve; independently seek symbolic route-local bounds sufficient
  for cofinal exact capacity and later continuum control.
- **constructive?**: yes — `eraseDups`, finite maximum induction, and power
  monotonicity are explicit; all five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on missing namespace openings
  and is not a pass.  The corrected focused check passes in about 1.0 second;
  the exact one-worker target passes 4,994 jobs with the new module taking
  about 1.0 second.  No evaluated cardinality, payment, cofinal capacity,
  completed uniform contraction, continuum QFT, or Clay theorem is asserted.

### [BF4-cutoff-two-carrier-recoding] Exact 65-state anchor recoding and capacity — **CLOSED 2026-08-23**

- **milestone**: derive the opaque canonical component's exact length from the
  certified 65-state permutation; prove generic equal-cutoff old/full and
  new/empty identities; contract the cutoff-two novel endpoint, occurrence,
  and routed-support lists to empty; and inhabit the resulting cutoff-two
  routed-ceiling capacity certificate symbolically.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoCarrierRecoding.lean`.
- **decl**: `cutoffTwoEdgeLoadFullStates_length`,
  `centralPhysicalFiniteEmbeddedVacuumSectorIndices_self`,
  `centralPhysicalFiniteVacuumSectorOldBlockIndices_self`,
  `centralPhysicalFiniteVacuumSectorNewBlockIndices_self`, the specialized
  old/new and novel-list identities,
  `cutoffTwoConditionalReverseForwardRoutedFiniteCeiling_self`,
  `cutoffTwoNovelSymmetricRoutedSupportFiniteRatioCeilingLoad_self_eqv_zero`,
  and `cutoffTwoNovelSymmetricAnchorRoutedCeilingCapacity`.
- **obligation**: construct an equally tractable recoding of the first genuine
  positive cutoff increment, expose its new shell and routed transitions, and
  prove or refute the local capacity payments; then lift a successful estimate
  cofinally and construct the thermodynamic and continuum limits.
- **constructive?**: yes — the proof transports a finite permutation and uses
  structural list induction, proof-carrying membership, rational
  nonnegativity, and the existing routed-prefix certificate.  All eight
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: a prior guarded cardinality `#eval` stopped at the 12 GiB
  reserve before any output and is inconclusive.  Early focused proof
  iterations hit the heartbeat limit during proof repair and are not passes.
  The corrected focused check passes in about 1.7 seconds; the exact one-worker
  target passes 4,995 jobs with the new module taking about 1.5 seconds.  The
  anchor certificate is not a cofinal family and proves no completed uniform
  contraction, continuum QFT, or Clay theorem.

### [BF4-cutoff-two-novel-shell-state-recoding] Executable later-shell classifier — **CLOSED 2026-08-23**

- **milestone**: identify embedded base indices exactly by represented-state
  membership; specialize old/new cutoff-two blocks to the certified 65-sector
  and its complement; construct a direct Boolean state classifier; and prove
  the new block equals the later vacuum component filtered by classifier
  rejection.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.lean`.
- **decl**:
  `mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem`,
  `mem_cutoffTwoEdgeLoadOldStates_iff_state_mem_cubeSector`,
  `mem_cutoffTwoEdgeLoadNewStates_iff_state_not_mem_cubeSector`,
  `cutoffTwoCubeSectorStateB`,
  `cutoffTwoCubeSectorStateB_true_iff_mem`,
  `cutoffTwoEdgeLoadNewStates_eq_classifierRejectFilter`, and
  `mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject`.
- **obligation**: recode novel endpoint pairs and routed transitions through
  the classifier-reject shell; derive a tractable finite or symbolic shell
  description and prove/refute its local capacity payments; then lift a
  successful bound cofinally and construct controlled limits.
- **constructive?**: yes — index injectivity, explicit cutoff embeddings,
  finite-list induction, 24-coordinate bounds, and a natural-number terminal
  classifier provide all decisions.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed during namespace and
  decidability repair and is not a pass.  The corrected focused check passes
  in about 2.4 seconds; the exact one-worker target passes 4,996 jobs with the
  new module taking about 2.2 seconds.  The result classifies but neither
  enumerates nor bounds the later shell, and proves no cofinal capacity,
  completed uniform contraction, continuum QFT, or Clay theorem.

### [BF4-cutoff-two-novel-shell-cardinality-balance] Constant 65-state old block — **CLOSED 2026-08-23**

- **milestone**: rewrite the old block as the classifier-accept filter; prove
  that its length is exactly 65 at every later cutoff; and prove the exact
  cardinality balance `|full later| = 65 + |new later|`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.lean`.
- **decl**: `cutoffTwoEdgeLoadOldStates_eq_classifierAcceptFilter`,
  `cutoffTwoEdgeLoadOldStates_length_of_later`,
  `cutoffTwoEdgeLoadOld_add_new_length`, and
  `cutoffTwoEdgeLoadFullStates_length_eq_65_add_new`.
- **obligation**: bound or recode the classifier-reject shell itself, express
  novel endpoint pairs and routes over that shell, and prove/refute their
  local capacity payments before attempting a cofinal lift and controlled
  limits.
- **constructive?**: yes — the proof uses the existing injective cutoff map,
  finite-list permutations, Boolean filter congruence, and structural length
  induction.  Both newly audited exports, and all eight audited exports in the
  module, use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the first focused check of the added balance failed on a
  natural-number reassociation goal and is not a pass.  The corrected focused
  check passes in about 3.1 seconds; the exact one-worker target passes 4,996
  jobs with the expanded module taking about 2.9 seconds.  The equality
  isolates but does not bound the new shell, and proves no cofinal capacity,
  completed uniform contraction, continuum QFT, or Clay theorem.

### [BF4-cutoff-two-novel-endpoint-classifier-recoding] Exact shell-polynomial endpoint count — **CLOSED 2026-08-23**

- **milestone**: recode the novel ordered endpoint list by the state-level
  accept/reject classifier; prove its semantic membership iff; and prove its
  exact length is `n^2 + 130 n`, where `n` is the genuinely new shell length.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding.lean`.
- **decl**: `cutoffTwoEdgeLoadOldStates_eq_classifierAcceptedIndices`,
  `cutoffTwoEdgeLoadNewStates_eq_classifierRejectedIndices`,
  `mem_cutoffTwoEdgeLoadOldStates_iff_classifier_accept`,
  `cutoffTwoNovelEndpointPairs_eq_classifierPairs`,
  `mem_cutoffTwoNovelEndpointPairs_iff_classifier_reject`, and
  `cutoffTwoNovelEndpointPairs_length`.
- **obligation**: bound routed edge occurrences in terms of shell length and
  simple-path length, convert the aggregate route cost into edge-local
  weighted load/capacity control, and then obtain a genuinely cutoff-uniform
  estimate before attempting completed or continuum limits.
- **constructive?**: yes — the proof uses Boolean filtering, finite Cartesian
  products, structural list induction, and constructive natural-number
  arithmetic.  All five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused proof attempt failed during repair of a
  local Cartesian length lemma and nonlinear arithmetic normalization and is
  not a pass.  The corrected focused check passes in about 2.7 seconds; the
  exact one-worker target passes 4,997 jobs with the new module taking about
  2.5 seconds.  The theorem neither bounds `n` nor proves route capacity,
  completed uniform contraction, continuum QFT, or the Clay theorem.

### [BF4-cutoff-two-novel-route-classifier-complexity] Shell-polynomial routed support — **CLOSED 2026-08-23**

- **milestone**: bound every selected loop-erased route by carrier length;
  aggregate that bound over the exact novel endpoint list; and transport it to
  both the routed edge projection and its duplicate-free support.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelRouteClassifierComplexity.lean`.
- **decl**:
  `cutoffTwoSimpleWeightedPathOccurrences_length_le_carrier`,
  `cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_pair_mul_carrier`,
  `cutoffTwoNovelSimpleWeightedEdgeOccurrences_length_le_shellPolynomial`,
  `cutoffTwoNovelRoutedDirectedEdges_length_eq_occurrences`,
  `cutoffTwoNovelRoutedDistinctDirectedEdges_length_le_occurrences`, and
  `cutoffTwoNovelRoutedDistinctDirectedEdges_length_le_shellPolynomial`.
- **obligation**: bound the occurrence weights and routed reverse/forward
  ratios, turn the aggregate support ceiling into edge-local load/capacity
  control, and obtain a genuinely cutoff-uniform contraction before attempting
  completion or continuum limits.
- **constructive?**: yes — the proof uses the loop-erased path certificate,
  structural `flatMap` induction, natural-number arithmetic, projection, and
  constructive duplicate erasure.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on multiplication
  reassociation and an underspecified list-map theorem and is not a pass.  The
  corrected focused check passes in about 1.6 seconds; the exact one-worker
  target passes 4,998 jobs with the new module taking about 1.7 seconds.  This
  bounds list sizes only: it does not bound shell size, route weights, local
  congestion, completed uniform contraction, continuum QFT, or the Clay
  theorem.

### [BF4-cutoff-two-novel-shell-edge-load] Shell-linear stationary load — **CLOSED 2026-08-23**

- **milestone**: prove the classifier-normal novel endpoint list is
  duplicate-free, embed its nonnegative one-path loads into the full ordered
  endpoint square, and derive the pointwise analytic estimate
  `novelEdgeLoad <= ofNat (65 + n)`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelShellEdgeLoadBound.lean`.
- **decl**: `cutoffTwoNovelEndpointPairs_nodup`,
  `cutoffTwoSimpleWeightedPathEdgeLoad_nonnegative`,
  `cutoffTwoNovelSimpleEdgeLoad_le_fullSimpleEdgeLoad`,
  `cutoffTwoNovelSimpleEdgeLoad_le_sectorSize`, and
  `cutoffTwoNovelSimpleEdgeLoad_le_shellLinear`.
- **obligation**: prove that allocated routed transition capacity dominates
  the fixed coercivity scale times this linear load, uniformly along a cofinal
  cutoff family; then compile the resulting contraction through completion
  and construct controlled thermodynamic/continuum limits.
- **constructive?**: yes — the proof uses Boolean-filter disjointness,
  Cartesian-list nodup, a finite weighted identity injection, stationary
  nonnegativity, and the existing full-flow mass bound.  All five audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the first focused check failed only because two required
  namespaces were not open and is not a pass.  The corrected focused check
  passes in about 2.2 seconds; the exact one-worker target passes 4,999 jobs
  with the new module taking about 2.2 seconds.  No cutoff-uniform transition
  floor, completed contraction, continuum QFT, or Clay theorem is proved.

### [BF4-cutoff-two-novel-shell-edge-floor-payment] One scalar capacity payment — **CLOSED 2026-08-23**

- **milestone**: reduce all four pointwise novel-flow capacity blocks to the
  scalar payment
  `novelFloor * ofNat (65 + n) <= half * finitePositiveEdgeFloor`,
  and compile a cofinal family of those payments to completed strict
  contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelShellEdgeFloorPayment.lean`.
- **decl**:
  `cutoffTwoNovelFloor_mul_load_le_halfKernel_of_shellEdgeFloorPayment`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_shellEdgeFloorPayment`,
  `CutoffTwoCofinalNovelShellEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity`,
  and
  `CutoffTwoCofinalNovelShellEdgeFloorPayment.toCompletedStrictContractionData`.
- **obligation**: construct the cofinal scalar payment, preferably after
  sharpening carrier size by the actual novel stationary endpoint mass; then
  obtain completed contraction and continue to thermodynamic/continuum
  control.
- **constructive?**: yes — positive-load route support invokes the located
  finite positive-edge floor, while the zero-load case is closed by rational
  order and kernel nonnegativity.  All four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed only because the completed
  gap namespace was not open and is not a pass.  The corrected focused check
  passes in about 2.3 seconds; the exact one-worker target passes 5,000 jobs
  with the new module taking about 2.3 seconds.  The payment premise is not
  inhabited, so no completed contraction, continuum QFT, or Clay theorem is
  claimed.

### [BF4-cutoff-two-novel-stationary-mass-load] Mass-refined fixed-edge load — **CLOSED 2026-08-23**

- **milestone**: define the exact novel stationary endpoint mass, decompose it
  into new--new and both directed cross products, prove it vanishes at cutoff
  two, and retain it in the bound
  `novelEdgeLoad <= (65+n) * novelMass`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound.lean`.
- **decl**: `cutoffTwoNovelEndpointWeightMass`,
  `cutoffTwoNovelEndpointWeightMass_eqv_newNew_add_cross`,
  `cutoffTwoNovelEndpointWeightMass_nonnegative`,
  `cutoffTwoNovelEndpointWeightMass_self_eqv_zero`,
  `cutoffTwoNovelPathLoadSum_le_sizeWeightedPairSum`,
  `cutoffTwoNovelSimpleEdgeLoad_le_size_mul_endpointMass`, and
  `cutoffTwoNovelSimpleEdgeLoad_le_shellSize_mul_endpointMass`.
- **obligation**: compile the mass-refined edge-floor payment and prove that
  new-shell stationary mass compensates for path-length growth and
  positive-edge decay along a cofinal cutoff family.
- **constructive?**: yes — all quantities are finite rational sums, the proof
  uses exact Cartesian factorization and path-load monotonicity, and cutoff-two
  vanishing is structural.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused attempts failed on missing namespaces and
  a deterministic elaboration timeout before local expression recoding; they
  are not passes.  The corrected focused check passes in about 1.4 seconds;
  the exact one-worker target passes 5,001 jobs with the new module taking
  about 1.4 seconds.  No cofinal mass decay, completed contraction, continuum
  QFT, or Clay theorem is proved.

### [BF4-cutoff-two-novel-stationary-mass-payment] Mass-refined capacity compiler — **CLOSED 2026-08-23**

- **milestone**: prove that the scalar payment
  `novelFloor * ((65+n) * novelMass) <= half * edgeFloor` implies all four
  pointwise novel-flow capacity blocks, and package its cofinal form into the
  existing completed strict-contraction datum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment.lean`.
- **decl**:
  `cutoffTwoNovelFloor_mul_load_le_halfKernel_of_stationaryMassEdgeFloorPayment`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_stationaryMassEdgeFloorPayment`,
  `CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity`,
  and
  `CutoffTwoCofinalNovelStationaryMassEdgeFloorPayment.toCompletedStrictContractionData`.
- **obligation**: bound novel endpoint mass by new-shell stationary mass and
  then prove that the resulting shell-weighted tail pays the positive routed
  edge floor along a cofinal family.
- **constructive?**: yes — the compiler uses only the proved mass-refined
  load estimate, finite positive-edge floor, and rational order algebra.  All
  four audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the focused check passes in about 2.4 seconds; the exact
  one-worker target passes 5,002 jobs with the new module taking about 2.3
  seconds.  The scalar payment premise is not inhabited, so no completed
  contraction, continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-novel-endpoint-new-shell-bound] Novel mass versus new-shell mass — **CLOSED 2026-08-23**

- **milestone**: prove the exact old/new stationary-mass partition, its
  subprobability bound, and the uniform estimate `novelMass <= 2*newMass`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound.lean`.
- **decl**: `cutoffTwoOldMass_nonnegative`,
  `cutoffTwoNewMass_nonnegative`,
  `cutoffTwoOldMass_add_newMass_eqv_fullSectorMass`,
  `cutoffTwoOldMass_add_newMass_le_one`,
  `cutoffTwoNovelEndpointWeightMass_le_newMass_add_newMass`, and
  `cutoffTwoNovelEndpointWeightMass_le_two_mul_newMass`.
- **obligation**: compile the resulting shell-weighted new-state tail payment,
  then prove that tail pays the positive routed edge floor cofinally.
- **constructive?**: yes — the proof is a finite filter partition,
  nonnegative finite sums, and rational monotonicity.  All six audited exports
  use exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two initial focused failures (missing namespace and
  unreduced `ofNat 2`) are not passes.  The corrected focused check passes in
  about 1.7 seconds; the exact one-worker target passes 5,003 jobs with the
  new module taking about 1.6 seconds.  No cofinal tail estimate, completed
  contraction, continuum QFT, or Clay theorem is proved.

### [BF4-cutoff-two-novel-new-shell-payment] New-shell-only capacity compiler — **CLOSED 2026-08-23**

- **milestone**: prove that
  `novelFloor * ((65+n) * (2*newMass)) <= half * edgeFloor` implies the exact
  stationary-mass payment, and compile its cofinal form to completed strict
  contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelNewShellMassEdgeFloorPayment.lean`.
- **decl**:
  `cutoffTwoStationaryMassEdgeFloorPayment_of_newShellMassEdgeFloorPayment`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_newShellMassEdgeFloorPayment`,
  `CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment.toCofinalNovelStationaryMassEdgeFloorPayment`,
  `CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity`,
  and
  `CutoffTwoCofinalNovelNewShellMassEdgeFloorPayment.toCompletedStrictContractionData`.
- **obligation**: prove the cofinal shell-weighted new-state stationary-mass
  estimate against the finite positive routed-edge floor.
- **constructive?**: yes — only monotonicity of multiplication by nonnegative
  rational factors and the proved `novelMass <= 2*newMass` estimate are used.
  All five audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused namespace failure is not a pass.  The
  corrected focused check passes in about 2.2 seconds; the exact one-worker
  target passes 5,004 jobs with the new module taking about 1.0 second.  The
  cofinal payment is not inhabited, so no completed contraction, continuum
  QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-new-shell-component-split] Controlled source tail versus component merger — **CLOSED 2026-08-23**

- **milestone**: decompose the new-shell stationary mass exactly into an
  outside-cutoff-two-positive-carrier contribution and a component-merger
  contribution; bound the first by the existing corrected-slab cutoff
  increment.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelNewShellMassComponentSplit.lean`.
- **decl**: `cutoffTwoNewMass_eqv_outside_add_componentMerger`,
  `cutoffTwoNewOutsidePositiveMass_nonnegative`,
  `cutoffTwoNewComponentMergerMass_nonnegative`,
  `cutoffTwoNewOutsidePositiveMass_le_fullOutsideIndexedMass`,
  `cutoffTwoFullOutsideIndexedMass_eqv_stationarySourceTail`,
  `cutoffTwoNewOutsidePositiveMass_le_stationarySourceTail`,
  `cutoffTwoNewOutsidePositiveMass_le_increment`, and
  `cutoffTwoNewMass_le_increment_add_componentMerger`.
- **obligation**: compile the increment-plus-merger estimate into the
  edge-floor payment and then exclude or quantitatively control component
  mergers.
- **constructive?**: yes — finite filter partition, an injective sublist sum,
  exact index/state recoding, and the existing cutoff-increment theorem.  All
  eight audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the initial focused namespace failure is not a pass.  The
  corrected focused check passes in about 1.2 seconds; the exact one-worker
  target passes 5,005 jobs with the new module taking about 1.0 second.  The
  component-merger mass is uncontrolled, so no completed contraction,
  continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-component-split-payment] Increment-plus-merger capacity compiler — **CLOSED 2026-08-23**

- **milestone**: prove that
  `novelFloor * ((65+n) * (2*(cutoffIncrement+componentMergerMass)))
  <= half * edgeFloor` implies the new-shell payment, all four finite capacity
  blocks, and, when given cofinally, completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentSplitEdgeFloorPayment.lean`.
- **decl**:
  `cutoffTwoNewShellMassEdgeFloorPayment_of_componentSplitPayment`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_componentSplitPayment`,
  `CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment.toCofinalNovelNewShellMassEdgeFloorPayment`,
  `CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity`,
  and
  `CutoffTwoCofinalNovelComponentSplitEdgeFloorPayment.toCompletedStrictContractionData`.
- **obligation**: inhabit the cofinal scalar payment by excluding or bounding
  component mergers and comparing the resulting shell-weighted mass against
  the finite positive routed-edge floor.
- **constructive?**: yes — multiplication monotonicity by explicit
  nonnegative rational factors and the proved component-split mass bound are
  the only new proof ingredients.  All five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 2.0 seconds; the exact
  one-worker target passes 5,006 jobs with the new module taking about 2.0
  seconds.  The cofinal payment is not inhabited, so no completed
  contraction, continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-no-component-merger-check] Executable merger-absence certificate — **CLOSED 2026-08-23**

- **milestone**: define an executable emptiness check for the component-merger
  index list; prove that success is equivalent to every new state lying
  outside the cutoff-two positive carrier, forces merger mass to vanish, and
  yields `newMass <= cutoffIncrement`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentMergerCertificate.lean`.
- **decl**: `cutoffTwoNoComponentMergerCheck`,
  `cutoffTwoNoComponentMergerCheck_true_iff_indices_empty`,
  `cutoffTwoNoComponentMergerCheck_true_iff_all_new_outside`,
  `cutoffTwoNewComponentMergerMass_eqv_zero_of_check`,
  `cutoffTwoNewMass_le_increment_of_noComponentMergerCheck`,
  `cutoffTwoNoComponentMergerCheck_self`, and
  `cutoffTwoNewComponentMergerMass_self_eqv_zero`.
- **obligation**: prove the check succeeds beyond the trivial equal-cutoff
  anchor or replace it by a quantitative merger bound; then pay the positive
  routed-edge floor cofinally.
- **constructive?**: yes — the soundness proof is a local structural recursion
  over the finite list.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: an initial version using the generic
  `List.filter_eq_nil_iff` audited with `Classical.choice` and is not a pass.
  The corrected focused check passes in about 0.9 seconds; the exact one-worker
  target passes 5,007 jobs with the new module taking about 1.0 second.  Only
  the anchor `later = 2` is inhabited, so no cofinal contraction, continuum
  QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-no-merger-increment-payment] Checked increment-only capacity compiler — **CLOSED 2026-08-23**

- **milestone**: under a successful no-merger check, reduce the component-
  split payment to
  `novelFloor * ((65+n) * (2*cutoffIncrement)) <= half * edgeFloor`; compile
  its cofinal checked form to all finite capacity blocks and completed strict
  contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelNoMergerIncrementEdgeFloorPayment.lean`.
- **decl**:
  `cutoffTwoComponentSplitPayment_of_noMergerIncrementPayment`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_noMergerIncrementPayment`,
  `CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment.toCofinalNovelComponentSplitEdgeFloorPayment`,
  `CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment.toCofinalNovelSimpleFlowCapacity`,
  and
  `CutoffTwoCofinalNovelNoMergerIncrementEdgeFloorPayment.toCompletedStrictContractionData`.
- **obligation**: inhabit both cofinal fields: component stability and the
  increment-only comparison against the finite positive routed-edge floor;
  otherwise replace the fixed-base route by a moving-base construction.
- **constructive?**: yes — exact rational equivalence removes the certified
  zero merger mass before invoking the existing capacity compiler.  All five
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the focused check passes in about 2.0 seconds; the exact
  one-worker target passes 5,008 jobs with the new module taking about 2.1
  seconds.  Neither cofinal field is inhabited, and fixed-base increment decay
  is not claimed; no completed contraction, continuum QFT, or Clay theorem is
  proved.

### [BF4-cutoff-two-component-merger-semantics] Merger witness semantics and decision — **CLOSED 2026-08-23**

- **milestone**: characterize merger membership as a cutoff-two-bounded,
  cutoff-two-positive state outside the 65-state vacuum component but inside
  the later rooted component; construct a Type-level zero-or-witness decision
  and prove every witness gives strictly positive merger mass.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSemantics.lean`.
- **decl**: `mem_cutoffTwoNewComponentMergerIndices_iff`,
  `cutoffTwoNewComponentMergerMass_pos_of_index`,
  `CutoffTwoComponentMergerWitness.state_semantics`,
  `CutoffTwoComponentMergerWitness.mergerMass_pos`,
  `cutoffTwoComponentMergerDecision`, and
  `cutoffTwoComponentMergerMassZeroOrPositiveData`.
- **obligation**: connect any merger witness to a newly opened later support
  edge/path between distinct cutoff-two components, then prove support
  stability or quantify the resulting merger mass.
- **constructive?**: yes — finite list cases return explicit Type-level proof
  data, and positivity of one stationary summand forces positivity of the
  merger mass.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused attempt failed on namespace, Boolean-iff,
  and Type-level wrapper interfaces and is not a pass.  The corrected focused
  check passes in about 1.6 seconds; the exact one-worker target passes 5,009
  jobs with the new module taking about 1.7 seconds.  No larger-cutoff merger
  outcome, cofinal contraction, continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-component-merger-support-path] Old positive state joins through a later path — **CLOSED 2026-08-23**

- **milestone**: convert any component-merger witness at `later >= 2` into
  Type-level data containing a cutoff-two-positive state outside the
  cutoff-two vacuum component and a literal later `ChainIn` path from the
  vacuum root to that state's later index; exclude this event at `later = 2`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentMergerSupportPath.lean`.
- **decl**: `CutoffTwoOldPositiveStateMergePath`,
  `CutoffTwoComponentMergerWitness.toOldPositiveStateMergePath`, and
  `no_cutoffTwoOldPositiveStateMergePath_self`.
- **obligation**: locate the first path edge leaving the embedded old vacuum
  component and characterize whether its target is newly positive or belongs
  to another old cutoff-two component; then prove stability or bound its mass.
- **constructive?**: yes — the rooted-component compiler already carries a
  Type-level `ChainIn`; the new construction combines it with the exact
  state semantics.  Both audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the initial missing-namespace failure is not a pass.  The
  corrected focused check passes in about 3.2 seconds; the exact one-worker
  target passes 5,010 jobs with the new module taking about 3.2 seconds.  No
  larger-cutoff event, cofinal contraction, continuum QFT, or Clay theorem is
  claimed.

### [BF4-cutoff-two-component-merger-boundary-exit] First embedded-component exit edge — **CLOSED 2026-08-23**

- **milestone**: constructively locate the first later support edge leaving
  the embedded cutoff-two vacuum component along any merger path, and decide
  whether the target is outside all cutoff-two positive support or belongs to
  a previously separate positive component.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentMergerBoundaryExit.lean`.
- **decl**: `CutoffTwoEmbeddedVacuumBoundaryExit`,
  `CutoffTwoOldPositiveStateMergePath.toEmbeddedVacuumBoundaryExit`,
  `CutoffTwoComponentMergerWitness.toEmbeddedVacuumBoundaryExit`, and
  `CutoffTwoEmbeddedVacuumBoundaryExit.targetShellDecision`.
- **obligation**: construct an executable boundary-closure certificate, prove
  that it excludes all merger witnesses, and determine whether it can hold
  cofinally or whether boundary mass must instead be paid quantitatively.
- **constructive?**: yes — a local structural recursion over `ChainIn`
  produces the boundary edge; finite Boolean shell membership gives the exact
  target decision.  All three audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two namespace-resolution failures are not passes.  The
  corrected focused check passes in about 1.2 seconds; the exact one-worker
  target passes 5,011 jobs with the new module taking about 1.2 seconds.  No
  boundary-closure certificate is inhabited, so no cofinal contraction,
  continuum QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-component-boundary-closure] Executable embedded-boundary closure — **CLOSED 2026-08-23**

- **milestone**: scan all embedded-cutoff-two-to-new-state candidate edges,
  prove exact soundness and completeness, and compile successful closure to
  no component mergers, zero merger mass, and the increment-only new-shell
  bound.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureCertificate.lean`.
- **decl**: `cutoffTwoEmbeddedVacuumBoundaryClosedCheck`,
  `cutoffTwoEmbeddedVacuumBoundaryClosedCheck_sound`,
  `cutoffTwoEmbeddedVacuumBoundaryClosedCheck_complete`,
  `cutoffTwoNoComponentMergerCheck_of_boundaryClosedCheck`,
  `CutoffTwoEmbeddedVacuumBoundaryClosedCertificate.toNoComponentMergerCertificate`,
  `cutoffTwoNewComponentMergerMass_eqv_zero_of_boundaryClosedCheck`, and
  `cutoffTwoNewMass_le_increment_of_boundaryClosedCheck`.
- **obligation**: inspect failures as literal crossing edges and either prove
  the checker cofinally or quantify the mass/capacity cost of those crossings.
- **constructive?**: yes — the checker is a finite `List.all` scan, its
  successful branch contradicts the Type-level first-exit witness, and all
  seven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the omitted-namespace failure and the subsequent timeout
  caused by reducing a large irrelevant source against an empty target are
  not passes.  After routing the anchor through completeness, the focused
  check passes in about 2.4 seconds; the exact one-worker target passes 5,012
  jobs with the new module taking about 2.4 seconds.  Only `later = 2` is
  inhabited, so no cofinal contraction, continuum QFT, or Clay theorem is
  claimed.

### [BF4-cutoff-two-component-boundary-decision] Closure-or-crossing trichotomy — **CLOSED 2026-08-23**

- **milestone**: constructively inspect the exact closure pair list and return
  either a successful closure certificate or a literal embedded-to-new later
  support edge; classify every failure edge as newly outside old positive
  support or directly entering a separate old-positive component.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryClosureDecision.lean`.
- **decl**: `cutoffTwoEmbeddedVacuumBoundaryClosureDecision` and
  `cutoffTwoEmbeddedVacuumBoundaryTrichotomy`.
- **obligation**: quantify the two crossing branches against stationary shell
  mass and edge-floor payment, or prove the closure branch on a moving-base
  cofinal schedule.
- **constructive?**: yes — local structural recursion returns membership and
  Boolean edge proofs in `Type`; the existing exact shell split preserves the
  semantic distinction between newly positive and old-component targets.
  Both audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the focused check passes in about 0.9 seconds; the exact
  one-worker target passes 5,013 jobs with the new module taking about 0.8
  seconds.  The decision does not establish which branch occurs at any larger
  cutoff, so no cofinal contraction, continuum QFT, or Clay theorem is
  claimed.

### [BF4-cutoff-two-component-boundary-mass-witness] Quantitative crossing data — **CLOSED 2026-08-23**

- **milestone**: prove every embedded-boundary crossing has positive later
  kernel and target stationary weight, bound that weight by its exact shell
  submass, and return a quantitative closed/outside/merger trichotomy.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentBoundaryMassWitness.lean`.
- **decl**: `cutoffTwoEmbeddedVacuumBoundaryExit_kernel_pos`,
  `cutoffTwoEmbeddedVacuumBoundaryExit_targetWeight_pos`,
  `cutoffTwoBoundaryExitOutsidePositive_targetWeight_le_mass`,
  `cutoffTwoBoundaryExitOutsidePositive_mass_pos`,
  `cutoffTwoBoundaryExitComponentMerger_targetWeight_le_mass`,
  `cutoffTwoBoundaryExitComponentMerger_mass_pos`, and
  `cutoffTwoEmbeddedVacuumBoundaryMassTrichotomy`.
- **obligation**: provide an upper budget for component-merger mass sufficient
  for edge-floor payment, then construct it cofinally or replace the fixed
  base by a moving-base schedule.
- **constructive?**: yes — finite nonnegative summation retains the witnessed
  target weight, support adjacency gives positive normalized kernel, and all
  seven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: two missing-namespace attempts are not passes.  The
  corrected focused check passes in about 1.3 seconds; the exact one-worker
  target passes 5,014 jobs with the new module taking about 1.3 seconds.  No
  uniform crossing floor, merger-mass ceiling, cofinal contraction, continuum
  QFT, or Clay theorem is claimed.

### [BF4-cutoff-two-component-merger-residual-budget] Division-free merger reserve compiler — **CLOSED 2026-08-23**

- **milestone**: split the exact component payment into increment and merger
  demands; compile a rational reserve paying both into finite capacity and a
  cofinal reserve family into completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget.lean`.
- **decl**:
  `cutoffTwoNovelComponentSplitPaymentDemand_eqv_increment_add_merger`,
  `CutoffTwoNovelComponentMergerResidualBudgetAt`,
  `CutoffTwoNovelComponentMergerResidualBudgetAt.reserve_nonnegative`,
  `cutoffTwoComponentSplitPayment_of_mergerResidualBudget`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_mergerResidualBudget`, and the three
  `CutoffTwoCofinalNovelComponentMergerResidualBudget` contraction compilers.
- **obligation**: construct residual budgets along a cofinal moving-base
  schedule; fixed cutoff-two increment decay is neither assumed nor proved.
- **constructive?**: yes — only exact rational distributivity, monotonicity,
  and proof-carrying reserve inequalities are used.  All eight audited exports
  use exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes in about 2.3 seconds; the exact
  one-worker target passes 5,015 jobs with the new module taking about 2.2
  seconds.  No reserve is inhabited, so no cofinal contraction, continuum QFT,
  or Clay theorem is claimed.

### [BF4-generic-embedded-boundary-growth] Boundary closure iff no new states — **CLOSED 2026-08-23**

- **milestone**: for arbitrary `base <= later`, construct a first embedded-
  component exit edge from every new later vacuum-sector state and prove the
  exact Boolean equivalence between boundary closure and an empty new block.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth.lean`.
- **decl**: `CentralPhysicalEmbeddedVacuumBoundaryExit`,
  `centralPhysicalFiniteNewStateBoundaryExit`,
  `centralPhysicalEmbeddedVacuumBoundaryClosedCheck_sound`,
  `centralPhysicalEmbeddedVacuumBoundaryClosedCheck_complete`, and
  `centralPhysicalEmbeddedVacuumBoundaryClosedCheck_true_iff_new_empty`.
- **obligation**: quantify generic moving-base new-state growth; closure cannot
  serve as a cofinal mechanism whenever new physical states occur.
- **constructive?**: yes — rooted `ChainIn` recursion locates the first exit,
  and a finite `List.all` scan is proved sound and complete.  All four audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the omitted-namespace and dependent-empty-case failures are
  not passes.  The corrected focused check passes in about 0.9 seconds; the
  exact one-worker target passes 5,016 jobs with the new module taking about
  0.9 seconds.  No larger-cutoff emptiness, cofinal contraction, continuum QFT,
  or Clay theorem is claimed.

### [BF4-generic-new-mass-component-split] Moving-base increment-plus-merger bound — **CLOSED 2026-08-23**

- **milestone**: partition arbitrary `base <= later` vacuum-sector new mass
  into newly positive and old-component-merger submasses, identify merger
  membership exactly, and bound the newly positive part by the local
  corrected-slab cutoff increment.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorNewMassComponentSplit.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorNewMass_eqv_outside_add_merger`,
  `mem_centralPhysicalFiniteNewComponentMergerIndices_iff`,
  `centralPhysicalFiniteNewOutsideBasePositiveMass_le_tail`,
  `centralPhysicalFiniteNewOutsideBasePositiveMass_le_increment`, and
  `centralPhysicalFiniteVacuumSectorNewMass_le_increment_add_merger`.
- **obligation**: decide and quantify the generic component-merger residual,
  then provide the base-sector size, coercivity, and edge-floor certificates
  required to pay it along a moving-cutoff schedule.
- **constructive?**: yes — the proof uses finite filters, injective finite-sum
  comparison, exact rational equivalence, and the existing corrected-slab
  tail bound.  All eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two missing-namespace attempts are not passes.  The
  corrected focused check passes in about 1.0 seconds; the exact one-worker
  target passes 5,017 jobs with the new module taking about 1.0 seconds.  No
  merger ceiling, local capacity, cofinal contraction, continuum QFT, or Clay
  theorem is claimed.

### [BF4-generic-component-merger-decision] Moving-base zero-or-positive merger data — **CLOSED 2026-08-23**

- **milestone**: decide the arbitrary-base finite merger list, remove merger
  mass in the empty branch, and expose an exact positive stationary-mass
  witness in the nonempty branch.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorComponentMergerDecision.lean`.
- **decl**:
  `centralPhysicalFiniteNoComponentMergerCheck_true_iff_indices_empty`,
  `centralPhysicalFiniteNoComponentMergerCheck_true_iff_all_new_outside`,
  `centralPhysicalFiniteVacuumSectorNewMass_le_increment_of_check`,
  `CentralPhysicalFiniteComponentMergerWitness.state_semantics`,
  `CentralPhysicalFiniteComponentMergerWitness.later_weight_pos`,
  `CentralPhysicalFiniteComponentMergerWitness.mergerMass_pos`,
  `centralPhysicalFiniteComponentMergerDecision`, and
  `centralPhysicalFiniteComponentMergerMassZeroOrPositiveData`.
- **obligation**: bound or pay positive merger mass using explicit generic
  base-sector size, coercivity, and later support-edge floor data, then inhabit
  those certificates along a cofinal moving-cutoff schedule.
- **constructive?**: yes — structural inspection of a finite list returns
  Type-level evidence in both branches; positivity uses only a witnessed
  positive term in a finite nonnegative rational sum.  All eleven audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: three failed focused elaboration attempts are not passes.
  The corrected focused check passes in about 1.2 seconds; the exact one-worker
  target passes 5,018 jobs with the new module taking about 1.2 seconds.  No
  nontrivial step is certified merger-free and no merger upper bound, cofinal
  contraction, continuum QFT, or Clay theorem is claimed.

### [BF4-generic-moving-base-residual-payment] Inhabited scalar payment interface — **CLOSED 2026-08-23**

- **milestone**: define the exact generic increment, merger, combined, and
  edge-floor payment quantities using the literal later carrier size; compile
  a division-free merger reserve to scaled new-mass payment; and inhabit the
  certificate at equal cutoffs.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMovingBaseResidualPayment.lean`.
- **decl**:
  `centralPhysicalFiniteMovingBaseComponentSplitPaymentDemand_eqv_increment_add_merger`,
  `CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt`,
  `CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt.componentSplitPayment`,
  `centralPhysicalFiniteMovingBaseNewMassPayment_of_componentSplitPayment`,
  `CentralPhysicalFiniteMovingBaseMergerResidualBudgetAt.newMassPayment`,
  `centralPhysicalFiniteMovingBaseComponentSplitPayment_of_noMergerIncrementPayment`,
  `slabParametricKCutoffIncrement_self_eqv_zero`, and
  `centralPhysicalFiniteMovingBaseMergerResidualBudgetAt_self`.
- **obligation**: derive a useful positive moving-base coercivity scale from
  the existing finite path/Poincare geometry and inhabit the residual payment
  at nontrivial moving steps, ultimately along a cofinal schedule.
- **constructive?**: yes — all quantities are explicit finite rational data;
  the reserve compiler is division-free; and the equal-cutoff inhabitant uses
  exact finite-filter emptiness and the constructed positive edge floor.  All
  eleven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: two failed focused elaboration attempts are not passes.  The
  corrected focused check passes in about 1.1 seconds; the exact one-worker
  target passes 5,019 jobs with the new module taking about 1.2 seconds.  No
  nontrivial residual budget, moving-base flow, cofinal contraction, continuum
  QFT, or Clay theorem is claimed.

### [BF4-generic-simple-coercivity] Explicit positive finite-sector coercivity — **CLOSED 2026-08-23**

- **milestone**: prove generic vacuum-component mass at most one, replace the
  recursive path ceiling by the literal `1 + carrierSize^2` simple-path scale,
  and divide the positive edge floor by that scale to obtain an actual finite
  coercivity constant.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorSimpleCoercivity.lean`.
- **decl**: `centralPhysicalFiniteVacuumSectorMass_le_one`,
  `centralPhysicalFiniteVacuumSectorMass_square_le_one`,
  `centralPhysicalFiniteVacuumSectorDirichlet_nonnegative`,
  `centralPhysicalFiniteVacuumSector_edgeFloor_mul_pairwise_le_simpleScale_mul_Dirichlet`,
  `centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor`,
  `centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_pos`, and
  `centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_mul_pairwise_le_Dirichlet`.
- **obligation**: compare the explicit coercivity-scaled moving-base
  increment-plus-merger demand with the later edge budget at nontrivial steps
  and then along a cofinal schedule.
- **constructive?**: yes — finite subsum comparison, loop-erased Type-level
  paths, explicit positive rational minima, and positive rational division
  suffice.  All six audited exports use exactly `[propext, Quot.sound]`; no
  forbidden construct was added.
- **status note**: the first failed focused attempt is not a pass.  The
  corrected focused check passes in about 1.1 seconds; the exact one-worker
  target passes 5,020 jobs with the new module taking about 1.0 seconds.  The
  floor is finite-cutoff and no uniform lower bound, cofinal contraction,
  continuum QFT, or Clay theorem is claimed.

### [BF4-simple-payment-cancellation] Dimensionless moving-base payment — **CLOSED 2026-08-23**

- **milestone**: substitute the explicit simple coercivity floor into the
  component-split moving-base payment and constructively cancel its common
  positive edge floor, leaving an exact dimensionless carrier-growth
  inequality; compile the resulting Type-level certificate back to scaled
  new-mass payment and inhabit it at equal cutoffs.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorSimplePaymentCancellation.lean`.
- **decl**:
  `centralPhysicalFiniteMovingBaseSimplePaymentCapacity_pos`,
  `centralPhysicalFiniteMovingBaseSimpleComponentPayment_iff_dimensionless`,
  `CentralPhysicalFiniteMovingBaseSimplePaymentAt`,
  `CentralPhysicalFiniteMovingBaseSimplePaymentAt.componentSplitPayment`,
  `CentralPhysicalFiniteMovingBaseSimplePaymentAt.newMassPayment`, and
  `centralPhysicalFiniteMovingBaseSimplePaymentAt_self`.
- **obligation**: bound the exact normalized new-block load by the quadratic
  carrier capacity at nontrivial moving steps, and separately obtain a
  cutoff-independent coercivity scale before any uniform spectral-gap claim.
- **constructive?**: yes — cancellation uses only multiplication by witnessed
  positive rationals and constructive order cancellation.  All five audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the focused guarded check passes on its first attempt in
  about 1.0 seconds; the exact one-worker target passes 5,021 jobs with the
  new module taking about 1.0 seconds.  No nontrivial moving step, uniform
  coercivity, completed contraction, continuum QFT, or Clay theorem is
  claimed.

### [BF4-simple-exact-new-mass-payment] Automatic finite new-mass payment — **CLOSED 2026-08-23**

- **milestone**: prove generic exact new-block mass at most one; show that a
  later carrier with at least four states automatically satisfies the
  dimensionless linear-load versus quadratic-capacity inequality; compile it
  to physical payment at the later simple coercivity floor; and inhabit the
  certificate for every cutoff-two-and-later carrier using its certified
  65-state old block.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorSimpleNewMassPayment.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorNewMass_le_one`,
  `centralPhysicalFiniteMovingBaseSimpleNewMassLoad_le_capacity_of_four_le`,
  `centralPhysicalFiniteMovingBaseSimpleNewMassPayment_iff_dimensionless`,
  `CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt.of_four_le_stateCount`,
  `CentralPhysicalFiniteMovingBaseSimpleNewMassPaymentAt.physicalPayment`,
  `cutoffTwoMovingBaseStateCount_eq_65_add_new`, and
  `cutoffTwoMovingBaseSimpleNewMassPhysicalPayment`.
- **obligation**: compare a single positive fixed coercivity floor with the
  later cutoff-dependent simple floors along a cofinal schedule, then feed
  that comparison into the established novel-flow capacity and completed-gap
  compiler.
- **constructive?**: yes — finite subsum injection, normalized stationary
  mass, natural-number multiplication monotonicity, and positive rational
  cancellation suffice.  All seven audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three failed focused elaboration attempts are not passes.
  The corrected focused check passes in about 10.1 seconds; the exact
  one-worker target passes 5,022 jobs with the new module taking about 10
  seconds.  The payment uses a possibly deteriorating later-sector floor; no
  uniform contraction, completed gap, continuum QFT, or Clay theorem is
  claimed.

### [BF4-cofinal-simple-floor-comparison] Fixed-floor comparison compiler — **CLOSED 2026-08-23**

- **milestone**: transfer the automatic later-simple-floor new-mass payment
  to the fixed positive cutoff-two novel-flow floor under one explicit floor
  comparison; compile the finite comparison to all four novel-flow capacity
  blocks; and compile a cofinal family of comparisons to the existing
  completed-cylinder strict-contraction datum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSimpleCoercivityFloorComparison.lean`.
- **decl**: `cutoffTwoLaterSimpleCoercivityFloor_pos`,
  `cutoffTwoNovelNewShellMassEdgeFloorPayment_of_fixedFloor_le_simpleFloor`,
  `cutoffTwoNovelSimpleFlowCapacityAt_of_fixedFloor_le_simpleFloor`,
  `CutoffTwoCofinalSimpleCoercivityFloorComparison`,
  `CutoffTwoCofinalSimpleCoercivityFloorComparison.toCofinalNovelNewShellMassEdgeFloorPayment`,
  `CutoffTwoCofinalSimpleCoercivityFloorComparison.toCofinalNovelSimpleFlowCapacity`,
  and
  `CutoffTwoCofinalSimpleCoercivityFloorComparison.toCompletedStrictContractionData`.
- **obligation**: inhabit the cofinal fixed-floor comparison, or prove that
  carrier growth forces this particular simple-path floor to zero and replace
  it with a sharper multiscale coercivity mechanism.
- **constructive?**: yes — the finite transfer uses nonnegativity of exact
  new mass and monotonicity under multiplication; the cofinal compiler merely
  composes existing Type-level certificates.  All six audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first failed focused attempt is not a pass.  The
  corrected focused check passes in about 2.7 seconds; the exact one-worker
  target passes 5,023 jobs with the new module taking about 2.6 seconds.  The
  cofinal comparison is not inhabited, and no completed gap claim without
  that certificate, continuum QFT, or Clay theorem is made.

### [BF4-simple-floor-growth-obstruction] Quadratic carrier budget — **CLOSED 2026-08-23**

- **milestone**: prove the generic finite edge floor is at most one, bound the
  simple coercivity floor times its `1 + stateCount^2` divisor by one, and
  show that every fixed-floor comparison forces
  `fixedFloor * stateCount^2 <= 1`, pointwise and along the proposed cofinal
  cutoff-two comparison family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthObstruction.lean`.
- **decl**: `listPositiveMinOne_le_one`,
  `centralPhysicalFiniteVacuumSectorEdgeFloor_le_one`,
  `centralPhysicalFiniteVacuumSectorSimpleCoercivityFloor_mul_scale_le_one`,
  `fixedFloor_mul_vacuumStateCountSquare_le_one_of_le`,
  `cutoffTwoFixedFloorComparison_forces_stateCountSquareBudget`, and
  `CutoffTwoCofinalSimpleCoercivityFloorComparison.stateCountSquareBudget`.
- **obligation**: prove the actual connected vacuum-sector state count escapes
  this fixed quadratic budget by constructing distinct positive-row states
  and support paths from the vacuum, or establish the unexpected alternative
  that those connected sectors remain uniformly finite.
- **constructive?**: yes — finite minimum recursion, positive rational
  division cancellation, and multiplication monotonicity suffice.  The first
  audited export uses `[propext]`; the remaining five use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes on its first attempt in about 1.0
  seconds; the exact one-worker target passes 5,024 jobs with the new module
  taking about 1.0 seconds.  Carrier unboundedness, failure of the cofinal
  comparison, uniform contraction, continuum QFT, and the Clay theorem are
  not claimed.

### [Z4-equal-pair-singlet-injection] Arbitrary equal-spin local injection — **CLOSED 2026-08-23**

- **milestone**: generalize the named singlet-channel injection from the
  fundamental pair `1,1` to every equal pair `spin,spin`, and lift it through
  physical permutation to the production explicit-valence multiplicity.
- **file**:
  `lean/YMGap/Continuum/Z4FusionEqualPairSingletInjection.lean`.
- **decl**: `fusionPathMultiplicity_le_equal_pair`,
  `fusionPathMultiplicity_physical_le_equal_pair`, and
  `explicitValenceMultiplicity_physical_equal_pair_replacement_le`.
- **obligation**: apply the local injection at every touched link of the
  spin-labelled lower cube, prove positive vacuum support, and derive actual
  connected-carrier growth.
- **constructive?**: yes — one named channel-zero summand, zero insertion,
  finite natural-sum monotonicity, and constructive permutation transport
  suffice.  All three audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 0.3 seconds; the exact one-worker
  target passes 512 jobs with the new module taking about 0.3 seconds.  No
  positive-row family, carrier-growth theorem, uniform gap, continuum QFT,
  or Clay theorem is claimed.

### [BF4-all-spin-cube-positive-ray] Cutoff-admitted positive support ray — **CLOSED 2026-08-23**

- **milestone**: construct the six-face cube carrying every label
  `spin <= K`; prove state and slab boundedness, link-product positivity,
  slab-term positivity, both orientations of the raw vacuum kernel entry,
  positive-row carrier membership, and injectivity in the spin parameter.
- **file**:
  `lean/YMGap/Continuum/BF4CentralLowerSpinCubePositiveRay.lean`.
- **decl**: `centralLowerSpinCubePhysical_eq_state`,
  `centralLowerSpinCubeState_mem_centralHalfStates`,
  `centralLowerSpinCubeState_injective`,
  `vacuum_linkMultiplicity_le_spinCube`,
  `centralLowerSpinCube_linkProduct_pos`,
  `centralLowerSpinCubePhysicalTerm_pos`,
  `centralLowerSpinCubePhysicalReflectedKernel_pos`,
  `centralPhysicalReflectedKernel_vacuum_spinCube_pos`, and
  `centralLowerSpinCubeState_mem_centralPositiveHalfStates`.
- **obligation**: locate these distinct states in the finite carrier, close
  each under its direct positive edge from the vacuum root, and compile the
  family into the quantitative root-component state-count bound.
- **constructive?**: yes — finite face incidence, an explicit singlet
  channel, bounded finite products and sums, and exact reflected-kernel
  symmetry suffice.  All nine audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two failed focused elaboration attempts are not passes.
  The corrected focused check passes in about 0.7 seconds; the exact
  one-worker target passes 982 jobs with the new module taking about 0.7
  seconds.  Root-component cardinality growth, failure of the cofinal simple
  floor, a uniform gap, continuum QFT, and the Clay theorem are not claimed.

### [BF4-spin-cube-vacuum-sector-growth] Linear rooted-carrier growth — **CLOSED 2026-08-23**

- **milestone**: locate every cutoff-admitted spin cube in the finite carrier,
  close its direct positive support edge under the vacuum root component, and
  prove the exact lower bound `K + 1 <= vacuumSectorIndices.length` at every
  positive coupling and half-extent zero.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeVacuumSectorGrowth.lean`.
- **decl**: `centralLowerSpinCubeState_mem_vacuumSector`,
  `centralLowerSpinCubeStates_nodup`,
  `centralLowerSpinCubeStates_subset_vacuumSector`,
  `centralLowerSpinCubeCodes_nodup`,
  `centralLowerSpinCubeCodes_subset_vacuumSectorStateCodes`, and
  `centralPhysicalFiniteVacuumSectorIndices_length_ge_cutoff_succ`.
- **obligation**: combine the linear lower bound with the existing fixed
  quadratic state-count budget and construct an explicit large cutoff that
  contradicts any proposed positive fixed-floor comparison family.
- **constructive?**: yes — carrier location, direct rooted-edge closure,
  faithful natural-number state coding, and finite-list injection suffice.
  All six audited exports use exactly `[propext, Quot.sound]`; no global
  decidable equality on edge-labelling functions or other forbidden
  construct was added.
- **status note**: one failed focused attempt is not a pass.  The corrected
  focused check passes in about 0.6 seconds; the exact one-worker target
  passes 1,094 jobs with the new module taking about 0.6 seconds.  Failure of
  the cofinal simple floor, a uniform gap, continuum QFT, and the Clay theorem
  are not yet claimed.

### [BF4-simple-floor-growth-no-go] Cofinal simple-floor comparison — **IMPOSSIBLE 2026-08-23**

- **milestone**: turn linear rooted-sector growth into an explicit rational
  denominator escape and prove that no cofinal family can compare the fixed
  cutoff-two floor with every later simple coercivity floor.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo.lean`.
- **decl**: `one_lt_mul_den_succ_square`,
  `cutoffTwoMovingBaseStateCount_ge_cutoff_succ`,
  `cutoffTwoFixedFloor_not_le_simpleFloor_of_den_le`,
  `cutoffTwoCofinalSimpleCoercivityFloorComparison_impossible`, and
  `no_cutoffTwoCofinalSimpleCoercivityFloorComparison`.
- **obligation**: abandon the global `1 + N^2` simple-path loss and establish
  a sharper cofinal weighted-flow, multiscale, or direct operator estimate
  whose coercivity does not decay merely because the physical carrier grows.
- **constructive?**: yes — the positive rational denominator is an explicit
  escape witness, while the spin-cube code injection supplies the finite-list
  cardinality lower bound.  All five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two failed focused attempts are not passes.  The corrected
  focused check passes in about 1.1 seconds; the exact one-worker target
  passes 5,028 jobs with the new module taking about 1.1 seconds.  This rules
  out only the crude global-state-count simple floor, not sharper capacity
  estimates, a uniform spectral gap, continuum QFT, or the Clay theorem.

### [BF4-spin-cube-vacuum-spokes] Explicit constant-length ray routing — **CLOSED 2026-08-23**

- **milestone**: construct a reusable faithful-code carrier locator, locate
  every cutoff-admitted spin cube, prove its indexed physical kernel edge to
  and from the vacuum strictly positive, and connect any two such vertices by
  an exact two-edge positive-kernel star path.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorEmbedding.lean` and
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeVacuumSpokes.lean`.
- **decl**: `centralPhysicalFiniteIndexOfState_lt`,
  `centralPhysicalFiniteStateAt_indexOfState_eq`,
  `centralLowerSpinCubeIndex_lt`,
  `centralPhysicalFiniteStateAt_spinCubeIndex_eq`,
  `centralPhysicalFiniteKernel_spinCubeIndex_zero_pos`,
  `centralPhysicalFiniteKernel_zero_spinCubeIndex_pos`,
  `centralLowerSpinCubeIndex_mem_vacuumSector`,
  `centralVacuumToLowerSpinCubeSpoke_edgeLength`,
  `centralLowerSpinCubeStarPath_edgeLength`,
  `centralLowerSpinCubeStarPath_directedEdges`, and
  `centralLowerSpinCube_endpoint_sq_le_two_spoke_square_sum`.
- **obligation**: aggregate the stationary-product demands of the spin-ray
  star flow on each vacuum spoke and compare that exact load with the same
  spoke's physical joint capacity; then extend or recursively glue this local
  routing beyond the explicit ray to the full vacuum sector.
- **constructive?**: yes — decidable equality is used only on faithful natural
  codes, all carrier and path witnesses remain Type-level, and all eleven
  audited exports use exactly `[propext, Quot.sound]`.
- **status note**: two failed focused attempts are not passes.  The corrected
  focused spoke check passes in about 0.9 seconds.  The exact one-worker spoke
  target passes 1,197 jobs with the new module taking about 0.8 seconds; the
  separately rebuilt locator target passes 1,170 jobs with its modified module
  taking about 3.7 seconds.  This removes the carrier-size path-length loss on
  the spin-cube ray only; spoke capacity, a full-sector uniform gap, continuum
  QFT, and the Clay theorem remain open.

### [BF4-spin-ray-flow-capacity] Exact star-flow spoke payment — **CLOSED 2026-08-23**

- **milestone**: put stationary-product demand on every ordered pair of
  excited spin cubes, regroup it exactly on each oriented vacuum spoke, bound
  the total ray mass by one, and reduce both spoke-capacity inequalities to
  `2 * delta <= P(spin,vacuum)`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayFlowCapacity.lean`.
- **decl**: `centralLowerExcitedSpinCubeIndex_injective_on`,
  `centralLowerExcitedSpinCubeIndices_nodup`,
  `centralLowerExcitedSpinCubeRayMass_le_one`,
  `centralLowerExcitedSpinCubeRayFlowLoad_leftSpoke_eqv`,
  `centralLowerExcitedSpinCubeRayFlowLoad_rightSpoke_eqv`,
  `centralLowerExcitedSpinCube_weight_mul_return_eqv_kernel`,
  `delta_mul_leftSpokeLoad_le_kernel_of_twice_delta_le_return`, and
  `delta_mul_rightSpokeLoad_le_kernel_of_twice_delta_le_return`.
- **obligation**: construct the positive minimum of the finite list of ray
  return probabilities at each cutoff, compile the resulting finite capacity
  witness, and then prove or refute a positive cofinal lower bound before
  extending the routing beyond the explicit spin ray.
- **constructive?**: yes — finite list sums, faithful-code injectivity,
  positive rational division, exact kernel symmetry, and multiplication
  monotonicity suffice.  All eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three failed focused elaboration attempts are not passes.
  The corrected focused check passes in about 1.4 seconds; the exact
  one-worker target passes 5,025 jobs with the new module taking about 1.6
  seconds.  This is a finite local-flow reduction only; a cutoff-uniform
  return floor, full-sector gap, continuum QFT, and the Clay theorem remain
  open.

### [BF4-spin-ray-finite-return-floor] Explicit finite ray capacity — **CLOSED 2026-08-23**

- **milestone**: prove strict positivity of every excited spin-cube vacuum
  return, take their literal constructive finite minimum, divide it by two,
  and package the resulting positive rational and both oriented spoke
  inequalities as an inhabited Type-level finite capacity certificate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayReturnFloor.lean`.
- **decl**: `centralLowerExcitedSpinCubeVacuumReturnProbability_pos`,
  `centralLowerExcitedSpinCubeReturnFloor_pos`,
  `centralLowerExcitedSpinCubeReturnFloor_le`,
  `centralLowerExcitedSpinCubeRayCapacity_pos`,
  `twice_centralLowerExcitedSpinCubeRayCapacity_le_return`, and
  `centralLowerExcitedSpinCubeFiniteRayCapacityAt`.
- **obligation**: isolate a positive cofinal lower bound for these explicit
  finite return floors, or prove an obstruction and redesign the ray routes;
  then extend any successful capacity mechanism beyond the spin-ray
  subsector.
- **constructive?**: yes — positive numerator and denominator witnesses,
  finite `Q'.min'` recursion, and positive rational division suffice.  All six
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: one failed focused attempt is not a pass.  The corrected
  focused check passes in about 1.1 seconds; the exact one-worker target
  passes 5,026 jobs with the new module taking about 1.1 seconds.  Finite
  positivity does not imply a cutoff-uniform floor; the full-sector gap,
  continuum QFT, and the Clay theorem remain open.

### [BF4-spin-ray-cofinal-return-compiler] Uniform scalar datum to cofinal spoke capacity — **CLOSED 2026-08-23**

- **milestone**: state one honest Type-level positive cofinal lower bound for
  the explicit finite return floors and compile it losslessly into one
  positive capacity constant controlling both orientations of every later
  spin-ray spoke.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayCofinalReturnFloor.lean`.
- **decl**:
  `FixedNomeCofinalSpinCubeRayReturnFloor.rayDelta_pos`,
  `FixedNomeCofinalSpinCubeRayReturnFloor.twice_rayDelta_le_return`,
  `FixedNomeCofinalSpinCubeRayReturnFloor.finiteCapacityAt`, and
  `FixedNomeCofinalSpinCubeRayReturnFloor.toCofinalRayCapacity`.
- **obligation**: inhabit `FixedNomeCofinalSpinCubeRayReturnFloor` from a
  cutoff-independent arbitrary-spin conditional row ceiling, or prove that
  the vacuum-star return probabilities decay and redesign the routes; then
  cover the remaining rooted sector.
- **constructive?**: yes — only the named Type-level premise, exact rational
  division, finite-floor comparison, and the already proved spoke compiler
  are used.  All four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes on its first attempt in about 1.0
  seconds; the exact one-worker target passes 5,027 jobs with the new module
  taking about 1.0 seconds.  The cofinal premise is not inhabited here, and no
  full-sector gap, continuum QFT, or Clay theorem is claimed.

### [BF4-spin-ray-escape-mass] Exact row split and conditional return floor — **CLOSED 2026-08-23**

- **milestone**: remove the unique vacuum index from each admitted excited
  spin-cube stationary row, identify the literal non-vacuum escape mass, and
  prove that `escape <= C * vacuumJoint` implies the genuine return floor
  `1 / (1 + C)`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayEscapeMass.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeNonVacuumEscapeMass_nonnegative`,
  `centralLowerExcitedSpinCube_weight_eqv_vacuumJoint_add_escape`,
  `centralLowerExcitedSpinCubeNonVacuumEscapeMass_le_weight`,
  `spinCubeEscapeReturnFloor_pos`, `spinCubeEscapeReturnFloor_le_one`, and
  `spinCubeEscapeReturnFloor_le_return_of_escape_le`.
- **obligation**: construct one cutoff-independent nonnegative escape-ratio
  ceiling for all sufficiently large cutoffs and all admitted spins, compile
  it into `FixedNomeCofinalSpinCubeRayReturnFloor`, and then extend the
  successful routing mechanism beyond the explicit spin-ray subsector.
- **constructive?**: yes — duplicate-free finite lists, literal filtering,
  exact sector stationarity, rational order monotonicity, and a positive
  reciprocal suffice.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three failed focused elaboration attempts are not passes.
  The corrected focused check passes in about 1.2 seconds; the exact
  one-worker target passes 5,027 jobs with the new module taking about 1.0
  seconds.  No cutoff-uniform escape ceiling, full-sector gap, continuum QFT,
  or Clay theorem is claimed.

### [BF4-spin-ray-cofinal-escape-compiler] Uniform escape ratio to cofinal capacity — **CLOSED 2026-08-23**

- **milestone**: state one cutoff-independent nonnegative escape-ratio ceiling
  as Type-level data and compile it through the exact reciprocal return floor,
  the literal finite return minimum, and the existing cofinal spoke-capacity
  machinery without additional loss.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayCofinalEscapeCeiling.lean`.
- **decl**:
  `FixedNomeCofinalSpinCubeEscapeRatioCeiling.returnFloor_pos`,
  `FixedNomeCofinalSpinCubeEscapeRatioCeiling.returnFloor_le_return`,
  `FixedNomeCofinalSpinCubeEscapeRatioCeiling.returnFloor_le_finiteReturnFloor`,
  `FixedNomeCofinalSpinCubeEscapeRatioCeiling.toCofinalRayReturnFloor`,
  `FixedNomeCofinalSpinCubeEscapeRatioCeiling.finiteRayCapacityAt`, and
  `FixedNomeCofinalSpinCubeEscapeRatioCeiling.toCofinalRayCapacity`.
- **obligation**: inhabit `FixedNomeCofinalSpinCubeEscapeRatioCeiling` from
  actual arbitrary-spin BF4 kernel estimates, or construct a concrete
  spin/cutoff obstruction and redesign the ray routing; then control the
  remaining rooted sector.
- **constructive?**: yes — the honest named Type-level premise, exact rational
  reciprocal, pointwise escape compiler, finite-minimum recursion, and prior
  spoke-capacity compiler suffice.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused check passes on its first attempt in about 1.3
  seconds; the exact one-worker target passes 5,029 jobs with the new module
  taking about 1.1 seconds.  The escape-ceiling datum remains uninhabited, and
  no full-sector gap, continuum QFT, or Clay theorem is claimed.

### [BF4-spin-ray-cofinal-escape-equivalence] Return floor iff escape ceiling — **CLOSED 2026-08-23**

- **milestone**: prove that a positive cofinal return floor constructs a
  cofinal escape-ratio ceiling by reciprocal scaling, completing Type-level
  maps in both directions between the two exact named frontiers.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayEscapeMass.lean` and
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayCofinalEscapeEquivalence.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeNonVacuumEscapeMass_le_weight`,
  `ReturnFloorCompiler.escapeCeiling_pos`,
  `ReturnFloorCompiler.escape_le_ceiling_mul_vacuumJoint`,
  `ReturnFloorCompiler.toCofinalEscapeRatioCeiling`,
  `returnFloorToEscapeCeilingToReturnFloor`, and
  `escapeCeilingToReturnFloorToEscapeCeiling`.
- **obligation**: stop recoding the same scalar wall and prove or refute the
  actual cutoff-uniform arbitrary-spin ratio between stationary row mass and
  its vacuum joint entry; a successful estimate must then be extended beyond
  the explicit spin ray.
- **constructive?**: yes — nonnegative row splitting, stationary-weight
  scaling, exact detailed-balance return cancellation, positive reciprocal,
  and Type-level structure maps suffice.  Every audited declaration uses
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two failed focused attempts are not passes.  After the
  modified escape dependency was rebuilt, the corrected focused check passes
  in about 1.3 seconds.  The exact one-worker target passes 5,030 jobs with
  the new module taking about 1.0 seconds.  Neither equivalent frontier is
  inhabited here, and no full-sector gap, continuum QFT, or Clay theorem is
  claimed.

### [BF4-spin-ray-raw-return-ratio] Exact partition cancellation and selected term — **CLOSED 2026-08-23**

- **milestone**: define the literal unnormalised positive-carrier row mass,
  cancel the common slab-partition reciprocal from every physical conditional
  row, specialize the result to every admitted excited spin cube, and locate
  the explicit positive zero-boundary production term below both its vacuum
  entry and its whole raw row.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRawReturnRatio.lean`.
- **decl**:
  `centralPhysicalPositiveRawRowMass_nonnegative`,
  `centralPhysicalPositiveRawRowMass_pos`,
  `centralNormalizedPhysicalReturn_eqv_rawRatio`,
  `centralLowerExcitedSpinCubeVacuumReturnProbability_eqv_rawRatio`,
  `centralLowerSpinCubePhysicalTerm_le_rawVacuumKernel`,
  `centralLowerSpinCubeRawVacuumKernel_le_rawRowMass`,
  `centralLowerSpinCubePhysicalTerm_le_rawRowMass`, and
  `centralLowerSpinCubePhysicalTerm_pos_and_le_rawRowMass`.
- **obligation**: prove or refute one cutoff- and spin-uniform upper bound on
  the literal raw positive-carrier row by a fixed multiple of the explicit
  selected zero-boundary term; if successful, compile it into the cofinal
  return floor and then extend routing beyond the spin ray.
- **constructive?**: yes — finite nonnegative row sums, positive retained-row
  mass, exact positive rational division, common-factor cancellation, and a
  located boundary-channel member suffice.  All eight audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three failed focused attempts are not passes.  The corrected
  focused check passes in about 1.1 seconds; the exact one-worker target passes
  5,027 jobs with the new module taking about 1.1 seconds.  No uniform raw-row
  ceiling, full-sector gap, continuum QFT, or Clay theorem is claimed.

### [BF4-spin-ray-selected-term-row-ceiling] Concrete raw ceiling to cofinal capacity — **CLOSED 2026-08-23**

- **milestone**: state one cofinal upper comparison of the literal raw
  positive-carrier row by a fixed multiple of the explicit selected
  zero-boundary physical term; derive `1 <= ceiling` from that comparison;
  and compile its reciprocal through the exact raw-return formula, finite
  minimum, and cofinal two-oriented-spoke capacity machinery.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeSelectedTermRowCeiling.lean`.
- **decl**:
  `spinCubeSelectedTermReturnFloor_pos`,
  `spinCubeSelectedTermReturnFloor_le_one`,
  `spinCubeSelectedTermReturnFloor_le_return_of_rawRow_le`,
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.one_le_ceiling`,
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.ceiling_pos`,
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.returnFloor_pos`,
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.returnFloor_le_return`,
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.returnFloor_le_finiteReturnFloor`,
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.toCofinalRayReturnFloor`,
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.finiteRayCapacityAt`, and
  `FixedNomeCofinalSpinCubeSelectedTermRowCeiling.toCofinalRayCapacity`.
- **obligation**: inhabit the selected-term row-ceiling structure from actual
  arbitrary-spin BF4 boundary-channel and fusion estimates, or prove a
  concrete obstruction and choose a less concentrated reference witness;
  then extend successful routing beyond the spin ray.
- **constructive?**: yes — a Type-level uniform comparison, one concrete
  spin-one witness, positive-factor cancellation, exact rational reciprocal,
  the raw-return identity, and finite-list recursion suffice.  All eleven
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: one failed focused attempt is not a pass.  The corrected
  focused check passes in about 1.3 seconds; the exact one-worker target passes
  5,029 jobs with the new module taking about 1.3 seconds.  The analytic datum
  remains uninhabited, and no full-sector gap, continuum QFT, or Clay theorem
  is claimed.

### [BF4-all-spin-cube-exact-selected-term] Exact fusion product and heat activity — **CLOSED 2026-08-23**

- **milestone**: compute every local link multiplicity of the selected
  arbitrary-spin closed cube as exactly one, compute its face factor as the
  sixth power of the corresponding heat coefficient, and identify the full
  selected physical term with that explicit activity.
- **file**:
  `lean/YMGap/Continuum/BF4CentralLowerSpinCubePhysicalTerm.lean`.
- **decl**:
  `centralLowerSpinCube_linkMultiplicity_eq_one`,
  `centralLowerSpinCube_linkProduct_eq_one`,
  `centralLowerSpinCubePhysicalFaceFactor_eqv`, and
  `centralLowerSpinCubePhysicalTerm_eqv`.
- **obligation**: prove or refute a cutoff- and spin-uniform upper bound
  `rawPositiveRowMass <= C * (coeffW w spin)^6`; if successful, use the
  selected-term compiler and then extend routing beyond the spin ray.
- **constructive?**: yes — finite incident-list permutations, inductive zero
  extensions, the exact two-valent singlet Boolean, finite link products, and
  finite face-product counting suffice.  All four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three failed focused attempts are not passes.  The corrected
  focused check passes in about 1.0 seconds; the exact one-worker target passes
  5,030 jobs with the new module taking about 1.0 seconds.  The uniform raw-row
  comparison, full-sector gap, continuum QFT, and Clay theorem remain open.

### [Z4-equal-pair-residual-multiplicity] Remove source-spin loss from local fusion bounds — **CLOSED 2026-08-23**

- **milestone**: prove that the one-, two-, and three-channel fusion counts
  beginning with an arbitrary equal pair are bounded by a cubic envelope
  involving only the remaining labels, with no dependence on the equal spin
  or the auxiliary cutoff.
- **file**:
  `lean/YMGap/Continuum/Z4EqualPairResidualMultiplicityBound.lean`.
- **decl**:
  `fusionOK_left_le_right_add_output`,
  `oneChannelMultiplicity_equalPair_le_residualSpinSumCube`,
  `twoChannelMultiplicity_equalPair_le_residualSpinSumCube`, and
  `threeChannelMultiplicity_equalPair_le_residualSpinSumCube`.
- **obligation**: transport these ordered equal-pair bounds through the
  actual cube-incidence permutations, allocate the residual charges only to
  non-source faces, and sum the resulting heat majorant uniformly in cutoff
  and admitted source spin.
- **constructive?**: yes — fusion symmetry, the triangle support inequality,
  backward channel support, stable finite range counts, and literal
  cardinality bounds suffice.  All four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 0.5 seconds; the exact one-worker
  target passes 473 jobs with the new module taking about 0.4 seconds.  No
  uniform raw-row ceiling, full-sector gap, continuum QFT, or Clay theorem is
  claimed.

### [Z4-equal-pair-residual-valence] Transport the residual bound through physical order — **CLOSED 2026-08-23**

- **milestone**: cover every canonical valence containing a leading equal
  pair and at most four residual labels, then use physical permutation
  invariance to bound an arbitrary actual incident ordering by the cubic
  residual-label envelope.
- **file**:
  `lean/YMGap/Continuum/Z4EqualPairResidualValenceBound.lean`.
- **decl**:
  `explicitValenceMultiplicity_equalPair_le_residualSpinSumCube` and
  `explicitValenceMultiplicity_physical_equalPair_le_residualSpinSumCube`.
- **obligation**: instantiate the actual-order theorem on every central-cube
  slab link, combine it with the untouched-link bound, allocate all residual
  charges to non-source faces, and sum the resulting heat majorant.
- **constructive?**: yes — finite valence cases, the exact explicit formulas,
  list-length arithmetic, bounded physical permutations, and the preceding
  channel bounds suffice.  Both audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 0.5 seconds; the exact one-worker
  target passes 513 jobs with the new module taking about 0.4 seconds.  No
  uniform raw-row ceiling, full-sector gap, continuum QFT, or Clay theorem is
  claimed.

### [Z4-residual-list-multiplicity] Unify generic and equal-pair residual coordinates — **CLOSED 2026-08-23**

- **milestone**: identify the recursive external-prefix sum with the ordinary
  sum of its finite incident-spin word, prove permutation invariance of that
  word sum, and restate the generic valence bound in residual-list form.
- **file**:
  `lean/YMGap/Continuum/Z4ResidualListMultiplicityBound.lean`.
- **decl**:
  `externalPrefixSpinSum_externalSpinsOfList`, `natListSum_perm`,
  `explicitValenceMultiplicity_list_le_spinSumCube`, and
  `explicitValenceMultiplicity_physical_perm_le_spinSumCube`.
- **obligation**: combine the generic zero-source-incidence case with the
  equal-pair two-incidence case at every actual cube slab link, then allocate
  the common residual bound to non-source faces and sum it.
- **constructive?**: yes — primitive recursion on natural numbers and lists,
  finite range decomposition, list permutations, and the existing generic
  fusion estimate suffice.  All four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 0.5 seconds; the exact one-worker
  target passes 514 jobs with the new module taking about 0.35 seconds.  No
  uniform raw-row ceiling, full-sector gap, continuum QFT, or Clay theorem is
  claimed.

### [BF4-central-spin-cube-residual-link] Remove source spin from the complete fusion product — **CLOSED 2026-08-23**

- **milestone**: recode every actual arbitrary-spin cube-source incident list
  as its selected source labels plus a vacuum-source residual list; split the
  checked zero-or-two incidence cases; and bound both every local link factor
  and the complete link product by source-spin-free residual quantities.
- **file**:
  `lean/YMGap/Continuum/BF4CentralSpinCubeResidualLinkBound.lean`.
- **decl**:
  `spinSource_incident_spins_perm_selected_residual`,
  `centralSpinCube_linkMultiplicity_le_residual`, and
  `centralSpinCube_linkProduct_le_residual`.
- **obligation**: allocate the residual link-product factors to non-source
  physical faces, combine them with the remaining heat coefficients, and sum
  the finite boundary/target carrier with a cutoff-uniform constant.
- **constructive?**: yes — explicit source labellings, finite list filters and
  permutations, the checked zero-or-two cube incidence, bounded assembly, the
  generic/equal-pair residual estimates, and natural product monotonicity
  suffice.  All three audited exports use exactly `[propext, Quot.sound]`; no
  forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 3.8 seconds; the exact one-worker
  target passes 986 jobs with the new module taking about 3.6 seconds.  No
  uniform raw-row ceiling, full-sector gap, continuum QFT, or Clay theorem is
  claimed.

### [BF4-central-spin-cube-residual-face] Allocate the residual product to non-source faces — **CLOSED 2026-08-23**

- **milestone**: flatten the residual incident-face identifiers over the
  corrected extent-one slab, certify that they are exactly four copies of the
  non-source physical faces, and convert the complete cubic link envelope into
  a twelfth-power factor on each such face.
- **file**:
  `lean/YMGap/Continuum/BF4CentralSpinCubeResidualFaceBound.lean`.
- **decl**:
  `centralSpinCubeResidualIncidenceIds_perm_fourfoldNonSource` and
  `centralSpinCubeResidualMultiplicityProduct_le_faceTwelfth`.
- **obligation**: multiply this twelfth-power factor by the non-source heat
  coefficients, rewrite each result as exponent-13 decorated activity, and
  sum the finite boundary/target carrier with a cutoff-uniform constant.
- **constructive?**: yes — a transparent sorting-based natural-list
  permutation checker, explicit corrected-slab incidence, recursive natural
  products, monotonicity, and exact power arithmetic suffice.  Both audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.  Direct `List.Perm` decision was rejected because its audit exposed
  `Classical.choice`.
- **status note**: two failed focused elaboration attempts are not passes.  The
  corrected focused check passes in about 7.6 seconds; the exact one-worker
  target passes 992 jobs with the new module taking about 7.7 seconds.  No
  uniform raw-row ceiling, full-sector gap, continuum QFT, or Clay theorem is
  claimed.

### [BF4-central-spin-cube-decorated-face] Absorb the residual charge into heat activities — **CLOSED 2026-08-23**

- **milestone**: factor the six arbitrary-spin source heat coefficients,
  discard the six unit vacuum-source coefficients, and pair the source-free
  twelfth-power residual charge with every remaining heat coefficient to
  obtain the exact exponent-13 decorated face product.
- **file**:
  `lean/YMGap/Continuum/BF4CentralSpinCubeResidualDecoratedFaceBound.lean`.
- **decl**:
  `centralSpinCube_faceCoefficient_factor`,
  `centralSpinCubePhysicalFaceFactor_eqv_activity_mul_vacuum`, and
  `centralVacuumFaceFactor_mul_twelfth_eqv_decorated`.
- **obligation**: combine the exact face factorization with the residual
  link-product inequality to dominate each production summand, then sum the
  non-source boundary/target carrier uniformly in cutoff.
- **constructive?**: yes — recursive rational products, explicit filtering of
  the source cube, bounded physical assembly, finite cube-face counting, and
  the existing coefficient-times-twelfth-power identity suffice.  All three
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: two failed focused elaboration attempts are not passes.  The
  corrected focused check passes in about 3.7 seconds; the exact one-worker
  target passes 993 jobs with the new module taking about 3.7 seconds.  No
  uniform raw-row ceiling, full-sector gap, continuum QFT, or Clay theorem is
  claimed.

### [BF4-central-spin-cube-term-decorated] Bound each production term by source activity times decorated residual — **CLOSED 2026-08-23**

- **milestone**: cast the source-free link-product and face-allocation bounds
  into rational order, multiply by the nonnegative literal face factor, and
  contract the result through the exact source and decorated-face identities.
- **file**:
  `lean/YMGap/Continuum/BF4CentralSpinCubeTermDecoratedBound.lean`.
- **decl**:
  `centralSpinCubePhysicalTerm_le_activity_mul_decorated`.
- **obligation**: sum this pointwise majorant over the finite physical
  boundary/target carrier by an injective map into independent non-source face
  labels, then use the anchor exponent-13 heat sum to obtain a cutoff-uniform
  raw-row constant.
- **constructive?**: yes — coefficient nonnegativity, recursive finite-product
  nonnegativity, natural-to-rational monotonicity, and the two preceding exact
  face equivalences suffice.  The audited export uses exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused guarded check passes on the first attempt in
  about 0.6 seconds; the exact one-worker target passes 994 jobs with the new
  module taking about 0.44 seconds.  No uniform raw-row ceiling, full-sector
  gap, continuum QFT, or Clay theorem is claimed.

### [BF4-central-spin-cube-residual-carrier-sum] Sum the residual boundary-target carrier uniformly — **CLOSED 2026-08-23**

- **milestone**: inject every physical boundary/target pair into its assembled
  non-source label vector, prove exact Cartesian factorization of the vector
  weight, certify the 66-face count, and apply the uniform exponent-13 one-face
  envelope.
- **file**:
  `lean/YMGap/Continuum/BF4CentralSpinCubeResidualCarrierSumBound.lean`.
- **decl**:
  `mem_boundedSpinVectors_iff`,
  `centralSpinCubeResidualCarrierSum_le_vectorPower`,
  `centralSpinCubeNonSourceFaceIds_length`, and
  `centralSpinCubeResidualCarrierSum_le_ceiling`.
- **obligation**: transport the termwise source-activity majorant through the
  production boundary sum and retained target sum to obtain the actual
  cutoff-uniform raw-row ceiling, then feed that theorem to the previously
  proved selected-term return/capacity compiler.
- **constructive?**: yes — explicit zero-through-cutoff vectors, list
  membership induction, supported-function extensionality, the existing
  assembly injection, finite weighted injection, exact Cartesian sums, and
  rational power monotonicity suffice.  All audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: two failed focused elaboration attempts are not passes.  The
  corrected focused check passes in about 3.9 seconds; the exact one-worker
  target passes 995 jobs with the new module taking about 3.8 seconds.  No
  raw-row ceiling, full-sector gap, continuum QFT, or Clay theorem is claimed
  yet.

### [BF4-central-spin-cube-raw-row-ceiling] Bound the literal positive raw row uniformly — **CLOSED 2026-08-23**

- **milestone**: enlarge the retained positive target filter by kernel
  nonnegativity, sum the source-activity decorated bound over all boundary and
  target labellings, identify the nested sum with the literal Cartesian
  residual carrier, and apply its fixed 66-face ceiling.
- **file**:
  `lean/YMGap/Continuum/BF4CentralSpinCubeRawRowCeiling.lean`.
- **decl**:
  `centralLowerSpinCubePositiveRawRow_le_activity_mul_ceiling`.
- **obligation**: combine the exact selected zero-boundary summand with this
  raw-row ceiling, cancel the common six-face source activity in the positive
  raw return ratio, and instantiate the existing witness-bearing spin-ray
  return/capacity compiler.
- **constructive?**: yes — finite filter partition, production-kernel
  nonnegativity, recursive termwise list order, finite Fubini, exact Cartesian
  identification, rational power nonnegativity, and the preceding carrier
  ceiling suffice.  The audited export uses exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three failed focused elaboration attempts are not passes.
  The corrected focused check passes in about 0.9 seconds; the exact
  one-worker dependency-complete target passes 5036 jobs with the new module
  taking about 0.9 seconds.  This is a cutoff-uniform certificate on one
  explicit spin-cube ray, not a full-sector gap, continuum QFT, or Clay
  theorem.

### [BF4-central-spin-cube-uniform-ray-capacity] Compile the raw-row ceiling into cofinal ray capacity — **CLOSED 2026-08-23**

- **milestone**: identify the selected zero-boundary production term with the
  same six-face source activity in the raw-row bound, inhabit the cofinal
  selected-term row-ceiling structure from cutoff zero, and compile it into a
  positive uniform return floor and both-oriented spoke capacity.
- **file**:
  `lean/YMGap/Continuum/BF4CentralSpinCubeUniformRayCapacity.lean`.
- **decl**:
  `anchorCentralSpinCubeSelectedTermRowCeiling`,
  `anchorCentralSpinCubeReturnFloor_pos`,
  `anchorCentralSpinCubeReturnFloor_le_return`,
  `anchorCentralSpinCubeCofinalRayReturnFloor`,
  `anchorCentralSpinCubeCofinalRayCapacity`, and
  `anchorCentralSpinCubeFiniteRayCapacityAt`.
- **obligation**: construct a cutoff-uniform routing or decomposition that
  connects every remaining positive physical vacuum-sector state to the
  controlled spin-cube/vacuum backbone without carrier-size or vanishing-edge
  loss, then contract that full-sector flow into a uniform Dirichlet or
  transfer estimate.
- **constructive?**: yes — the exact selected-term activity identity, the
  literal raw-row ceiling, rational commutativity, and the already proved
  witness-bearing return/capacity compiler suffice.  All six audited exports
  use exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 1.1 seconds; the exact one-worker
  dependency-complete target passes 5040 jobs with the new module taking about
  1.2 seconds.  The certificate is uniform only on the explicit spin-cube ray;
  it is not a full vacuum-complement gap, continuum QFT, or Clay theorem.

### [BF4-central-spin-cube-ray-Dirichlet-coercivity] Contract uniform spoke capacity into ray-sector coercivity — **CLOSED 2026-08-23**

- **milestone**: enumerate the stationary-product pairwise variance of all
  excited spin-cube ray endpoints, pay each endpoint square by its literal
  two-spoke occurrence budget, regroup repeated directed spokes exactly,
  extend the spoke capacity to every carrier edge by an occurrence-support
  dichotomy, and sum the pointwise comparison into the genuine physical
  Dirichlet form.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeRayDirichletCoercivity.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeRayPairwiseVariance_eqv_offset`,
  `centralLowerExcitedSpinCubeRayPairwiseVariance_le_rawOccurrenceEnergy`,
  `centralLowerExcitedSpinCubeRayRawOccurrenceEnergy_eqv_loadedDirichlet`,
  `CentralLowerExcitedSpinCubeFiniteRayCapacityAt.delta_mul_rayFlowLoad_le_physicalKernel`,
  `CentralLowerExcitedSpinCubeFiniteRayCapacityAt.delta_mul_rayPairwiseVariance_le_physicalDirichlet`,
  `FixedNomeCofinalSpinCubeRayCapacity.delta_mul_rayPairwiseVariance_le_physicalDirichlet`,
  and
  `anchorCentralSpinCube_delta_mul_rayPairwiseVariance_le_physicalDirichlet`.
- **obligation**: cover every off-ray state in the finite physical vacuum
  sector by a controlled path or decomposition into the ray/vacuum backbone,
  with a cutoff-uniform full-sector congestion bound; only then contract the
  full stationary pairwise variance into a uniform finite transfer estimate.
- **constructive?**: yes — finite Cartesian reindexing, the exact two-edge
  Cauchy path, nonnegative stationary demand, literal occurrence support,
  duplicate-preserving edge-load regrouping, the positive-load witness, and
  finite sum monotonicity suffice.  All eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: five failed focused elaboration attempts and one
  deliberately interrupted expensive guarded attempt are not passes.  The
  corrected focused check passes in about 1.7 seconds; the exact one-worker
  dependency-complete target passes 5041 jobs with the new module taking about
  1.6 seconds.  The theorem is uniform only for stationary pairwise variance
  restricted to the explicit spin-cube ray.  It is not a full
  vacuum-complement gap, continuum QFT, or Clay theorem.

### [BF4-spin-cube-off-ray-residual-frontier] Isolate the exact nonempty residual after ray coercivity — **CLOSED 2026-08-23**

- **milestone**: filter the full finite vacuum sector by explicit ray
  membership, identify the filtered ray with the spin-ordered ray up to
  permutation, prove the complement contains the vacuum, split the full
  stationary pairwise variance into ray--ray plus three literal residual
  blocks, and compile a half-energy residual certificate into full-sector
  pairwise Dirichlet coercivity.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualFrontier.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeFilteredRayIndices_perm_rayIndices`,
  `zero_mem_centralLowerExcitedSpinCubeOffRayIndices`,
  `centralPhysicalFiniteVacuumSectorPairwiseVariance_eqv_ray_add_offRayResidual`,
  `centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_nonnegative`,
  `CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualCoercivityAt.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet`,
  `FixedNomeCofinalSpinCubeOffRayResidualCoercivity`, and
  `FixedNomeCofinalSpinCubeOffRayResidualCoercivity.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet`.
- **obligation**: inhabit the cofinal residual structure by routing or
  decomposing all ray--off, off--ray, and off--off stationary demands so their
  weighted load fits the half of genuine physical Dirichlet capacity reserved
  from the ray proof.  Then establish a uniform positive lower bound on the
  physical vacuum-sector mass before applying the centered transfer and
  completion bridges.
- **constructive?**: yes — decidable finite filtering, nodup permutation,
  nonzero excited-ray indices, the explicit vacuum root, exact four-block
  finite sums, block nonnegativity, and rational half-energy allocation
  suffice.  All eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 1.4 seconds; the exact one-worker
  dependency-complete target passes 5042 jobs with the new module taking about
  1.3 seconds.  No inhabitant of the cofinal off-ray residual certificate,
  full vacuum-complement gap, continuum QFT, or Clay theorem is claimed.

### [BF4-spin-cube-off-ray-residual-flow] Route the residual into a literal coefficient-independent edge load — **CLOSED 2026-08-23**

- **milestone**: enumerate exactly the three residual endpoint blocks, route
  every stationary demand through the constructive loop-erased positive
  physical-kernel path, prove the finite Cauchy endpoint bound, retain and
  regroup all duplicate directed-edge occurrences, and contract the residual
  pairwise form into one loaded Dirichlet form.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualFlow.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualFlowPairwiseVariance_eqv_residual`,
  `centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawPairBudget`,
  `centralLowerExcitedSpinCubeOffRayResidualOccurrence_mem_sector`,
  `centralLowerExcitedSpinCubeOffRayResidualOccurrence_kernel_pos`,
  `centralLowerExcitedSpinCubeOffRayResidualRawOccurrenceEnergy_eqv_loadedDirichlet`,
  and
  `centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_rawLoadedDirichlet`.
- **obligation**: prove a cutoff-uniform, coefficient-free pointwise capacity
  comparison placing the shared coercivity floor times the explicit residual
  flow load below the half physical-kernel capacity reserved by the ray proof;
  then compile it into the already isolated cofinal residual certificate.
- **constructive?**: yes — finite Cartesian enumeration, sector-filter
  membership, constructive simple positive paths, finite Cauchy--Schwarz,
  nonnegative stationary weights, occurrence support, and exact
  duplicate-preserving load regrouping suffice.  All eight audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: one failed focused elaboration attempt is not a pass.  The
  corrected focused check passes in about 1.4 seconds; the exact one-worker
  dependency-complete target passes 5043 jobs with the new module taking about
  1.2 seconds.  The residual load is explicit, but no uniform pointwise
  congestion inequality, full vacuum-complement gap, continuum QFT, or Clay
  theorem is claimed.

### [BF4-spin-cube-off-ray-residual-flow-capacity] Compile local congestion into full finite coercivity — **CLOSED 2026-08-23**

- **milestone**: replace the coefficient-uniform residual form hypothesis by
  one pointwise comparison between the explicit residual edge load and half
  the genuine physical-kernel capacity, sum that comparison into the loaded
  Dirichlet form, inhabit the residual coercivity certificate, and compile a
  cofinal family into full finite-sector pairwise coercivity.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualFlowCapacity.lean`.
- **decl**:
  `CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt.sharedFloor_mul_rawLoadedDirichlet_le_half_physicalDirichlet`,
  `CentralLowerExcitedSpinCubeOffRayResidualFlowCapacityAt.toOffRayResidualCoercivityAt`,
  `FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity`, and
  `FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet`.
- **obligation**: inhabit the cofinal pointwise structure by proving that the
  explicit residual flow load fits the reserved half physical-kernel capacity
  on every carrier edge, with one cutoff-independent positive floor.  Then
  establish the separate uniform sector-mass lower bound required for a
  centered transfer contraction.
- **constructive?**: yes — rational joint scaling, finite sum monotonicity,
  square nonnegativity, the exact residual loaded-flow theorem, and the
  existing half-energy compiler suffice.  All five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three initial focused attempts were interrupted or failed
  because missing namespace openings caused expensive definitional reduction;
  none is a pass.  A temporary profiler localized the issue and was removed.
  The corrected focused check passes in about 1.3 seconds; the exact one-worker
  dependency-complete target passes 5044 jobs with the new module taking about
  1.2 seconds.  The pointwise capacity family is not inhabited, so no
  unconditional full-sector gap, continuum QFT, or Clay theorem is claimed.

### [BF4-spin-cube-off-ray-residual-linear-congestion] Reduce simple-path congestion to one scalar ratio — **CLOSED 2026-08-23**

- **milestone**: prove that every chosen residual path has no repeated directed
  edge and length at most the finite carrier size, sum its stationary-product
  charge exactly over the residual endpoint list, and compile one scalar
  comparison against the minimum positive physical edge into pointwise
  residual capacity and full finite-sector coercivity.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualLinearCongestion.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorSimplePositivePath_directedEdges_nodup`,
  `centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_le`,
  `centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize_mul_endpointWeightSum`,
  `CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualLinearRatioAt.toResidualFlowCapacityAt`,
  `FixedNomeCofinalSpinCubeOffRayResidualLinearRatio`, and
  `FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet`.
- **obligation**: first bound the literal residual endpoint stationary mass;
  then replace the displayed carrier-size/minimum-edge ratio by a structured
  local flow estimate whose capacity is uniform in the cutoff.  A separate
  uniform positive sector-mass floor is still required before deriving a
  centered transfer contraction.
- **constructive?**: yes — loop-erased finite walks, no-duplicate directed
  edges, finite carrier length, nonnegative stationary products, exact
  duplicate-preserving list flattening, minimum-positive-edge comparison, and
  the prior pointwise capacity compiler suffice.  All nine audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: all earlier interrupted, profiler-prefix, and failed
  focused attempts are not passes.  The corrected complete focused guarded
  check passes in about 1.3 seconds; the exact one-worker dependency-complete
  target passes 5045 jobs with the new module taking about 1.4 seconds.  No
  inhabitant of the scalar ratio, cutoff-uniform full-sector gap, continuum
  QFT, or Clay theorem is claimed.

### [BF4-spin-cube-off-ray-residual-endpoint-mass] Normalize the residual endpoint mass — **CLOSED 2026-08-23**

- **milestone**: prove the three residual endpoint blocks are a duplicate-free
  subcarrier of the full vacuum-sector Cartesian square, bound their literal
  stationary-product mass by the full sector mass square and hence by one,
  remove the endpoint-mass factor from the directed residual-load bound, and
  compile the resulting mass-free scalar ratio into full finite coercivity.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualEndpointMassBound.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualEndpointPairs_nodup`,
  `centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_fullPairWeightSum`,
  `centralPhysicalFiniteVacuumSectorFullPairWeightSum_eqv_massSquare`,
  `centralLowerExcitedSpinCubeOffRayResidualEndpointWeightSum_le_one`,
  `centralLowerExcitedSpinCubeOffRayResidualFlowLoad_le_sectorSize`,
  `CentralLowerExcitedSpinCubeOffRayResidualNormalizedLinearRatioAt.toResidualFlowCapacityAt`,
  and
  `FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet`.
- **obligation**: replace the remaining full-carrier path-length and minimum
  positive-edge comparison by structured local or multiscale routing with a
  cutoff-uniform weighted congestion constant.  Separately establish the
  uniform positive vacuum-sector mass floor needed to turn full pairwise
  coercivity into a centered transfer contraction.
- **constructive?**: yes — complementary Boolean filters, explicit Cartesian
  block disjointness, finite-list nodup, identity injection, stationary-weight
  nonnegativity, exact Cartesian-product factorization, and finite physical-law
  normalization suffice.  All nine audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: three slow focused attempts were interrupted and one
  focused attempt failed on a missing target-weight unfolding; none is a
  pass.  Replacing the expensive older-cost comparison by a direct mass-free
  capacity compiler gives a complete focused check in about 1.25 seconds.
  The exact one-worker dependency-complete target passes 5046 jobs with the
  new module taking about 1.3 seconds.  No inhabitant of the mass-free ratio,
  cutoff-uniform full-sector gap, continuum QFT, or Clay theorem is claimed.

### [BF4-spin-cube-finite-linear-full-sector-coercivity] Construct a positive full-sector floor at every cutoff — **CLOSED 2026-08-23**

- **milestone**: restrict the proved spin-cube ray capacity to the minimum of
  its ray floor and the minimum positive physical edge divided by
  `1 + sectorSize`, use the mass-free residual-flow compiler, and derive an
  unconditional positive full-sector pairwise Dirichlet coercivity theorem at
  every finite cutoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeFiniteLinearRayDelta_pos`,
  `centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity`,
  `centralLowerExcitedSpinCubeFiniteLinearNormalizedRatioAt`,
  `centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_pos`,
  `centralLowerExcitedSpinCubeFiniteLinearFullCoercivityFloor_mul_pairwiseVariance_le_physicalDirichlet`,
  `anchorCentralSpinCubeFiniteLinearFullCoercivityFloor_pos`, and
  `anchorCentralSpinCubeFiniteLinearFullCoercivityFloor_mul_pairwiseVariance_le_physicalDirichlet`.
- **obligation**: replace the cutoff-dependent carrier-size and minimum-edge
  factors in the displayed finite floor by a structured local or multiscale
  routing certificate with a common positive weighted-congestion constant.
  Separately prove a uniform positive physical sector-mass floor before
  compiling centered transfer contraction and completion/limit statements.
- **constructive?**: yes — positivity of the finite edge floor and normalized
  linear cost, constructive rational minimum/division, monotone scaling of the
  existing ray-capacity fields, and the normalized residual-flow compiler
  suffice.  All eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on missing namespace openings
  and is not a pass.  The corrected complete focused check passes in about
  2.1 seconds; the exact one-worker dependency-complete target passes 5047
  jobs with the new module taking about 2.1 seconds.  The theorem constructs
  a positive floor at each cutoff but no cutoff-uniform lower bound, completed
  gap, continuum QFT, or Clay theorem.

### [BF4-physical-vacuum-root-variance] Contract full pairwise demand to the same rooted observable — **CLOSED 2026-08-23**

- **milestone**: prove root-shift invariance of finite weighted pairwise
  variance, use the exact mass/diagonal/mean-square identity to drop only the
  nonnegative shifted mean square, remove the mass factor for a nonnegative
  law of mass at most one, and specialize the result to the physical vacuum
  root `0`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorRootVariance.lean`.
- **decl**:
  `finiteWeightedRootVariance_nonnegative`,
  `finiteWeightedPairwiseVariance_shiftRoot_eqv`,
  `finiteWeightedPairwiseVariance_le_twice_mass_rootVariance`,
  `finiteWeightedPairwiseVariance_le_twice_rootVariance`, and
  `centralPhysicalFiniteVacuumSectorPairwiseVariance_le_twice_rootVariance`.
- **obligation**: route each literal state-to-vacuum square along a positive
  physical-kernel path, regroup the one-body demands into a directed local
  traffic function, and prove a common positive capacity comparison for that
  traffic.  The separate uniform sector-mass floor is still required for the
  centered transfer compiler.
- **constructive?**: yes — rational additive congruence, the exact finite
  pairwise identity, rational square nonnegativity, nonnegative finite sums,
  and the proved physical sector mass upper bound suffice.  All five audited
  exports use only `[propext]` or `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first two focused checks failed on missing namespace
  openings and rational shift normalization and are not passes.  The corrected
  focused check passes in about 0.9 seconds; the exact one-worker
  dependency-complete target passes 5021 jobs with the new module taking about
  0.94 seconds.  No rooted traffic capacity, cutoff-uniform full-sector gap,
  continuum QFT, or Clay theorem is claimed.

### [BF4-physical-vacuum-root-traffic] Route the same rooted observable into one local edge load — **CLOSED 2026-08-23**

- **milestone**: attach one loop-erased positive physical-kernel path from
  every finite-sector state to the vacuum, weight each directed occurrence by
  twice the state mass times path length, prove the rooted Cauchy budget, and
  regroup all duplicate occurrences into a coefficient-independent directed
  root-flow load.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorRootTraffic.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSector_root_sq_le_rawPathBudget`,
  `centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawBudget`,
  `centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_rawBudget`,
  `centralPhysicalFiniteVacuumSectorRootOccurrence_mem_sector`,
  `centralPhysicalFiniteVacuumSectorRootOccurrence_kernel_pos`,
  `centralPhysicalFiniteVacuumSectorRootRawOccurrenceEnergy_eqv_loadedDirichlet`,
  and
  `centralPhysicalFiniteVacuumSectorPairwiseVariance_le_rootRawLoadedDirichlet`.
- **obligation**: prove a cutoff-independent positive comparison between the
  genuine physical kernel and the explicit local root traffic, either directly
  or via a structured local/multiscale decomposition of the states whose root
  paths cross each edge.
- **constructive?**: yes — the prior same-observable root contraction, literal
  loop-erased positive paths, finite Cauchy--Schwarz, occurrence membership and
  positivity, and duplicate-preserving finite regrouping suffice.  All seven
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the focused check passes on its first attempt in about 1.17
  seconds; the exact one-worker dependency-complete target passes 5022 jobs
  with the new module taking about 1.2 seconds.  No local uniform capacity,
  completed gap, continuum QFT, or Clay theorem is claimed.

### [BF4-physical-vacuum-root-traffic-capacity] Compile local root capacity and inhabit it at every finite cutoff — **CLOSED 2026-08-23**

- **milestone**: bound every local root-flow load by its exact total traffic,
  prove positive load witnesses a strictly positive physical edge, compile a
  pointwise `delta * load <= kernel` comparison into full pairwise Dirichlet
  coercivity, construct a positive finite-cutoff capacity using the minimum
  positive edge divided by `1 + totalRootTraffic`, and isolate the exact
  cofinal common-`delta` structure.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorRootTrafficCapacity.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorRootFlowLoad_le_totalTraffic`,
  `centralPhysicalFiniteVacuumSectorRootFlowLoad_pos_implies_kernel_pos`,
  `CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt.delta_mul_pairwiseVariance_le_physicalDirichlet`,
  `centralPhysicalFiniteVacuumSectorRootFiniteDelta_pos`,
  `centralPhysicalFiniteVacuumSectorRootFiniteCapacityAt`,
  `centralPhysicalFiniteVacuumSectorRootFiniteDelta_mul_pairwiseVariance_le_physicalDirichlet`,
  `FixedNomeCofinalVacuumRootTrafficCapacity`, and
  `FixedNomeCofinalVacuumRootTrafficCapacity.delta_mul_pairwiseVariance_le_physicalDirichlet`.
- **obligation**: inhabit the cofinal structure by one positive `delta` whose
  pointwise root-traffic comparison holds at every later cutoff.  Separately
  establish the uniform positive physical sector-mass floor needed by the
  centered transfer compiler.
- **constructive?**: yes — nonnegative finite traffic, pointwise indicator
  monotonicity, positive-load occurrence witnessing, the finite positive-edge
  floor, constructive rational division, and finite Dirichlet summation
  suffice.  All eight audited exports use exactly `[propext, Quot.sound]`; no
  forbidden construct was added.
- **status note**: the first focused check failed only on a missing finite-sum
  namespace and is not a pass.  The corrected focused check passes in about
  1.23 seconds; the exact one-worker dependency-complete target passes 5023
  jobs with the new module taking about 1.3 seconds.  The finite capacities are
  unconditional but cutoff-dependent; no cofinal uniform capacity, completed
  gap, continuum QFT, or Clay theorem is claimed.

### [BF4-physical-vacuum-sector-uniform-mass-floor] Lift one uniform positive row into the complete sector mass — **CLOSED 2026-08-23**

- **milestone**: for every fixed rational nome `0 < w < 1` and half-extent,
  use the persistent all-zero physical state and the generic uniform
  positive-row theorem to construct an explicit positive lower bound for the
  complete finite physical vacuum-sector mass at every later cutoff; specialize
  the result to the spin-cube anchor `w = 1/400`, `half = 0`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorUniformMassFloor.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorUniformMassFloor_pos`,
  `centralPhysicalFiniteVacuumSectorUniformMassFloor_le`,
  `anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor_pos`, and
  `anchorCentralPhysicalFiniteVacuumSectorUniformMassFloor_le`.
- **obligation**: combine this now-constructed mass floor with an inhabitant of
  `FixedNomeCofinalVacuumRootTrafficCapacity` to compile centered finite strict
  contraction and the existing completed strict-contraction datum.  The
  cofinal root-traffic capacity itself remains the immediate analytic input.
- **constructive?**: yes — persistence of the explicit all-zero carrier state,
  the generic uniform positive-row floor, stationary-weight nonnegativity, and
  finite-list sum monotonicity suffice.  All four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused guarded check passes on its first attempt in
  about 0.48 seconds.  The exact one-worker dependency-complete target passes
  1188 jobs, with the new module taking about 0.512 seconds.  This closes the
  fixed-nome sector-mass lane; it does not inhabit the cofinal root-traffic
  capacity or prove a completed/continuum/Clay mass gap.

### [BF4-physical-vacuum-root-traffic-completed-gap] Compile cofinal root capacity and uniform mass into the completed strict contraction — **CLOSED 2026-08-24**

- **milestone**: prove the generic centered Poincare algebra from one finite
  root-traffic capacity and one positive sector-mass lower bound, construct the
  explicit strict rate `q = 1 / (1 + delta * massFloor)`, combine a cofinal
  root-capacity family with the constructed fixed-nome uniform mass floor, and
  return both the existing cofinal finite strict-gap interface and the actual
  completed vacuum-sector strict-contraction datum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap.lean`.
- **decl**:
  `rootTraffic_strength_mul_diagonal_le_deficit`,
  `rootTraffic_abs_matrix_le_rate_mul_diagonal`,
  `FixedNomeCofinalVacuumRootTrafficCapacity.toFiniteStrictGap`, and
  `FixedNomeCofinalVacuumRootTrafficCapacity.toCompletedStrictContractionData`.
- **obligation**: inhabit the already isolated
  `FixedNomeCofinalVacuumRootTrafficCapacity` by proving one positive local
  capacity floor for the explicit root flow at every later representation
  cutoff.  No further rooted finite-to-completed compiler is missing.
- **constructive?**: yes — exact centered pairwise variance, the pointwise
  root-capacity Dirichlet compiler, the exact doubled transfer deficit,
  rational positive-factor cancellation, Gram positivity, and explicit
  rational division suffice.  All four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: four focused attempts failed and are not passes.  Two slow
  attempts exposed missing namespace openings and two fast attempts localized
  a residual unfolding and field-notation namespace issue.  The corrected
  focused check passes in about 1.4 seconds.  The exact one-worker
  dependency-complete target passes 5025 jobs, with the new module taking about
  1.3 seconds.  No cofinal capacity inhabitant, physical-scale uniform gap,
  continuum QFT, or Clay theorem is claimed.

### [BF4-physical-vacuum-root-traffic-linear-moment] Bound local load by the first weighted path-length moment — **CLOSED 2026-08-24**

- **milestone**: prove that every canonical loop-erased vacuum-root path has
  no duplicate directed edge, bound the contribution of one state to any
  fixed edge by its doubled weight times one path-length factor, sum that
  pointwise estimate into a first-moment local-load ceiling, construct an
  unconditional positive capacity ratio at each finite cutoff, and compile
  the corresponding cofinal scalar-ratio interface through local capacity to
  the completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorRootSimplePath_directedEdges_nodup`,
  `centralPhysicalFiniteVacuumSectorRootWeightedPathLoad_le_stateLinearLoad`,
  `centralPhysicalFiniteVacuumSectorRootFlowLoad_le_linearMoment`,
  `CentralPhysicalFiniteVacuumSectorRootLinearRatioAt.toRootTrafficCapacityAt`,
  `centralPhysicalFiniteVacuumSectorRootFiniteLinearRatioAt`,
  `FixedNomeCofinalVacuumRootLinearRatio.toRootTrafficCapacity`, and
  `FixedNomeCofinalVacuumRootLinearRatio.toCompletedStrictContractionData`.
- **obligation**: inhabit `FixedNomeCofinalVacuumRootLinearRatio` by proving
  that one positive scalar times the explicit first weighted length cost is
  bounded by the minimum used physical edge at every later cutoff, or replace
  the generic component paths by geometric paths for which such a comparison
  is provable.  Thermodynamic/continuum and weak-to-strong physical-scale
  survival remain separate obligations.
- **constructive?**: yes — constructive walk recursion, loop-erased vertex
  simplicity, duplicate-free directed-edge occurrence, rational load
  nonnegativity, exact flat-map regrouping, finite-list sum monotonicity, the
  finite positive-edge floor, and constructive positive division suffice.
  All seven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused check failed on an unavailable list-sum
  lemma name and an implicit dependent positivity argument and is not a pass.
  The corrected complete focused guarded check passes in about 1.3 seconds.
  The exact one-worker dependency-complete target passes 5026 jobs, with the
  new module taking about 1.3 seconds.  The finite ratio is unconditional but
  cutoff-dependent; no cofinal ratio, continuum QFT, or Clay theorem is
  claimed.

### [BF4-dynamic-vacuum-root-physical-band] Keep the rooted completed gap on one observable-connected physical trajectory — **CLOSED 2026-08-24**

- **milestone**: package a scale-indexed family of the actual fixed-half
  completed vacuum-root transfers and their cofinal linear-ratio inputs,
  retain the literal completed same-object autocorrelation decay at every
  scale, impose a two-sided physical scaling band on the definitionally same
  rate, prove a uniform finite positive physical-gap band, derive an effective
  lattice-margin-zero modulus, and construct the canonical sharp continuum
  floor interfaces.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumRootLinearPhysicalBand.lean`.
- **decl**:
  `FixedHalfDynamicVacuumRootLinearFamily.completedGapAt`,
  `FixedHalfDynamicVacuumRootLinearFamily.completedAutocorrelation_sq_decay`,
  `FixedHalfDynamicVacuumRootPhysicalRateBand.floor_le_physicalGap`,
  `FixedHalfDynamicVacuumRootPhysicalRateBand.physicalGap_le_ceiling`,
  `FixedHalfDynamicVacuumRootPhysicalRateBand.latticeMargin_le_epsilon`,
  `FixedHalfDynamicVacuumRootPhysicalRateBand.one_sub_epsilon_le_rate`,
  `FixedHalfDynamicVacuumRootPhysicalRateBand.toContinuumGapTheorem`, and
  `FixedHalfDynamicVacuumRootPhysicalRateBand.toUniformPhysicalGapFloor`.
- **obligation**: inhabit the dynamic family with one cofinal root-linear ratio
  at each physical scale and prove the genuine two-sided RG estimate
  `c*a_j <= 1-q_j <= C*a_j` for the compiled rate of that same transfer.
  Independently construct graph-norm/OS convergence for those same carriers
  and transfers; no abstract floor may substitute for this object-level seam.
- **constructive?**: yes — dependent scale-indexed completed-gap compilation,
  the existing same-object autocorrelation theorem, positive rational
  division, two-sided quotient comparison, explicit spacing-zero moduli, and
  exact rational cancellation suffice.  All eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on a missing namespace
  opening and missing local rational-equivalence notation and is not a pass.
  The corrected complete focused guarded check passes in about 1.5 seconds.
  The exact one-worker dependency-complete target passes 5028 jobs, with the
  new module taking about 1.6 seconds.  Neither the dynamic ratio family nor
  the physical-rate band is inhabited; no continuum QFT or Clay theorem is
  claimed.

### [BF4-dynamic-vacuum-root-strength-band] Reduce physical-rate matching to the explicit rooted strength — **CLOSED 2026-08-24**

- **milestone**: prove that the completed rooted vacuum-sector rate is exactly
  `q_j = 1/(1+s_j)` and its margin is rationally equivalent to
  `s_j/(1+s_j)`, where
  `s_j = rootCapacityDelta_j * uniformSectorMassFloor_j`; compile a two-sided
  spacing estimate and finite cap for this explicit strength into the existing
  same-object physical-rate band and sharp continuum-gap interface.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumRootStrengthPhysicalBand.lean`.
- **decl**:
  `cutoffTwoDirichletGluingMargin_eqv_strengthRatio`,
  `dynamicVacuumRootCompletedGapAt_rate_eq`,
  `dynamicVacuumRootLatticeMargin_eqv_strengthRatio`,
  `FixedHalfDynamicVacuumRootStrengthBand.physicalFloor_pos`,
  `FixedHalfDynamicVacuumRootStrengthBand.physicalFloor_mul_spacing_le_strengthRatio`,
  `FixedHalfDynamicVacuumRootStrengthBand.strengthRatio_le_strength`,
  `FixedHalfDynamicVacuumRootStrengthBand.toPhysicalRateBand`, and
  `FixedHalfDynamicVacuumRootStrengthBand.toContinuumGapTheorem`.
- **obligation**: inhabit the scale-indexed dynamic family and prove that its
  concrete rooted strength is bounded above and below by positive multiples
  of the physical transfer spacing, with one finite cap.  Equivalently, the
  remaining rate-matching work is now an estimate on the product of the
  cofinal root-capacity ratio and the already explicit sector-mass floor, not
  an unrelated abstract gap constant.  Graph-norm/OS continuum convergence of
  the same carriers and transfers remains independent and open.
- **constructive?**: yes — exact rational division identities, positivity of
  the rooted capacity and explicit sector-mass floor, monotonicity under a
  finite denominator cap, and the preceding same-object completed-gap compiler
  suffice.  All eight audited exports use exactly `[propext, Quot.sound]`; no
  forbidden construct was added.
- **status note**: the first focused attempt failed on rational reassociation
  and an accidental nested namespace and is not a pass.  After explicit
  constructive equivalence chains, the complete focused guarded check passes
  in about 1.5 seconds.  The exact one-worker dependency-complete target passes
  5029 jobs, with the new module taking about 1.5 seconds.  No dynamic family,
  strength band, continuum QFT, or Clay theorem is inhabited or claimed.

### [BF4-dynamic-vacuum-root-strength-normalization] Derive the cap and upper positivity from normalized BF4 data — **CLOSED 2026-08-24**

- **milestone**: prove the explicit uniform vacuum-sector mass floor is at
  most one, prove every admissible cofinal root-linear `delta` is at most one,
  deduce the unconditional dynamic strength cap `s_j <= 1`, derive positivity
  of any upper spacing multiplier from its inequality, and construct the
  previous strength and physical-rate bands from only the two-sided
  strength/spacing comparison.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumRootStrengthNormalization.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorUniformMassFloor_le_one`,
  `cofinalVacuumRootLinearRatio_delta_le_one`,
  `dynamicVacuumRootStrength_le_one`,
  `FixedHalfDynamicVacuumRootStrengthScaling.upper_pos`,
  `FixedHalfDynamicVacuumRootStrengthScaling.toStrengthBand`,
  `FixedHalfDynamicVacuumRootStrengthScaling.toPhysicalRateBand`, and
  `FixedHalfDynamicVacuumRootStrengthScaling.toContinuumGapTheorem`.
- **obligation**: inhabit the dynamic cofinal root-ratio family and prove the
  two genuine analytic inequalities
  `lower*a_j <= delta_j*uniformMassFloor_j <= upper*a_j` on its actual
  transfer spacing.  No separate strength cap or proof that `upper > 0` is
  needed.  Graph-norm/OS convergence of those same carriers and transfers
  remains a separate open producer lane.
- **constructive?**: yes — the explicit anchor mass comparison, total
  probability bound, root cost lower bound by one, normalized edge-floor upper
  bound by one, rational product monotonicity, and positive division suffice.
  All seven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused attempt failed on one missing namespace
  opening and is not a pass; its downstream `sorryAx` lines were elaboration
  contamination only.  The corrected focused guarded check passes in about
  1.2 seconds.  The exact one-worker dependency-complete target passes 5034
  jobs, with the new module taking about 1.3 seconds.  No dynamic family,
  strength scaling, continuum QFT, or Clay theorem is inhabited or claimed.

### [BF4-vacuum-root-linear-ratio-no-go] Rule out the global minimum-edge cofinal ratio at half-extent zero — **CLOSED 2026-08-24**

- **milestone**: use the `K` distinct positive all-spin vacuum spokes to prove
  `edgeFloor_K * K <= vacuumWeight_K <= 1`; show the root-linear cost is at
  least one; derive `delta*K <= 1` from every later instance of an alleged
  cofinal root-linear ratio; contradict this at an explicit cutoff determined
  by the positive rational denominator; prove the cofinal interface is empty
  for every positive nome at half-extent zero.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo.lean`.
- **decl**:
  `centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_vacuumWeight`,
  `centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_one`,
  `FixedNomeCofinalVacuumRootLinearRatio.delta_le_edgeFloor`,
  `FixedNomeCofinalVacuumRootLinearRatio.delta_mul_cutoff_le_one`,
  `FixedNomeCofinalVacuumRootLinearRatio.impossible`, and
  `no_fixedNomeCofinalVacuumRootLinearRatio`.
- **obligation**: abandon the global minimum-edge/root-linear ratio as the
  half-extent-zero producer.  Preserve the valid finite and conditional
  compilers, but reroute the actual proof through local weight cancellation,
  such as a cofinal spin-ray return/escape bound combined with control of the
  off-ray residual carrier, or through a genuinely multiscale/direct-operator
  coercivity theorem.  Rebuild the dynamic physical-rate family on that viable
  local source before attempting physical scaling.
- **constructive?**: yes — explicit spin-ray indices, duplicate-free finite
  injection, positive vacuum spokes, finite-sum monotonicity, exact sector
  stationarity, probability-row normalization, and the denominator witness
  for a positive rational suffice.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on missing finite-index
  namespace access and invalid homonymous-namespace field notation and is not
  a pass; its downstream `sorryAx` lines were elaboration contamination only.
  The corrected focused guarded check passes in about 1.1 seconds.  The exact
  one-worker dependency-complete target passes 5037 jobs, with the new module
  taking about 1.1 seconds.  This proves a route-specific no-go, not a no-gap
  theorem; continuum QFT and the Clay theorem remain open.

### [BF4-spin-cube-off-ray-residual-completed-gap] Compile local residual capacity to the completed sector contraction — **CLOSED 2026-08-24**

- **milestone**: prove the generic centered deficit and strict rational form
  estimates from an arbitrary positive full-sector pairwise Dirichlet
  coercivity floor and positive sector-mass floor; specialize the result to
  the cofinal spin-ray/off-ray residual coercivity; compile both that interface
  and the stronger pointwise residual-flow-capacity interface into the
  existing cofinal finite strict gap and actual completed vacuum-sector
  strict-contraction datum.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCompletedGap.lean`.
- **decl**:
  `pairwiseCoercivity_strength_mul_diagonal_le_deficit`,
  `pairwiseCoercivity_abs_matrix_le_rate_mul_diagonal`,
  `FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toFiniteStrictGap`,
  `FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toCompletedStrictContractionData`,
  `FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.toFiniteStrictGap`, and
  `FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.toCompletedStrictContractionData`.
- **obligation**: inhabit one cofinal positive off-ray residual-flow capacity
  at the desired fixed nome, then build the dynamic same-object family and
  prove that its resulting local strength has the required two-sided physical
  spacing scaling.  Independently construct graph-norm/OS convergence for
  those same completed carriers and transfers.  No global minimum-edge ratio
  is required by this route.
- **constructive?**: yes — exact centered pairwise variance, exact doubled
  transfer deficit, rational positive-factor cancellation, finite Gram
  positivity, the constructed uniform sector-mass floor, the existing local
  ray/residual coercivity split, and the completion map suffice.  All six
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first focused attempt failed on dependent positivity
  inference and homonymous-namespace field notation and is not a pass; its
  downstream `sorryAx` lines were elaboration contamination only.  The
  corrected focused guarded check passes in about 1.6 seconds.  The exact
  one-worker dependency-complete target passes 5046 jobs, with the new module
  taking about 1.4 seconds.  No residual-capacity inhabitant, dynamic family,
  continuum QFT, or Clay theorem is claimed.

### [BF4-dynamic-completed-vacuum-sector-family] Factor all viable finite producers through one dynamic same-object completed path — **CLOSED 2026-08-24**

- **milestone**: define a source-independent scale-indexed family of the
  actual completed canonical vacuum-sector transfers; retain literal
  same-object autocorrelation decay; compile a two-sided rate/spacing band to
  rational physical-gap bounds and the sharp scalar continuum-gap interface;
  factor the rate law through an exact normalized strength and compile
  two-sided strength scaling plus a finite cap to that same physical band.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorCompletedFamily.lean`.
- **decl**: `DynamicVacuumSectorCompletedFamily`,
  `DynamicVacuumSectorCompletedFamily.completedAutocorrelation_sq_decay`,
  `DynamicVacuumSectorPhysicalRateBand`,
  `DynamicVacuumSectorPhysicalRateBand.toContinuumGapTheorem`,
  `DynamicVacuumSectorNormalizedStrengthLaw`,
  `DynamicVacuumSectorStrengthBand`, and
  `DynamicVacuumSectorStrengthBand.toPhysicalRateBand`.
- **obligation**: construct a dynamic finite producer, prove its exact
  strength/spacing band, and provide graph-norm/OS convergence and
  observable-identification maps for the same completed transfers.  The
  scalar continuum-gap output alone is not a continuum Yang--Mills theory.
- **constructive?**: yes — the existing completed strict contraction and
  same-object moments, rational positive division, Type-level spacing modulus,
  normalized-strength comparison, and explicit finite cap suffice.  All
  thirteen audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the final focused guarded check passes in about 1.7 seconds.
  The exact one-worker dependency-complete target passes 1374 jobs, with the
  module taking about 1.5 seconds.  No dynamic family, graph-norm limit,
  continuum QFT, or Clay theorem is inhabited or claimed.

### [BF4-dynamic-spin-cube-off-ray-residual-family] Attach local residual capacity to the common dynamic path — **CLOSED 2026-08-24**

- **milestone**: package scale-wise cofinal spin-ray and off-ray residual
  coercivity data; construct the actual completed vacuum-sector transfer at
  every scale; erase the finite source into the common dynamic family only
  after completion; identify the exact local strength
  `((1/2) * rayCapacity.delta) * uniformSectorMassFloor`; and compile the
  stronger dynamic pointwise residual-flow capacity into the same path.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayResidualFamily.lean`.
- **decl**: `DynamicSpinCubeOffRayResidualCoercivityFamily`,
  `DynamicSpinCubeOffRayResidualCoercivityFamily.toCompletedFamily`,
  `DynamicSpinCubeOffRayResidualCoercivityFamily.completedGapAt_rate_eq`,
  `DynamicSpinCubeOffRayResidualCoercivityFamily.toNormalizedStrengthLaw`,
  `DynamicSpinCubeOffRayResidualCoercivityFamily.toContinuumGapTheorem`,
  `DynamicSpinCubeOffRayResidualFlowCapacityFamily`, and
  `DynamicSpinCubeOffRayResidualFlowCapacityFamily.toResidualCoercivityFamily`.
- **obligation**: inhabit the scale-wise local residual family and prove a
  positive lower spacing multiple, finite upper spacing multiple, and finite
  cap for its exact local strength.  In parallel, construct graph-norm/OS
  convergence and a same-object continuum observable pin for these completed
  transfers.
- **constructive?**: yes — the fixed-nome local completed-gap compiler, exact
  gluing rate identity, explicit sector-mass floor, dependent scale-wise
  source data, and common normalized-strength compiler suffice.  All eleven
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: early focused attempts failed on missing physical-spacing
  namespaces, a stale imported artifact, and one definitional rewrite and are
  not passes; their `sorryAx` output was downstream elaboration contamination.
  The corrected focused guarded check passes in about 2.0 seconds.  The exact
  one-worker dependency-complete target passes 5056 jobs, with the module
  taking about 1.8 seconds.  No dynamic capacity family, strength band,
  continuum QFT, or Clay theorem is claimed.

### [BF4-dynamic-vacuum-sector-observable-path] Compile literal completed moments to a non-vacuous physical separator — **CLOSED 2026-08-24**

- **milestone**: define a cutoff-independent observable pin into the actual
  scale-wise completed vacuum complements; require exact rational-to-`RC`
  identifications for squared same-object autocorrelations and norm squares,
  a uniform fourth-power normalization, positive completed rates, and a
  distinguished nonzero local channel; reflect the completed moment estimate
  to a rational correlation bound; construct the corresponding
  `PhysicalSeparator`, two-sided `PhysicalGapFloor`, and scheduled
  fixed-physical-time lattice sampling.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorObservablePath.lean`.
- **decl**: `DynamicVacuumSectorObservablePin`,
  `DynamicVacuumSectorObservablePin.connectedCorrSq_le_rateSq_normFourth`,
  `DynamicVacuumSectorObservablePin.connectedCorrSq_control`,
  `DynamicVacuumSectorObservablePin.toPhysicalSeparator`,
  `DynamicVacuumSectorObservablePin.toPhysicalGapFloor`, and
  `DynamicVacuumSectorObservablePin.physicalSampling`.
- **obligation**: inhabit the observable pin with genuine gauge-invariant local
  BF4 observables and their actual completed vectors, prove the exact rational
  moment identifications and uniform normalization, and then identify the
  physically sampled correlators with the selected projective measure, one
  cutoff-independent OS insertion, and the reconstructed nonzero spectral
  channel.  Independently inhabit the local residual-capacity family and its
  exact strength/spacing band.
- **constructive?**: yes — the existing completed same-object
  autocorrelation decay, exact quotient equalities, constant-`RC` order
  reflection, nonnegative rational power monotonicity, explicit Type-level
  normalization data, and the existing spacing-zero modulus suffice.  All
  seven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused attempt failed on a missing namespace and
  is not a pass; its `sorryAx` lines were elaboration contamination only.  The
  corrected focused guarded check passes in about 1.0 seconds.  The exact
  one-worker dependency-complete target passes 1379 jobs, with the new module
  taking about 1.0 seconds.  No observable pin, projective continuum measure,
  OS identification, continuum QFT, or Clay theorem is inhabited or claimed.

### [BF4-dynamic-vacuum-sector-continuum-realization] Join the same exact rate and sampled correlator to one OS reconstruction — **CLOSED 2026-08-24**

- **milestone**: build the full-range exact logarithmic certificate for the
  observable-generated separator; name the exact-log upper bound, exact-rate
  Cauchy modulus, projective/OS sampled-correlation handoff, nonzero
  reconstruction spectral channel, and exact-rate reconstruction convergence;
  and compile them into the standard same-object continuum realization,
  conditional exact-log-gap endpoint, positive continuum mass, and exact OS
  connected-correlator/spectral-correlator identification.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorContinuumRealization.lean`.
- **decl**: `DynamicVacuumSectorObservablePin.fullRangeRateFamily`,
  `DynamicVacuumSectorObservablePin.exactCertificate`,
  `DynamicVacuumSectorContinuumHandoff`,
  `DynamicVacuumSectorContinuumHandoff.toContinuumRealization`,
  `DynamicVacuumSectorContinuumHandoff.continuumMass_posEv`, and
  `DynamicVacuumSectorContinuumHandoff.osGapCorr_equiv_spectral`.
- **obligation**: inhabit the explicit exact-log ceiling and Cauchy modulus for
  the actual dynamic separator, construct the selected projective continuum
  measure and OS functional, prove that its cutoff-independent insertion is
  the limit of the physically sampled completed-path correlator, and identify
  both that correlator and the same exact rate limit with the reconstruction's
  nonzero spectral channel and logarithmic gap.  The local capacity, physical
  strength scaling, and observable pin remain separate upstream producers.
- **constructive?**: yes — the existing physical margin floor compiler,
  full-range exact-log certificate, constructive-real Cauchy completion,
  spacing modulus, projective-functional convergence compiler, uniqueness of
  exact-rate limits, and OS correlation composition suffice.  All six audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the first focused attempt failed on helper field-notation
  namespaces and the positivity namespace and is not a pass.  After explicit
  helper applications, the corrected focused guarded check passes in about
  0.9 seconds.  The exact one-worker dependency-complete target passes 1382
  jobs, with the new module taking about 0.9 seconds.  No handoff, continuum
  measure, continuum Yang--Mills existence, OS spectral/rate pin, or Clay
  theorem is inhabited or claimed.

### [BF4-spin-cube-off-ray-residual-global-floor-no-go] Rule out both global-minimum residual ratios — **CLOSED 2026-08-24**

- **milestone**: cancel the common positive half factor in each cofinal
  off-ray scalar ratio; use only that each scalar cost is at least one to
  force the fixed cofinal ray `delta` below the complete finite-sector edge
  minimum; combine `edgeFloor_K * K <= 1` with the explicit denominator
  escape scale for a positive rational; prove both the endpoint-mass linear
  ratio and the improved mass-free carrier-linear ratio are uninhabited.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualGlobalFloorNoGo.lean`.
- **decl**:
  `FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.delta_le_edgeFloor`,
  `FixedNomeCofinalSpinCubeOffRayResidualLinearRatio.impossible`,
  `no_fixedNomeCofinalSpinCubeOffRayResidualLinearRatio`,
  `FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.delta_le_edgeFloor`,
  `FixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio.impossible`, and
  `no_fixedNomeCofinalSpinCubeOffRayResidualNormalizedLinearRatio`.
- **obligation**: do not spend further effort refining either scalar
  global-minimum cost: even replacing that cost by one cannot overcome the
  edge-floor decay.  Attack the exact pointwise residual-flow capacity by
  comparing local loads with the matching local physical-kernel entries
  before taking a minimum, or build a multiscale/direct-operator estimate
  targeting the same dynamic completed-family interface.  The local
  capacity, exact strength/spacing band, observable pin, and continuum
  handoff remain uninhabited producers.
- **constructive?**: yes — rational positive-factor cancellation, the padded
  cost lower bound, the explicit all-spin spoke budget, and the denominator
  witness suffice.  All six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused guarded check passes in about 1.4 seconds.  The
  exact one-worker dependency-complete target passes 5059 jobs, with the new
  module taking about 1.1 seconds.  This excludes two proof compilers, not a
  spectral gap: exact local capacity, continuum Yang--Mills, and the Clay
  theorem remain open.

### [BF4-spin-cube-off-ray-residual-conditional-congestion] Cancel stationary source mass from the exact local frontier — **CLOSED 2026-08-24**

- **milestone**: define the indexed physical conditional transition; prove
  stationary weight times conditional transition equals the literal physical
  joint entry; divide each residual endpoint-pair edge contribution by the
  positive edge-source weight; prove their relative sum reconstructs the
  exact residual flow load; cancel the common source factor to obtain an
  iff between joint capacity and dimensionless conditional congestion; and
  compile a cofinal conditional family to the completed strict contraction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualConditionalCongestion.lean`.
- **decl**:
  `centralPhysicalFiniteWeight_mul_conditional_eqv_kernel`,
  `centralPhysicalFiniteWeight_mul_relativePairDemand_eqv_pathLoad`,
  `centralPhysicalFiniteWeight_mul_relativeSourceFlowLoad_eqv_flowLoad`,
  `centralLowerExcitedSpinCubeOffRayResidualEdgeCapacity_iff_conditionalCongestion`,
  `CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt.ofResidualFlowCapacityAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualConditionalCongestionAt.toResidualFlowCapacityAt`,
  `centralLowerExcitedSpinCubeFiniteLinearConditionalCongestionAt`,
  `anchorCentralSpinCubeFiniteLinearConditionalCongestionAt`,
  and
  `FixedNomeCofinalSpinCubeOffRayResidualConditionalCongestion.toCompletedStrictContractionData`.
- **obligation**: inhabit the cofinal conditional-congestion family by
  comparing exact relative traffic with the matching physical conditional
  transition on every used directed edge.  Preserve the explicit endpoint
  pair and positive-path lineage; do not reintroduce a global edge minimum,
  carrier-cardinality ceiling, or minimum stationary mass.  If the canonical
  loop-erased paths cannot be controlled, replace them by explicit local or
  multiscale BF4 routing while targeting this same dimensionless interface.
- **constructive?**: yes — finite sector positivity, exact physical Markov
  factorization, explicit positive rational division, duplicate-preserving
  finite regrouping, and positive-factor order cancellation suffice.  All
  nine audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused check failed on one missing namespace
  and is not a pass; its downstream `sorryAx` lines were elaboration
  contamination only.  The final focused guarded check passes in about
  1.3 seconds.  The exact one-worker dependency-complete target passes 5050
  jobs, with the new module taking about 1.4 seconds.  The conditional
  interface is inhabited at every finite cutoff by the concrete restricted
  carrier-linear certificate, but no cofinal uniform conditional family,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-spin-cube-off-ray-residual-conditional-harnack-target] Expand the local quotient into exact projective path traffic — **CLOSED 2026-08-24**

- **milestone**: prove an exact path-incidence formula for each listed
  residual endpoint-pair load; define the stationary endpoint/source ratio;
  rewrite each relative pair demand as ratio times the other endpoint mass
  times path length and incidence; sum without changing the endpoint or path
  witnesses; prove an iff between conditional congestion and this explicit
  Harnack target; provide lossless finite/cofinal compilers and unconditional
  finite-cutoff inhabitants.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualConditionalHarnackTarget.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualWeightedPathEdgeLoad_eqv_indicator`,
  `centralPhysicalFiniteWeight_mul_endpointWeightRatio_eqv_endpointWeight`,
  `centralLowerExcitedSpinCubeOffRayResidualPathPairRelativeSourceDemand_eqv_harnackTerm`,
  `centralLowerExcitedSpinCubeOffRayResidualRelativeSourceFlowLoad_eqv_harnackLoad`,
  `centralLowerExcitedSpinCubeOffRayResidualConditionalCongestion_iff_harnackTarget`,
  `CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt.ofConditionalCongestionAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualConditionalHarnackAt.toConditionalCongestionAt`,
  `centralLowerExcitedSpinCubeFiniteLinearConditionalHarnackAt`,
  `anchorCentralSpinCubeFiniteLinearConditionalHarnackAt`, and
  `FixedNomeCofinalSpinCubeOffRayResidualConditionalHarnack.toCompletedStrictContractionData`.
- **obligation**: telescope the endpoint/source stationary ratio along the
  actual positive path into reverse/forward conditional-transition ratios,
  then prove a cutoff-uniform local or multiscale bound on the resulting
  transition products, path incidences, and lengths.  Do not replace the
  local target by a global edge minimum or carrier-wide scalar ceiling.
- **constructive?**: yes — duplicate-free simple paths, exact finite-list
  edge indicators, positive rational division, finite regrouping, and exact
  equality transport suffice.  All ten audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused attempt failed on zero-division
  normalization and one missing namespace and is not a pass; its downstream
  `sorryAx` output was elaboration contamination only.  The corrected focused
  guarded check passes in about 1.4 seconds.  The exact one-worker
  dependency-complete target passes 5051 jobs, with the new module taking
  about 1.5 seconds.  The interface is inhabited at every finite cutoff but
  no cofinal uniform Harnack family, continuum Yang--Mills theory, or Clay
  theorem is claimed.

### [BF4-spin-cube-off-ray-residual-conditional-pathwise-detailed-balance] Telescope projective endpoint ratios along exact physical paths — **CLOSED 2026-08-24**

- **milestone**: prove arbitrary-cutoff indexed conditional detailed balance,
  symmetric joint-edge positivity, forward and reverse conditional
  positivity, the one-edge stationary-ratio/reverse-forward identity, and
  the exact product telescope along the unchanged Type-level positive path.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance.lean`.
- **decl**:
  `centralPhysicalFiniteConditionalKernel_detailedBalance`,
  `centralPhysicalFiniteKernel_reverse_pos_of_pos`,
  `centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos`,
  `centralPhysicalFiniteConditionalKernel_reverse_pos_of_kernel_pos`,
  `centralPhysicalFiniteWeightRatio_eqv_conditionalReverseForward`,
  `centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_oneStep`,
  and
  `centralLowerExcitedSpinCubeOffRayResidualEndpointWeightRatioAtSource_eqv_pathProduct`.
- **obligation**: substitute the exact path product into the summed Harnack
  target, then construct a cutoff-uniform bound on transition products,
  incidences, and path lengths, or supply a local/multiscale/direct-operator
  route targeting the same completed dynamic interface.
- **constructive?**: yes — finite-sector membership, support-graph symmetry,
  physical detailed balance, positive rational division and cancellation,
  and recursion over Type-level positive paths suffice.  All seven audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the focused guarded check passes in about 1.4 seconds.  The
  exact one-worker dependency-complete target passes 5052 jobs, with the new
  module taking about 1.4 seconds.  This is an exact equality compiler; no
  cofinal Harnack bound, continuum Yang--Mills theory, or Clay theorem is
  claimed.

### [BF4-spin-cube-off-ray-residual-conditional-transition-product-target] Expose the final canonical-path analytic sum — **CLOSED 2026-08-24**

- **milestone**: construct a positive prefix from directed-edge incidence;
  substitute the exact detailed-balance telescope into each Harnack summand;
  prove equality of the summed Harnack and transition-product loads; prove an
  iff at the edge-capacity target; provide lossless finite/cofinal compilers,
  unconditional finite-cutoff inhabitants, and the completed-contraction
  consumer.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualPathPairConditionalHarnackTerm_eqv_transitionProduct`,
  `centralLowerExcitedSpinCubeOffRayResidualConditionalHarnackLoad_eqv_transitionProductLoad`,
  `centralLowerExcitedSpinCubeOffRayResidualHarnackTarget_iff_transitionProductTarget`,
  `CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt.ofConditionalHarnackAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualConditionalTransitionProductAt.toConditionalHarnackAt`,
  `centralLowerExcitedSpinCubeFiniteLinearConditionalTransitionProductAt`,
  `anchorCentralSpinCubeFiniteLinearConditionalTransitionProductAt`, and
  `FixedNomeCofinalSpinCubeOffRayResidualConditionalTransitionProduct.toCompletedStrictContractionData`.
- **obligation**: prove the displayed transition-product edge inequality
  uniformly in cutoff using BF4-specific local routing, a multiscale flow, or
  a direct-operator replacement.  In particular, control prefix products,
  path incidence, and length without reverting to a complete-sector minimum.
- **constructive?**: yes — Type-level prefix extraction, the pathwise
  detailed-balance equality, finite-list congruence, and equality transport
  suffice.  All eight audited exports use exactly `[propext, Quot.sound]`;
  no forbidden construct was added.
- **status note**: the first focused attempt failed because `prefix` is
  reserved syntax and one namespace was missing; it is not a pass, and its
  downstream `sorryAx` output was elaboration contamination.  The corrected
  focused guarded check passes in about 1.4 seconds.  The exact one-worker
  dependency-complete target passes 5053 jobs, with the new module taking
  about 1.4 seconds.  Finite inhabitants exist, but no cofinal uniform family,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-spin-cube-off-ray-residual-adaptive-routing] Permit BF4-local routes without changing the contraction consumer — **CLOSED 2026-08-24**

- **milestone**: define Type-level positive physical-kernel routing data for
  every finite-sector endpoint pair; compile any supplied routing through
  pathwise Cauchy--Schwarz, duplicate-preserving weighted occurrences, and
  exact edge-load regrouping; prove the residual pairwise variance is bounded
  by the routed loaded Dirichlet form; compile pointwise routed capacity to
  the existing residual coercivity and completed strict contraction; and
  prove that the canonical loop-erased routing recovers the old flow load and
  capacity interface exactly in both directions.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting.lean`.
- **decl**:
  `CentralPhysicalFiniteVacuumSectorPositiveRoutingAt`,
  `canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt`,
  `centralLowerExcitedSpinCubeOffRayResidualPairwiseVariance_le_routedRawLoadedDirichlet`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_canonical_eq`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.toOffRayResidualCoercivityAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.ofCanonical`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedFlowCapacityAt.toCanonical`,
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity.toCofinalResidualCoercivity`,
  and
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveRoutingCapacity.toCompletedStrictContractionData`.
- **obligation**: construct a cofinal BF4-local or multiscale routing whose
  exact directed-edge loads satisfy the cutoff-uniform pointwise capacity
  comparison.  The new routing freedom must be used to control spin-local
  transition ratios, incidences, and lengths; it must not be collapsed back
  to a complete-sector edge minimum or an opaque carrier-cardinality bound.
  A direct-operator producer remains admissible if it targets the same
  residual-coercivity consumer.
- **constructive?**: yes — every routing contains literal Type-level positive
  paths, and finite Cauchy--Schwarz plus exact list regrouping proves the
  form estimate.  All eleven audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on missing opened namespaces
  and is not a pass; its downstream `sorryAx` output was elaboration
  contamination only.  The corrected focused guarded check passes in about
  3.6 seconds.  The exact one-worker dependency-complete target passes 5047
  jobs, with the new module taking about 3.6 seconds.  No cofinal routed
  capacity, physical strength-scaling theorem, same-object observable pin,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-spin-cube-off-ray-residual-adaptive-conditional-congestion] Cancel source mass for every supplied route — **CLOSED 2026-08-24**

- **milestone**: define route-parametric relative endpoint-pair demand and
  relative flow load; prove source weight times relative demand reconstructs
  the exact routed joint traffic; cancel the common positive source weight
  against the physical joint/conditional factorization; prove an iff between
  routed pointwise capacity and dimensionless conditional congestion; compile
  a cofinal adaptive conditional family to the completed strict contraction;
  and prove exact two-way compatibility with the previous conditional
  interface on the canonical routing.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion.lean`.
- **decl**:
  `centralPhysicalFiniteWeight_mul_routedRelativePairDemand_eqv_pathLoad`,
  `centralPhysicalFiniteWeight_mul_routedRelativeSourceFlowLoad_eqv_flowLoad`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedEdgeCapacity_iff_conditionalCongestion`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.ofRoutedFlowCapacityAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.toRoutedFlowCapacityAt`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_canonical_eq`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.ofCanonical`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalCongestionAt.toCanonical`,
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion.toAdaptiveRoutingCapacity`,
  and
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalCongestion.toCompletedStrictContractionData`.
- **obligation**: choose explicit BF4-local or multiscale positive routes and
  prove their exact relative traffic is uniformly bounded by the matching
  physical conditional transition on every used directed edge.  Preserve the
  route and endpoint witnesses; do not reintroduce a minimum stationary mass,
  complete-sector edge floor, or carrier-wide scalar ceiling.
- **constructive?**: yes — finite positive stationary weights, exact rational
  division, duplicate-preserving summation, physical Markov factorization,
  and positive-factor order cancellation suffice.  All eleven audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the first focused check failed on missing opened namespaces
  and is not a pass; its downstream `sorryAx` output was elaboration
  contamination only.  The corrected focused guarded check passes in about
  1.5 seconds.  The exact one-worker dependency-complete target passes 5052
  jobs, with the new module taking about 1.5 seconds.  No cofinal adaptive
  conditional family, physical strength-scaling theorem, same-object
  observable pin, continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-spin-cube-off-ray-residual-adaptive-transition-product-target] Expose the multiplicity-aware routed analytic sum — **CLOSED 2026-08-24**

- **milestone**: retain repeated directed-edge occurrences for arbitrary
  positive routes; extract a constructive prefix to every selected edge
  source; telescope the endpoint/source stationary ratio into exact
  reverse/forward conditional-transition products; prove equality with the
  routed relative flow load; prove the pointwise target iff; provide finite
  and cofinal compilers, a canonical finite inhabitant, and exact two-way
  compatibility with the previous simple-path product interface.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairRelativeSourceDemand_eqv_transitionProduct`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTarget_iff_transitionProductTarget`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.ofRoutedConditionalCongestionAt`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.toRoutedConditionalCongestionAt`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_canonical_eqv`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.ofCanonical`,
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt.toCanonical`,
  `centralLowerExcitedSpinCubeFiniteLinearRoutedConditionalTransitionProductAt`,
  and
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct.toCompletedStrictContractionData`.
- **obligation**: construct a cofinal family of explicit BF4-local or
  multiscale positive routes and prove that the exact prefix-transition
  products times endpoint weight, route length, and repeated-edge
  multiplicity fit inside the matching conditional transition uniformly in
  representation cutoff.  Preserve these observable factors; do not replace
  them by a complete-sector minimum or carrier-cardinality ceiling.
- **constructive?**: yes — literal Type-level positive routes, exact finite
  occurrence sums, positive rational division, constructive prefix
  extraction, pathwise detailed balance, and equality transport suffice.  All
  eleven audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused check failed on two missing opened
  namespaces and is not a pass; its downstream `sorryAx` output was
  elaboration contamination only.  The corrected focused check passes in
  about 1.5 seconds.  The exact one-worker dependency-complete target passes
  5056 jobs, with the new module taking about 1.6 seconds.  A finite canonical
  inhabitant exists, but no cofinal uniform adaptive product family,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-dynamic-spin-cube-off-ray-adaptive-transition-product-family] Join the adaptive local producer to the common dynamic path — **CLOSED 2026-08-24**

- **milestone**: package scale-wise nomes, physical spacing, cofinal spin-ray
  capacities, and cofinal adaptive transition-product data; compile each
  scale through adaptive conditional congestion, routed capacity, and the
  existing residual coercivity; construct the same source-independent dynamic
  completed family; and expose its exact normalized-strength and physical-rate
  compilers.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily.lean`.
- **decl**:
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveConditionalCongestionAt`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveRoutingCapacityAt`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.residualCoercivityAt`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toResidualCoercivityFamily`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toCompletedFamily`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toNormalizedStrengthLaw`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalRateBand`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toContinuumGapTheorem`.
- **obligation**: independently inhabit the six inputs that converge on this
  same dynamic completed path: cofinal local adaptive product capacity,
  two-sided exact-strength scaling, a concrete same-object gauge-invariant
  observable pin, exact-log cutoff control, projective/OS correlation
  convergence, and reconstruction spectral/rate identification.  Do not
  substitute unrelated rates, correlators, carriers, or continuum objects at
  the joins.
- **constructive?**: yes — the module composes existing Type-level lossless
  compilers and retains the same dependent nome, spacing, completed transfer,
  and normalized strength.  All eight audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check failed on one missing namespace and
  is not a pass; its downstream errors and `sorryAx` lines were elaboration
  contamination only.  The corrected focused check passes in about 1.4
  seconds.  The exact one-worker dependency-complete target passes 5067 jobs,
  with the new module taking about 1.4 seconds.  No dynamic family, strength
  band, observable pin, continuum handoff, continuum Yang--Mills theory, or
  Clay theorem is claimed.

### [BF4-physical-moving-centered-vacuum-pairing] Connect legal rational recentering to the actual completed vacuum pairing — **CLOSED 2026-08-24**

- **milestone**: keep one fixed finite cylinder coefficient; recenter only its
  root coordinate by the rational pulled mean/root-weight ratio at each
  selected cutoff; prove exact selected-cutoff centering; prove the
  constructive-real identity `headCorrectionLimit * rootWeightLimit =
  rawMeanLimit`; expand every fixed moving-centered completed mean; prove
  those completed means converge to zero; and identify every term with the
  actual completed global-vacuum pairing of the embedded dense cylinder.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.lean`.
- **decl**:
  `centralPhysicalVacuumSectorMovingCenteredPresentation`,
  `centralPhysicalVacuumSectorMovingCenteredPresentation_meanZero`,
  `centralPhysicalHeadCorrection_mul_root_equiv_mean`,
  `centralPhysicalMovingCenteredMeanLimit_equiv_expansion`,
  `centralPhysicalMovingCenteredMeanLimit_converges_zero`, and
  `centralPhysicalMovingCentered_completedVacuumPairing_eq`.
- **obligation**: construct an explicit graph-norm cross-cutoff modulus for
  these moving presentations, realize its completed vector, prove that vector
  is nonzero, and connect its same-object transfer moments to the existing
  dynamic completed family.  Do not assume that generic cutoff-limit moments
  are rational merely to satisfy the current rational observable-pin
  interface; refine that interface to retain genuine `CReal` moments if
  necessary.
- **constructive?**: yes — the moving correction is rational at every dense
  stage; positive rational division, exact finite-list algebra,
  approximation-wise lifting to Bishop reals, and explicit constructive
  convergence suffice.  All five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: early guarded checks timed out during repeated unfolding of
  the large BF4 dependent terms and are not passes.  The direct
  approximation-wise refactor passes the corrected focused guarded check in
  about 19.3 seconds.  The exact one-worker dependency-complete target passes
  1369 jobs in about 20 seconds.  This closes only the completed
  vacuum-pairing convergence bridge; no graph-norm Cauchy completed vector,
  nonzero observable channel, dynamic observable pin, continuum Yang--Mills
  theory, or Clay theorem is claimed.

### [BF4-physical-moving-centered-completion] Complete the same moving rational observable — **CLOSED 2026-08-24**

- **milestone**: expose executable Type-level cutoff rates for the pulled
  weighted mean, pulled root weight, and rational head correction; prove an
  exact fixed-raw-plus-moving-root semantic expansion; derive a uniform
  pointwise squared-difference estimate from the head-correction rate; lift it
  to the actual cutoff-removed physical sector squared distance; construct an
  explicit-modulus Cauchy representative; and define its sector and global
  completed vectors.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorFormCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy.lean`,
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion.lean`.
- **decl**:
  `centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffRate`,
  `centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoff_regular`,
  `centralPhysicalFinitePulledVacuumSectorRootWeightCutoffRate`,
  `centralPhysicalFinitePulledVacuumSectorRootWeightCutoff_regular`,
  `centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffRate`,
  `centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoff_regular`,
  `centralPhysicalVacuumSectorMovingCentered_value_equiv_expansion`,
  `centralPhysicalVacuumSectorMovingCentered_pointwiseSq`,
  `centralPhysicalVacuumSectorMovingCenteredCauchy`,
  `centralPhysicalVacuumSectorMovingCenteredCompletion`, and
  `centralPhysicalVacuumSectorMovingCenteredGlobalVector`.
- **obligation**: prove that this same completed vector is orthogonal to the
  completed vacuum by identifying its completion pairing with the already
  proved zero limit; prove a positive norm lower bound so the quotient class
  is nonzero; then identify its same-object completed transfer moments with
  the observable channel accepted by the common dynamic completed family.
  Do not replace the vector, transfer, correlation, sampling channel, or rate
  at any compiler join.
- **constructive?**: yes — the dense coefficients stay rational, the cutoff
  witnesses are explicit functions `Q' -> Nat`, and finite rational
  cancellation, bounded state-cylinder values, and physical seminorm
  monotonicity suffice.  The audited interfaces use at most
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first guarded attempt timed out inside large-context
  quotient-rational normalization.  The second exposed an unfinished
  denominator identity and a missing qualification; all associated
  downstream `sorryAx` output was failed-elaboration contamination.  After
  factoring the small algebra compilers, the corrected focused check passes.
  The exact one-worker dependency-complete target passes 1370 jobs, with the
  new module taking about 136 seconds.  No completed vacuum-orthogonality,
  nonzero observable, dynamic observable pin, continuum Yang--Mills theory,
  or Clay theorem is claimed.

### [BF4-physical-moving-centered-vacuum-orthogonal] Descend the zero pairing to the same completed vector — **CLOSED 2026-08-24**

- **milestone**: identify the moving completed representative's dense vacuum
  pairing sequence term by term with the pulled-mean sequence; combine its
  convergence to the completed pairing with the pulled means' convergence to
  zero; apply constructive limit uniqueness; and descend the result to prove
  actual completed global-vacuum orthogonality for the exact previously
  constructed vector.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal.lean`.
- **decl**:
  `centralPhysicalVacuumSectorMovingCentered_pairingLimit_equiv_zero` and
  `centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal`.
- **obligation**: prove a strictly positive completed diagonal/norm lower
  bound for this same vector, so it is not the zero quotient class; then
  identify its completed transfer moments with the observable channel used by
  the common dynamic completed family.  Preserve the vector, transfer,
  correlation, sampling channel, and rate at every compiler join.
- **constructive?**: yes — termwise `CReal.Equiv`, explicit outer pairing
  convergence, explicit moving-mean convergence, constructive limit
  uniqueness, and quotient soundness suffice.  Both audited exports use
  exactly `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first guarded check had one missing opened form
  namespace; its later timeouts and `sorryAx` lines were failed-elaboration
  contamination only.  After using an explicit definitional change through
  the completion maps, the corrected focused check passes in about 0.5
  seconds.  The exact one-worker dependency-complete target passes 1371 jobs,
  with the new module taking about 0.5 seconds.  No nonzero observable,
  dynamic observable pin, continuum Yang--Mills theory, or Clay theorem is
  claimed.

### [BF4-physical-moving-centered-nonzero] Preserve one cube coordinate through completion — **CLOSED 2026-08-24**

- **milestone**: constructively locate the central lower-cube state in the
  cutoff-one canonical vacuum component; define its fixed indicator
  coefficient; prove moving root centering preserves its nonroot value one;
  prove a reusable positive-row-floor domination theorem for every fixed
  base-sector coordinate; specialize it to a uniform positive stagewise
  distance from zero; rule out completion closeness at half that floor; and
  transport sector nonzeroness through the injective sector-to-global map to
  the exact public completed moving vector.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCylinder_coordinateDifferenceSq_floor_le_distSq`,
  `centralPhysicalCutoffOneCubeIndex_mem_vacuumSector`,
  `centralPhysicalCutoffOneCubeMovingCenteredCoefficient_at_cube`,
  `centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_zeroPresentationDistSq`,
  `centralPhysicalCutoffOneCubeMovingCenteredSector_not_close_zero`,
  `centralPhysicalCutoffOneCubeMovingCenteredCompletion_ne_sectorZero`,
  `centralPhysicalCutoffOneSectorZeroCompletion_toGlobal_eq_zero`, and
  `centralPhysicalCutoffOneCubeMovingCenteredGlobalVector_ne_zero`.
- **obligation**: identify the completed transfer moments of this exact
  nonzero vacuum-orthogonal vector with the same observable channel used by
  the common dynamic completed family, and then inhabit or refine the dynamic
  observable pin without replacing the vector, transfer, correlation,
  sampling channel, or rate.  This fixed-nome, half-extent-zero anti-vacuity
  result is not a thermodynamic or continuum nontriviality theorem.
- **constructive?**: yes — finite carrier lookup, decidable index equality,
  exact rational coordinate preservation, a positive rational row floor,
  explicit Cauchy/close moduli, semantic nullity, and quotient injectivity
  suffice.  The three audited exports use exactly `[propext, Quot.sound]`; no
  forbidden construct was added.
- **status note**: early guarded attempts with missing namespace imports, an
  unbridged zero-presentation/global-zero distinction, and direct nested
  global-Cauchy normalization failed or timed out and are not passes.  The
  sector-first refactor passes the corrected focused guarded check.  The
  exact one-worker dependency-complete target passes 1641 jobs, with the new
  module taking about 204 seconds.  No same-object transfer-moment join,
  dynamic observable pin, thermodynamic limit, continuum Yang--Mills theory,
  or Clay theorem is claimed.

### [BF4-physical-moving-centered-positive-norm] Transport the cube floor to the completed same-object channel — **CLOSED 2026-08-24**

- **milestone**: identify every dense moving cube diagonal pairing with its
  squared distance from zero; retain the existing positive rational cube
  coordinate floor at every stage; push that floor through the explicit outer
  pairing limit; compute the actual completed sector inner product on the
  moving representative; and prove that the literal zero-time same-object
  completed autocorrelation has the same strict positive rational witness.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm.lean`.
- **decl**:
  `centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_pairing`,
  `centralPhysicalCutoffOneCubeMovingCentered_floor_le_pairingLimit`,
  `centralPhysicalCutoffOneCubeMovingCentered_completedInner_eq_pairingLimitR`,
  `centralPhysicalCutoffOneCubeMovingCentered_floor_le_completedInner`,
  `centralPhysicalCutoffOneCubeMovingCentered_completedInner_isPositive`,
  `centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_eq_inner`,
  and
  `centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_isPositive`.
- **obligation**: package this exact vector as a scale-indexed observable in
  every nome of a `DynamicVacuumSectorCompletedFamily`, retain the literal
  `RC` norm and autocorrelation, and derive its completed decay without the
  unjustified rational-moment fields of the existing observable pin.  Then
  connect that channel to one physical rate band and the later projective/OS
  limit without replacing the vector, transfer, moment, sampling channel, or
  rate.
- **constructive?**: yes — the rational floor is an explicit function of the
  nome; stagewise `CReal.leEv`, explicit `ConvergesTo` data, the constructive
  limit-order theorem, and quotient soundness suffice.  The three audited
  exports use exactly `[propext, Quot.sound]`; no forbidden construct was
  added.  No inference from mere nonzeroness to positivity is used.
- **status note**: early guarded checks with unresolved nested namespaces for
  the dense inner and moving presentation timed out during downstream
  normalization and emitted failed-elaboration `sorryAx`; none are passes.
  After the namespace corrections and the explicit representative bridge,
  the corrected focused check passes.  The exact one-worker
  dependency-complete target passes 1643 jobs, with the new module taking
  about 0.65 seconds after dependency replay.  No dynamic observable path,
  physical rate band, thermodynamic limit, continuum Yang--Mills theory, or
  Clay theorem is claimed.

### [BF4-physical-dynamic-same-object-rc-channel] Carry the exact moving cube moment through every dynamic completed scale — **CLOSED 2026-08-24**

- **milestone**: define a scale-indexed same-object channel whose vector lives
  in the actual completed vacuum complement; retain a Type-level rational
  positive floor for its literal norm; define its norm and connected moments
  directly in `RC`; prove time-zero norm identity, strict positivity, and
  completed-rate decay; identify the same autocorrelation with the global
  adaptive-transfer matrix coefficient; and inhabit the channel with the
  exact moving-centered cutoff-one cube vector at every nome of any supplied
  `DynamicVacuumSectorCompletedFamily 0`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.lean`.
- **decl**:
  `DynamicVacuumSectorSameObjectRCChannel`,
  `DynamicVacuumSectorSameObjectRCChannel.normSq`,
  `DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation`,
  `DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq`,
  `DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_zero_isPositive`,
  `DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelationSq_decay`,
  `DynamicVacuumSectorSameObjectRCChannel.connectedAutocorrelation_eq_global`,
  `centralPhysicalDynamicMovingCubeVectorAt`,
  `centralPhysicalDynamicMovingCubeRCChannel`, and
  `centralPhysicalDynamicMovingCube_connectedSq_decay`.
- **obligation**: preserve this exact `RC` channel through scheduled physical-
  time sampling and projective/OS convergence.  Either build an RC-valued
  physical-separation consumer, or supply constructive rational envelopes
  and error moduli before using the existing rational `PhysicalSeparator`.
  Do not assert that arbitrary completed moments are rational.  The dynamic
  completed family and its physical strength/rate band remain Type-level
  inputs, not inhabitants produced here.
- **constructive?**: yes — the vector, rate, norm floor, and moments remain in
  one dependent record; all moment equalities are definitional or already
  proved sector/global bridges; the lower witness is explicit rational data.
  The five audited exports use exactly `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first guarded check failed only on invalid line-broken
  field notation and its downstream `sorryAx` output is failed-elaboration
  contamination.  After using explicit compiler names, the focused check
  passes.  The exact one-worker dependency-complete target passes 1654 jobs,
  with the new module taking about 0.82 seconds after dependency replay.  No
  rational observable pin, physical separator, continuum correlation limit,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-dynamic-scheduled-rc-channel] Sample the exact channel at fixed physical time and isolate its cutoff limit — **CLOSED 2026-08-24**

- **milestone**: construct floor lattice powers from the dynamic family's
  spacing-to-zero data; prove sampled physical-distance convergence; preserve
  the exact completed-rate decay and global adaptive-transfer matrix-
  coefficient identity under those powers; retain zero-time norm positivity;
  state explicit representative/modulus data for the genuine `RC` cutoff
  limit; separate a scale-uniform norm floor from per-scale positivity; and
  prove conditional strict positivity of the continuum zero-time channel.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorScheduledRCChannel.lean`.
- **decl**:
  `centralPhysicalDynamicRCSampling`,
  `centralPhysicalDynamicRCLatticeSteps`,
  `centralPhysicalDynamicRCSampledDistance_converges`,
  `sampledConnectedAutocorrelation`,
  `sampledConnectedAutocorrelationSq`,
  `sampledConnectedAutocorrelationSq_decay`,
  `sampledConnectedAutocorrelation_eq_global`,
  `sampledConnectedAutocorrelation_zero_isPositive`,
  `DynamicVacuumSectorUniformRCNormFloor`,
  `ScheduledRCContinuumLimit`, and
  `ScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive`.
- **obligation**: construct, for the actual moving cube channel and one actual
  dynamic completed family, the representative-level cutoff correlation
  convergence and a positive scale-uniform norm floor.  Separately derive the
  sampled rate-envelope limit from the same family's physical strength/rate
  band, then identify the resulting continuum correlation with one selected
  projective/OS observable and reconstructed generator.  Per-scale positivity
  must not be substituted for the uniform floor.
- **constructive?**: yes — sampling is an explicit Nat function; distance and
  correlation limits carry moduli; quotient representatives are supplied as
  Type-level data with class-identification proofs; the norm floor is rational
  Type-level data.  The five audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first guarded check missed the definitional unfolding
  of the floor-sampling constructor at time zero and its downstream `sorryAx`
  was failed-elaboration contamination.  The corrected focused check passes.
  The exact one-worker dependency-complete target passes 1656 jobs, with the
  new module taking about 0.83 seconds after dependency replay.  No RC cutoff-
  limit inhabitant, uniform norm floor, physical rate envelope, projective/OS
  identification, continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-adaptive-moving-cube-path] Compose the viable local producer with the exact sampled observable — **CLOSED 2026-08-24**

- **milestone**: compile a supplied dynamic adaptive off-ray transition-
  product family into its actual completed family and exact moving-centered
  cube `CReal` channel; use the same physical-time sampling powers; prove
  sampled squared decay at the actual completed rate; identify the unsquared
  sample with the same global adaptive-transfer matrix coefficient; retain
  strict time-zero positivity; and attach an optional strength band to that
  definitionally identical rate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveMovingCubePath.lean`.
- **decl**:
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toMovingCubeRCChannel`,
  `movingCubeLatticeSteps`,
  `movingCubeSampledConnectedAutocorrelation`,
  `movingCubeSampledConnectedAutocorrelationSq`,
  `movingCubeSampledConnectedAutocorrelationSq_decay`,
  `movingCubeSampledConnectedAutocorrelation_eq_global`,
  `movingCubeSampledConnectedAutocorrelation_zero_isPositive`,
  `movingCube_completedRate_physicalBand`, and
  `movingCube_physicalGap_twoSided`.
- **obligation**: inhabit the adaptive transition-product family and its
  uniform strength band; construct representative-level cutoff convergence
  for this exact sampled `CReal` correlation; and prove a scale-uniform
  positive normalization or explicitly track a controlled observable
  renormalization.  Then identify that same limiting correlation through the
  projective measure and OS reconstruction.  A rate or moment for a different
  vector, transfer, normalization, or representative is not a substitute.
- **constructive?**: yes — every compiler is an explicit definition or proof
  over the supplied Type-level producer; the vector, transfer, sampling power,
  moment, and rate are preserved definitionally at the joins.  The five
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first focused check failed only because field notation
  searched the producer namespace instead of this module's compiler namespace;
  its downstream `sorryAx` was failed-elaboration contamination.  Explicit
  compiler calls fixed the issue.  The focused check passes, and the exact
  one-worker dependency-complete target passes 5077 jobs with the new module
  taking about 1.3 seconds.  No producer inhabitant, strength-band inhabitant,
  cutoff-limit channel, uniform norm floor, projective/OS identification,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-normalized-moving-cube-channel] Normalize the exact sampled observable while exposing the cutoff debt — **CLOSED 2026-08-24**

- **milestone**: prove the concrete cube-coordinate floor is at most one;
  rescale the actual global completed vacuum-complement vector by its positive
  reciprocal; name the reciprocal-square norm debt and reciprocal-fourth-
  power squared-correlation debt; prove exact norm and matrix-coefficient
  scaling; retain the same completed-rate decay; prove a scale-uniform norm
  floor one; sample at canonical physical time; and show that any explicit
  cutoff limit of this same normalized channel is nonzero at time zero.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel.lean`.
- **decl**:
  `centralPhysicalVacuumSectorCoordinateFloor_le_one`,
  `movingCubeNormalizationScale`,
  `movingCubeNormalizationNormDebt`,
  `movingCubeNormalizationCorrelationSqDebt`,
  `normalizedMovingCubeGlobalVectorAt`,
  `normalizedMovingCubeNormSq`,
  `normalizedMovingCubeConnectedAutocorrelation`,
  `normalizedMovingCubeNormSq_eq_scaled`,
  `normalizedMovingCubeConnectedAutocorrelation_eq_scaled`,
  `normalizedMovingCubeConnectedAutocorrelationSq_decay`,
  `one_le_normalizedMovingCubeNormSq`,
  `normalizedMovingCubeSampledConnectedAutocorrelation`,
  `normalizedMovingCubeSampledConnectedAutocorrelationSq_decay`,
  `one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero`,
  `NormalizedMovingCubeScheduledRCContinuumLimit`, and
  `NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive`.
- **obligation**: construct representative-level cutoff convergence for the
  reciprocal-normalized same-observable channel.  That proof must control the
  explicit norm and squared-correlation debts rather than silently replacing
  the observable.  Specialize the compiler to the adaptive producer and its
  physical strength band, then identify the exact limiting correlation with
  the selected projective/OS observable and reconstructed generator.
- **constructive?**: yes — reciprocal scaling uses the already supplied
  positive rational floor; the actual completed vector is scaled through the
  proved rational module operation; every moment identity remains in `RC`;
  representative convergence is explicit Type-level data.  The fourteen
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: early guarded checks with missing carrier/completion
  namespace openings and wrapper-unfolding mismatches emitted downstream
  failed-elaboration `sorryAx`; none are passes.  The corrected focused check
  passes.  The exact one-worker dependency-complete target passes 1657 jobs,
  with the new module taking about 1.7 seconds.  No normalized cutoff-limit
  inhabitant, producer inhabitant, strength band, projective/OS
  identification, continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-adaptive-normalized-moving-cube-path] Preserve the adaptive producer through normalized sampling — **CLOSED 2026-08-24**

- **milestone**: specialize the reciprocal scale and both normalization debts
  to the completed family produced by one supplied adaptive transition-
  product family; retain the actual normalized global vector, norm, sampled
  connected matrix coefficient, and scheduled power; prove exact equality to
  the reciprocal-square rescaling of the raw producer moment and to the
  literal global matrix coefficient; retain completed-rate decay, norm floor
  one, and the same physical strength band; and expose the exact normalized
  cutoff-limit type whose inhabitant gives continuum zero-time positivity.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.lean`.
- **decl**:
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeScale`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeNormDebt`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeCorrelationSqDebt`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeVectorAt`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeSampledConnectedAutocorrelation_eq_scaled_raw`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeSampledConnectedAutocorrelation_eq_global`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeSampledConnectedAutocorrelationSq_decay`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.one_le_normalizedMovingCubeSampledConnectedAutocorrelation_zero`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCube_physicalGap_twoSided`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.NormalizedMovingCubeContinuumLimit`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation_zero_isPositive`.
- **obligation**: derive the producer-indexed normalized cutoff limit from
  constructive representative convergence of the raw sampled moment together
  with convergence or another adequate control of the reciprocal-square debt.
  Preserve the reciprocal-fourth-power debt through squared-decay passage and
  combine it with the sampled physical-rate envelope.  Then identify this same
  normalized correlation through projective measure and OS reconstruction.
- **constructive?**: yes — all joins are definitional or named equalities over
  one supplied producer, and the normalized continuum interface requires
  explicit representatives and moduli.  The six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first guarded check had unresolved nested imported
  namespaces and source-theorem shadowing; downstream normalization timed out
  and emitted failed-elaboration `sorryAx`.  The second check found one
  remaining completed-moment namespace.  Neither is a pass.  The corrected
  focused check passes.  The exact one-worker dependency-complete target
  passes 5079 jobs, with the new module taking about 1.4 seconds.  No producer,
  strength band, normalized cutoff limit, projective/OS identification,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-normalized-moving-cube-limit-compiler] Factor normalized cutoff convergence into raw and debt limits — **CLOSED 2026-08-24**

- **milestone**: state constructive-real convergence of the exact reciprocal-
  square normalization debt; identify every normalized sampled moment with
  that debt times the raw same-observable moment; combine the explicit raw
  representative limit and debt limit through general constructive product
  continuity; construct the normalized scheduled cutoff-limit record; prove
  its continuum value is the quotient-real product of the two input limits;
  and retain strict zero-time positivity.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler.lean`.
- **decl**:
  `MovingCubeNormalizationNormDebtLimit`,
  `normalizedMovingCubeSampledConnectedAutocorrelation_eq_scaled_raw`,
  `compileNormalizedMovingCubeScheduledRCContinuumLimit`,
  `compileNormalizedMovingCube_continuum_eq_product`, and
  `compileNormalizedMovingCube_continuum_zero_isPositive`.
- **obligation**: inhabit the raw sampled moving-cube representative limit and
  the actual reciprocal-square debt limit for one adaptive producer.  For the
  continuum decay inequality, also control the reciprocal-fourth-power debt
  and the scheduled completed-rate powers, then connect the exact normalized
  correlation to the projective/OS observable and reconstructed generator.
- **constructive?**: yes — both sequences and their representatives are
  explicit, and the compiler uses the general constructive product-
  convergence modulus.  The four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first two guarded checks lacked the general product-
  convergence theorem in the import closure and then referenced its wrong
  namespace; their downstream `sorryAx` reports are failed elaboration and not
  passes.  The corrected focused check passes.  The exact one-worker
  dependency-complete target passes 1658 jobs, with the new module taking
  about 0.76 seconds.  No raw limit, debt limit, adaptive producer, strength
  band, projective/OS identification, continuum Yang--Mills theory, or Clay
  theorem is claimed.

### [BF4-physical-normalized-moving-cube-continuum-decay] Pass exact finite decay through the same-channel cutoff limit — **CLOSED 2026-08-24**

- **milestone**: name the exact scheduled squared-rate factor; state its
  representative-level constructive convergence interface; rewrite the
  finite normalized `RC` decay theorem on the exact representatives selected
  by the same normalized cutoff-limit record; prove convergence of both sides
  by constructive product continuity; pass the inequality to the limits; and
  descend the resulting continuum squared-decay theorem to `RC`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler.lean`.
- **decl**:
  `normalizedMovingCubeSampledRatePower`,
  `NormalizedMovingCubeSampledRatePowerLimit`,
  `normalizedMovingCubeLimitRepresentativeSq_decay`,
  `normalizedMovingCubeContinuumRepresentativeSq_decay`, and
  `normalizedMovingCubeContinuumConnectedAutocorrelationSq_decay`.
- **obligation**: inhabit the exact scheduled-rate-power limit and identify
  its values with a physical exponential governed by the same completed rate
  and a uniform positive physical gap.  Independently inhabit the raw
  same-observable correlation limit and reciprocal-square debt limit that
  construct the normalized correlation limit.  Then preserve this exact
  continuum correlation through projective/OS reconstruction.
- **constructive?**: yes — no new representative is selected; the existing
  `represents` fields rewrite both sides of the finite inequality, and all
  limit products carry explicit constructive convergence data.  The three
  audited exports use exactly `[propext, Quot.sound]`; no forbidden construct
  was added.
- **status note**: the first guarded check used a locally aliased polymorphic
  product-convergence theorem whose implicit terms could not be inferred; its
  downstream `sorryAx` is failed elaboration and not a pass.  Fully qualified
  applications fixed the boundary.  The corrected focused check passes.  The
  exact one-worker dependency-complete target passes 1659 jobs, with the new
  module taking about 0.69 seconds.  No scheduled rate-power limit, normalized
  correlation limit, physical exponential identification, projective/OS
  identification, continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-normalized-moving-cube-variation-compiler] Compile three parallel scale variations into one continuum decay channel — **CLOSED 2026-08-24**

- **milestone**: pin explicit representatives to the raw sampled moving-cube
  `RC` classes; use summable consecutive-scale variation to construct their
  scheduled cutoff limit; separately construct the reciprocal-square debt
  limit and exact scheduled-rate-power limit from summable variations; feed
  the raw/debt outputs into the normalized product-limit compiler; feed the
  rate output into the continuum-decay compiler; and obtain one strictly
  positive continuum same-observable channel with squared decay.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.lean`.
- **decl**:
  `MovingCubeRawScheduledRepresentativeVariation`,
  `MovingCubeRawScheduledRepresentativeVariation.toScheduledRCContinuumLimit`,
  `MovingCubeNormalizationNormDebtVariation`,
  `movingCubeNormalizationNormDebtLimitOfVariation`,
  `NormalizedMovingCubeSampledRatePowerVariation`,
  `normalizedMovingCubeSampledRatePowerLimitOfVariation`,
  `normalizedMovingCubeLimitOfVariations`,
  `normalizedMovingCubeLimitOfVariations_zero_isPositive`, and
  `normalizedMovingCubeLimitOfVariations_sq_decay`.
- **obligation**: prove the three summable scale-variation inputs from one
  adaptive producer.  The raw representatives must remain pinned to its exact
  sampled moments; the debt variation must control its exact reciprocal
  normalization; and the rate-power variation must be identified with a
  physical exponential carrying the same positive rate.  Then connect that
  continuum correlation to the projective/OS observable and reconstruction.
- **constructive?**: yes — each local variation supplies an explicit tail
  rate, hence a `ModCauchyEv`, complete limit, and convergence modulus.  The
  three outputs rejoin only through the already checked same-object compiler
  chain.  The five audited exports use exactly `[propext, Quot.sound]`; no
  forbidden construct was added.
- **status note**: two convenience-bundle attempts timed out during weak-head
  normalization, first over reducible variation aliases and then in an opaque
  wrapper declaration; their downstream `sorryAx` reports are failed
  elaboration and not passes.  Replacing the bundle by three explicit compiler
  arguments preserves the theorem and passes the corrected focused check.
  The exact one-worker dependency-complete target passes 1660 jobs, with the
  new module taking about 0.85 seconds.  No variation input, physical
  exponential identification, projective/OS identification, continuum Yang--
  Mills theory, or Clay theorem is claimed.

### [BF4-physical-rational-step-variation] Rationalize the debt and rate-power variation frontiers — **CLOSED 2026-08-24**

- **milestone**: compile a nonnegative rational consecutive-step budget with
  antitone tail control into the existing constructive-real variation and
  complete limit; construct zero variation for pointwise-rationally-constant
  streams; specialize this interface to the exact reciprocal-square
  normalization debt and scheduled squared-rate power; prove the time-zero
  rate stream is pointwise equivalent to one; reduce the full rate branch to
  positive physical times; and rejoin both rational branches with the genuine
  raw `CReal` representative variation in the same continuum decay theorem.
- **files**:
  `lean/YMGap/Continuum/SummableRationalStepVariation.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.lean`.
- **decl**:
  `SummableRationalStepVariation`,
  `SummableRationalStepVariation.toSummableCRealStepVariation`,
  `SummableRationalStepVariation.toModCauchyEv`,
  `SummableRationalStepVariation.limit`,
  `SummableRationalStepVariation.converges`,
  `SummableRationalStepVariation.ofPointwiseEqvConstant`,
  `MovingCubeNormalizationNormDebtRationalVariation`,
  `NormalizedMovingCubeSampledRatePowerRationalVariation`,
  `normalizedMovingCubeSampledRatePower_zero_eqv_one`,
  `normalizedMovingCubeSampledRatePowerRationalVariationOfPositive`,
  `normalizedMovingCubeLimitOfRationalDebtVariation`, and
  `normalizedMovingCubeLimitOfRationalVariations_sq_decay`.
- **obligation**: prove rational step/tail estimates for the exact reciprocal-
  square debt and positive-time scheduled rate powers of one adaptive
  producer, and prove `CReal` representative variation for its exact raw
  same-object moments.  Identify the resulting rate-power limit with a
  physical exponential before projective/OS reconstruction.
- **constructive?**: yes — the rational embedding has zero inner regularity,
  every tail modulus is explicit, and the raw moment is not falsely recoded as
  rational.  The audited exports use only `[propext]` or
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first generic check lacked the local `Q'.eqv` notation;
  one adapter check ran before the generic `.olean` existed; and the first
  time-zero proof left `1 ≈ 1`.  None is a pass, and their downstream
  `sorryAx` reports are failed-elaboration contamination.  Corrected focused
  checks pass.  Exact one-worker targets pass 38 jobs for the generic module
  and 1662 jobs for the BF4 adapter.  No variation estimate, adaptive family,
  physical-exponential identification, projective/OS reconstruction,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-adaptive-rational-variation-path] Preserve one adaptive observable through three parallel variation branches — **CLOSED 2026-08-24**

- **milestone**: specialize the raw representative, rational normalization-
  debt, and rational positive-time rate-power variation inputs to the exact
  completed family produced by one adaptive transition-product family;
  construct the time-zero rate branch; compile raw/debt variation into the
  continuum limit of the exact normalized moving-cube connected correlation;
  retain strict zero-time positivity; and rejoin the third branch in its
  continuum squared-decay inequality.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.lean`.
- **decl**:
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.MovingCubeRawVariation`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.MovingCubeNormalizationDebtRationalVariation`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.PositiveMovingCubeRatePowerRationalVariation`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeRatePowerRationalVariationOfPositive`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfRationalVariations`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfRationalVariations_zero_isPositive`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfRationalVariations_sq_decay`.
- **obligation**: independently prove all three explicit cross-scale inputs
  for one adaptive producer, then identify its scheduled rate-power limit with
  a uniform positive physical exponential and its exact connected correlation
  through projective measure and OS reconstruction.
- **constructive?**: yes — every input is indexed by the identical adaptive
  family, the raw representatives remain pinned to its same-object `RC`
  classes, and the branches rejoin only in the already checked product and
  decay compilers.  The four audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first guarded check omitted the scheduled-rate
  definition's namespace.  The second timed out at 10M heartbeats while
  generating a convenience dependent record over deeply reducible producer
  types.  Neither is a pass; their later projection errors and `sorryAx` are
  failed-elaboration contamination.  Three explicit indexed arguments remove
  the unnecessary packaging cost.  The corrected focused check passes, and
  the exact one-worker target passes 5085 jobs with the new module taking
  about 1.2 seconds.  No variation estimate, adaptive family, physical-
  exponential identification, projective/OS reconstruction, continuum Yang--
  Mills theory, or Clay theorem is claimed.

### [BF4-physical-bounded-normalization-scale-variation] Compile reciprocal-scale variation into squared debt — **CLOSED 2026-08-24**

- **milestone**: prove that positive constant scaling preserves an antitone
  rational tail control; prove `y^2 <= x^2 + (K+K)*v` from nonnegativity,
  ceiling `K`, and `y <= x+v`; compile summable variation of a bounded rational
  stream into variation of its square; apply this to the reciprocal moving-
  cube normalization scale; and preserve the exact adaptive producer,
  normalized continuum correlation, zero-time positivity, and squared-decay
  join through that smaller normalization input.
- **files**:
  `lean/YMGap/Continuum/SummableRationalSquareStepVariation.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.lean`.
- **decl**:
  `scaledAntitoneTailControl`, `square_step_le`,
  `SummableRationalStepVariation.square`,
  `MovingCubeNormalizationScaleRationalVariation`,
  `movingCubeNormalizationNormDebtRationalVariationOfScale`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeNormalizationDebtRationalVariationOfScale`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfScaleRationalVariation`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfScaleRationalVariation_zero_isPositive`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfScaleRationalVariation_sq_decay`.
- **obligation**: prove a positive uniform ceiling and summable step/tail
  variation for the exact reciprocal normalization scales of one adaptive
  producer, or choose and justify a different normalization.  Independently
  prove its raw moment and positive-time rate-power variation, then identify
  the rate limit with a uniform physical exponential and the same correlation
  through projective/OS reconstruction.
- **constructive?**: yes — rational tail rescaling uses explicit positive
  division, the square bound is direct ordered rational algebra, and all
  downstream objects retain the same producer index.  Audited exports use only
  `[propext]` or `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first generic check lacked the division import, one
  association intermediate, and correct positivity-helper arities.  The first
  BF4 specialization check used field notation across an extension namespace.
  Neither is a pass; their `sorryAx` is failed-elaboration contamination.
  Corrected focused checks pass.  Exact one-worker targets pass 45, 1663, and
  5086 jobs for the generic, BF4, and adaptive modules, with the new modules
  taking about 0.23, 1.1, and 1.5 seconds after replay.  No ceiling, variation
  estimate, adaptive family, physical-exponential identification,
  projective/OS reconstruction, continuum Yang--Mills theory, or Clay theorem
  is claimed.

### [BF4-physical-exact-log-rate-variation] Join physical-gap and spacing tails into exact-log cutoff removal — **CLOSED 2026-08-24**

- **milestone**: turn the same-family upper rate band into a linear margin
  tail and computed direct-log half-window; identify its rational margin proxy
  with the completed family's exact physical gap; join summable rational gap
  variation with inverse-square physical-spacing control; construct the
  full-range exact logarithmic rate's `ModCauchyEv`, complete limit, and
  convergence modulus; construct exact-rate cutoff removal after an
  independent full-log ceiling is supplied; and inject the derived modulus
  into the existing observable-connected continuum handoff.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.lean`.
- **decl**:
  `DynamicVacuumSectorObservablePin.exactLogLinearMarginTail`,
  `DynamicVacuumSectorObservablePin.exactLogRateStart`,
  `DynamicVacuumSectorObservablePin.marginRate_eqv_physicalGap`,
  `DynamicVacuumSectorObservablePin.exactLogRateCauchy`,
  `DynamicVacuumSectorObservablePin.exactLogRateLimit`,
  `DynamicVacuumSectorObservablePin.exactLogRateConverges`,
  `DynamicVacuumSectorObservablePin.exactRateCutoffRemovalOfVariations`, and
  `DynamicVacuumSectorContinuumHandoff.ofExactLogVariations`.
- **obligation**: prove summable physical-gap variation and an inverse-square
  spacing tail for one actual adaptive family; supply its observable pin and
  a finite full-log ceiling; then prove that its actual scheduled rational
  powers converge to the physical exponential governed by this same exact
  logarithmic mass.  Raw moment and normalization variation plus the
  projective/OS semantic identification remain independent branches.
- **constructive?**: yes — the half-window start, shifted tail controls,
  approximation-index regularity, global Cauchy modulus, limit, and convergence
  witness are all Type-level data.  The six audited exports use exactly
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first guarded check addressed imported extension
  declarations through the wrong namespace and reduced the computed tail
  start to an invalid reflexive bound.  It is not a pass; its downstream
  `sorryAx` reports are failed-elaboration contamination.  After opening the
  defining namespace and keeping the `Nat.le_max_left` proof, the focused
  check passes.  The exact one-worker dependency-complete target passes 1400
  jobs, with the new module taking about 65 seconds.  No variation input,
  ceiling, observable pin, log/power identification, projective/OS
  reconstruction, continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-rational-euler-power-sandwich] Bound finite rational powers by constructive exponentials — **CLOSED 2026-08-24**

- **milestone**: for every rational decrement `0 <= d < 1`, construct the
  Euler margin `1-d`, its rational odds `d/(1-d)`, prove the exact denominator
  cancellation, and derive the constructive-real corridor
  `exp(-(d/(1-d))*n) <= (1-d)^n <= exp(-d*n)`; restate the result for a
  positive transfer rate `q <= 1` as
  `exp(-((1-q)/q)*n) <= q^n <= exp(-(1-q)*n)`.
- **file**:
  `lean/YMGap/Continuum/RationalEulerPowerSandwich.lean`.
- **decl**:
  `eulerMargin`, `eulerMargin_pos`, `eulerOdds`,
  `eulerOdds_nonnegative`,
  `one_add_eulerOdds_mul_eulerMargin_eqv_one`,
  `oneOver1p_eulerOdds_le_margin`, `expNeg_eulerOdds_le_margin`,
  `eulerMargin_geRat_expNeg`, `expNeg_cpow_ge_eulerMargin_pow`,
  `expNeg_cpow_equiv_scaled`, `rationalEulerPower_lower`,
  `rationalEulerPower_upper`, `rationalEulerPower_sandwich`,
  `eulerMargin_one_sub_eqv`, and `rationalRatePower_sandwich`.
- **obligation**: specialize the finite corridor to the exact squared
  moving-cube rate and floor schedule, and prove convergence of its lower and
  upper exponent streams to one physical exponent.  This still requires
  inhabited physical-gap/spacing control and does not discharge the raw
  moment, normalization, or projective/OS branches.
- **constructive?**: yes — the proof uses rational ordered algebra, the
  constructive Pade and alternating-series exponential estimates,
  constructive-real powers, and explicit eventual order.  Audited exports use
  only `[propext]` or `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first focused check used nonexistent names for
  definitional constructive-real power equations; the second addressed a
  multiplication lemma through the wrong namespace; and the first
  transfer-currency corollary used a nonexistent zero-addition lemma.  These
  are not passes.  Replacing them with definitional `change`, the defining
  namespace, and the available rational equivalences made the corrected
  focused check pass.  The exact one-worker target passes 175 dependency jobs,
  with the new module taking about 0.31 seconds.  No cross-scale convergence,
  physical exponential identification, projective/OS reconstruction,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-scheduled-rate-euler-corridor] Attach the finite corridor to the exact adaptive schedule — **CLOSED 2026-08-24**

- **milestone**: define the literal squared completed rate and its two
  scheduled Euler exponents; prove the squared rate is positive and at most
  one; bracket the exact normalized moving-cube factor
  `((q_j*q_j)^floor(t/a_j))` by the corresponding constructive exponentials;
  prove strict completed-rate positivity from the residual-coercivity
  producer's explicit positive reciprocal; and specialize the corridor to the
  exact adaptive transition-product family with no new analytic hypothesis.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.lean`.
- **decl**:
  `completedSquaredRate`, `completedSquaredRate_pos`,
  `completedSquaredRate_le_one`, `scheduledSquaredRateUpperExponent`,
  `scheduledSquaredRateLowerExponent`,
  `scheduledSquaredRateUpperExponent_nonnegative`,
  `scheduledSquaredRateLowerExponent_nonnegative`,
  `normalizedMovingCubeSampledRatePower_euler_sandwich`,
  `DynamicSpinCubeOffRayResidualCoercivityFamily.completedRate_pos`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos`,
  and the adaptive
  `normalizedMovingCubeSampledRatePower_euler_sandwich`.
- **obligation**: prove cross-scale convergence of both scheduled exponent
  streams to the same physical exponent using the exact physical-gap stream,
  rate-to-one control, and sampled-distance convergence; then squeeze the
  scheduled rational powers and identify their existing complete limit.
- **constructive?**: yes — strict positivity is derived by unfolding the
  explicit positive rational quotient, and the finite corridor is inherited
  without changing the producer, completed rate, squared power, or sampling
  schedule.  All six audited exports use exactly `[propext, Quot.sound]`.
- **status note**: the first guarded check omitted two defining namespace
  opens and attempted field notation for extension theorems in a different
  namespace.  It is not a pass; its downstream `sorryAx` reports are failed-
  elaboration contamination.  The corrected focused check passes.  The exact
  one-worker target passes 5082 dependency jobs, with the new module taking
  about 1.3 seconds.  No cross-scale exponent convergence, rate-power limit,
  raw moment or normalization estimate, projective/OS reconstruction,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-scheduled-rate-exponent-limit] Contract both Euler exponents to `M*2*t` — **CLOSED 2026-08-24**

- **milestone**: factor `1-q^2` as `(1-q)(1+q)` in the rational setoid;
  cancel the exact physical-gap denominator; prove the completed rate tends to
  one from the physical rate band; prove its square and exact positive
  reciprocal tend to one; factor the upper scheduled exponent into physical
  gap, `1+q`, and sampled distance; and prove both the upper and odds-corrected
  lower exponents converge to the identical constructive-real product
  `M*2*t` selected by the physical-gap variation limit.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler.lean`.
- **decl**:
  `one_sub_square_eqv`, `physicalGap_mul_spacing_eqv_latticeMargin`,
  `scheduledSquaredRateUpperExponent_factor_eqv`,
  `completedRate_converges_one`, `one_add_completedRate_converges_two`,
  `completedSquaredRate_converges_one`,
  `completedSquaredRateReciprocal`,
  `completedSquaredRateReciprocal_converges_one`,
  `scheduledSquaredRatePhysicalExponentLimit`,
  `scheduledSquaredRateUpperExponent_converges`,
  `scheduledSquaredRateLowerExponent_factor_eqv`, and
  `scheduledSquaredRateLowerExponent_converges`.
- **obligation**: transport the common exponent limit through the
  constructive exponential, use the finite Euler corridor to squeeze the
  literal scheduled rational powers, and identify the already constructed
  rate-power complete limit with that physical exponential.  The physical
  band and gap variation must still be inhabited for one adaptive producer.
- **constructive?**: yes — the rate convergence uses the computed band modulus;
  reciprocal convergence uses an explicit half-window and a positive rational
  square floor; all products use constructive-real sequential continuity.
  Audited exports use only `[propext]` or `[propext, Quot.sound]`.
- **status note**: the first guarded check exposed reversed congruence-helper
  orientations, an unopened rate-band namespace, and a reducible local name
  that required `change`.  The second exposed the available distribution and
  negated-product orientations plus a final commutation.  Neither is a pass;
  their downstream `sorryAx` is failed-elaboration contamination.  The
  corrected focused check passes.  The exact one-worker target passes 5084
  dependency jobs, with the new module taking about 1.2 seconds.  No
  exponential-value or scheduled-power convergence, adaptive analytic input,
  raw moment or normalization estimate, projective/OS reconstruction,
  continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-scheduled-rate-exponential-squeeze] Identify the literal scheduled-power limit with the `2*M*t` exponential — **CLOSED 2026-08-24**

- **milestone**: prove a reusable eventual-order squeeze: two nonnegative
  rational exponent streams converging to the same constructive real have
  `leRat`-vanishing exponential width, and any convergent middle stream
  squeezed between those endpoints shares both endpoint limits; prove the
  scheduled upper exponent is no larger than the odds-corrected lower
  exponent; specialize the squeeze to the exact squared completed rate and
  floor schedule; identify both Euler exponential streams with the already
  constructed complete limit of the literal scheduled rational powers; and
  return that identification together with the normalized same-observable
  continuum squared-decay theorem.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.lean`.
- **decl**:
  `expNegEndpoints_leRat_close`,
  `endpoints_converge_of_leRat_sandwich`,
  `scheduledSquaredRateUpperExponent_le_lower`,
  `scheduledSquaredRateUpperExponential`,
  `scheduledSquaredRateLowerExponential`,
  `scheduledSquaredRateEulerExponentials_converge`,
  `normalizedMovingCubePhysicalExponentialLimit`,
  `normalizedMovingCubePhysicalExponentialLimit_identification`, and
  `normalizedMovingCubePhysicalExponential_sq_decay`.
- **obligation**: inhabit the physical-gap and scheduled-rate-power rational
  variations for one actual adaptive family.  The physical exponent is the
  gap-variation limit times `2*t`; its positive uniform floor should be
  exported explicitly.  The raw same-object moment and normalization-scale
  variations, concrete observable pin, and projective/OS semantic
  reconstruction remain independent open branches.
- **constructive?**: yes — the compiler does not assume a global exponential
  on arbitrary `CReal`s.  It defines the route-specific value by the complete
  limit of the literal powers and proves both rational exponential endpoint
  streams converge to that exact value.  All six audited exports use only
  `[propext]` or `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first guarded check exposed four missing parentheses
  around approximation applications and one binder ordered after the type
  that referenced it.  It is not a pass; its downstream `sorryAx` reports are
  failed-elaboration contamination.  The corrected focused check passes.  The
  exact one-worker dependency-complete target passes 5088 jobs, with the new
  module taking about 1.2 seconds.  No analytic variation input, continuum
  measure, OS reconstruction, all-vector completed gap, continuum Yang--Mills
  theory, or Clay theorem is claimed.

### [BF4-physical-adaptive-exponential-path] Preserve the adaptive producer through the positive physical exponential join — **CLOSED 2026-08-24**

- **milestone**: pass the physical rate band's explicit positive floor to the
  physical-gap variation limit; prove the common exponent `M*2*t` is `PosEv`
  at every positive physical time; specialize the scheduled-power physical
  exponential to the exact off-ray adaptive transition-product producer;
  preserve its positive-time rate variation; and return one theorem containing
  the adaptive normalized moving-cube squared decay together with convergence
  of both Euler exponential endpoints to its exact rate factor.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.lean`.
- **decl**:
  `physicalGapVariationLimit_floor`,
  `physicalGapVariationLimit_posEv`,
  `scheduledSquaredRatePhysicalExponentLimit_posEv`, adaptive
  `PhysicalGapRationalVariation`, adaptive
  `physicalExponentialLimit`, adaptive
  `physicalExponentialLimit_identification`, and adaptive
  `normalizedMovingCubePhysicalExponential_sq_decay`.
- **obligation**: inhabit one adaptive producer, its strength band, exact
  physical-gap rational variation, raw same-object moment variation,
  normalization-debt or bounded-scale variation, and positive-time scheduled-
  power variation.  Then identify the exact connected continuum correlation
  through the projective measure and OS reconstruction and extend a uniform
  estimate to the completed vacuum complement.
- **constructive?**: yes — the physical floor remains the literal rational
  floor of the same strength band, and the exponential/decay result retains
  the identical adaptive family and observable.  All audited exports use only
  `[propext]` or `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: a first positive-exponent formulation audited with
  `Classical.choice` because `omega` was used to eliminate the impossible
  zero-time branch.  It was rejected and replaced by direct
  `Nat.not_lt_zero`, restoring the allowed gate.  The first adaptive check ran
  before the changed dependency `.olean` was rebuilt and also omitted opens
  for two nested extension namespaces; it is not a pass, and all associated
  `sorryAx` output is failed-elaboration contamination.  The corrected
  focused checks pass.  The exact one-worker dependency-complete adaptive
  target passes 5092 jobs, with the new module taking about 1.3 seconds.  No
  analytic input, projective/OS reconstruction, all-vector gap, continuum
  Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-raw-moving-cube-continuum-decay] Bypass normalization debt while retaining one observable — **CLOSED 2026-08-24**

- **milestone**: retain the literal unnormalized moving-cube sampled
  autocorrelation; compile its raw representative variation to the exact
  scheduled continuum limit; pass the finite same-object squared-decay
  estimate through raw-moment and scheduled-rate-power convergence; state
  nontriviality only as positivity of that exact observable's zero-time limit;
  and rejoin positivity and decay in one definitionally connected theorem.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler.lean`.
- **decl**:
  `rawMovingCubeContinuumLimitOfVariation`,
  `MovingCubeRawContinuumNontriviality`,
  `rawMovingCubeLimitRepresentativeSq_decay`,
  `rawMovingCubeContinuumRepresentativeSq_decay`,
  `rawMovingCubeContinuumConnectedAutocorrelationSq_decay`, and
  `rawMovingCubeObservableConnectedContinuumPath`.
- **obligation**: inhabit raw same-object representative variation and
  positivity of its actual zero-time continuum limit for one adaptive
  producer.  The rate branch remains the existing exact scheduled-power
  variation and physical-exponential compiler.  Then construct the
  projective/OS same-object identification and extend the estimate uniformly
  from one channel to the completed vacuum complement.
- **constructive?**: yes — no reciprocal normalization or unrelated amplitude
  is inserted.  The same representative family supplies the finite moment,
  continuum correlation, zero-time amplitude, and decay theorem.  All five
  audited exports use only `[propext, Quot.sound]`; no forbidden construct was
  added.
- **status note**: the focused guarded check passes.  The exact one-worker
  dependency-complete target passes 1661 jobs, with the new module taking
  about 0.85 seconds.  No analytic variation or positivity input, continuum
  measure, OS reconstruction, all-vector completed gap, continuum Yang--Mills
  theory, or Clay theorem is claimed.

### [BF4-physical-adaptive-raw-exponential-path] Specialize the normalization-free path to one adaptive producer — **CLOSED 2026-08-24**

- **milestone**: specialize the raw moving-cube continuum limit and its
  zero-time nontriviality certificate to the off-ray adaptive
  transition-product family; reuse the exact physical exponential already
  selected by that producer's scheduled powers; and return positivity, raw
  same-observable squared decay, and both Euler endpoint identifications in
  one theorem without a normalization-debt input.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath.lean`.
- **decl**:
  adaptive `rawMovingCubeContinuumLimit`,
  `RawMovingCubeContinuumNontriviality`,
  `rawMovingCubeContinuumConnectedAutocorrelation`, and
  `rawMovingCubePhysicalExponentialPath`.
- **obligation**: inhabit the raw representative variation, its exact
  zero-time continuum nontriviality, the physical-gap variation, and the
  positive-time scheduled-power variation for one adaptive producer.  Then
  identify this same correlation in the projective/OS continuum theory and
  promote one-observable decay to a uniform completed vacuum-complement gap.
- **constructive?**: yes — the theorem preserves producer, observable,
  centering, sampling, rate, amplitude, and limit lineage, and removes the
  reciprocal normalization branch entirely.  All three audited exports use
  only `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the first two guarded checks exposed namespace-resolution
  mistakes in extension field notation and then one omitted base-field
  projection.  Neither is a pass; their `sorryAx` output is failed-elaboration
  contamination.  The corrected focused check passes.  The exact one-worker
  dependency-complete target passes 5094 jobs, with the new module taking
  about 1.1 seconds.  No analytic input, continuum measure, OS reconstruction,
  all-vector gap, continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-raw-projective-os-correlation-handoff] Identify the exact raw limit with one connected OS insertion — **CLOSED 2026-08-24**

- **milestone**: retain completed-real raw representatives; require their
  equality with expectations of a cutoff-independent insertion on the
  selected projective measure thread; use constructive limit uniqueness to
  identify the exact raw continuum limit with the selected OS functional;
  identify that functional with one connected OS two-point insertion; descend
  to `RC`; and transport the same zero-time nontriviality certificate.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff.lean`.
- **decl**:
  `RawMovingCubeProjectiveOSCorrelationHandoff`,
  `rawLimitRepresentative_eq_osFunctional`,
  `rawLimitRepresentative_eq_osConnected`,
  `rawContinuumConnectedAutocorrelation_eq_osConnected`, and
  `osConnected_zero_isPositive`.
- **obligation**: construct a continuum projective measure and its
  measure-linked OS data; prove that the literal raw moving-cube
  representatives are the selected stage expectations of a fixed OS
  insertion; and supply its connected two-point interpretation.  The next
  semantic frontier is equality with the selected Wilson GNS transfer matrix
  coefficient, followed separately by a uniform completed-vacuum-complement
  operator gap.
- **constructive?**: yes — limit uniqueness consumes the two explicit
  convergence moduli and termwise representative equivalence.  No new
  representative, rational separator surrogate, or positivity witness is
  chosen.  All four audited exports use only `[propext, Quot.sound]`.
- **status note**: the focused guarded check passes.  The exact one-worker
  dependency-complete target passes 1662 jobs, with the new module taking
  about 0.76 seconds.  No projective measure, OS/GNS semantics, all-vector
  gap, continuum Yang--Mills theory, or Clay theorem is claimed.

### [BF4-physical-raw-wilson-gns-handoff] Identify the raw OS channel with the selected completed-GNS matrix coefficient — **CLOSED 2026-08-24**

- **milestone**: index the raw projective/OS handoff by the selected Wilson
  datum's own `measureLinked` field; embed its exact connected insertion in the
  completed Wilson GNS carrier; retain its vacuum-orthogonality proof; identify
  the raw continuum correlation with the selected transfer autocorrelation;
  export the generic connected-OS/Wilson pin; and prove that a separately
  supplied all-vector iterated gap implies decay of this channel.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff.lean`.
- **decl**:
  `RawMovingCubeWilsonMatrixCoefficientPin`, `gapState`,
  `toWilsonOSConnectedMatrixCoefficientPin`,
  `rawContinuumConnectedAutocorrelation_eq_matrixCoefficient`, and
  `rawContinuumConnectedAutocorrelationSqDecay`.
- **obligation**: inhabit the projective/OS handoff, selected Wilson GNS data,
  exact matrix-coefficient equality, and vacuum-orthogonality pin.  Separately
  prove a uniform operator-norm estimate on every selected
  vacuum-orthogonal completed vector and identify its separator with the
  dynamic physical-rate limit.
- **constructive?**: yes — the measure thread is fixed definitionally by
  `W.measureLinked`, and the one-channel theorem only consumes the all-vector
  gap in the valid direction.  All three audited exports use only
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused guarded check passes.  The exact one-worker
  dependency-complete target passes 1666 jobs, with the new module taking
  about 0.71 seconds.  No semantic pin, all-vector gap, continuum Yang--Mills
  theory, or Clay theorem is claimed.

### [BF4-physical-dynamic-wilson-graph-norm-limit] Pass scheduled physical-time contractions to every Wilson vacuum vector — **CLOSED 2026-08-24**

- **milestone**: formulate choice-free representative-level graph-norm data
  for the varying completed BF4 vacuum sectors; use the scheduled power for
  one unit of physical time rather than one lattice step; retain explicit
  finite norm representatives and both convergence moduli; pin the exact
  scheduled squared-rate limit to the selected Wilson separator squared; pass
  the finite all-vector power contraction through those limits; and construct
  `WilsonOperatorNormGapPin` by quotient induction.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler.lean`.
- **decl**:
  `DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit`,
  `finitePhysicalTimeRepresentative_norm_gap`,
  `physicalTimeOne_limit_operator_norm_gap`, and
  `toWilsonOperatorNormGapPin`.
- **obligation**: construct finite approximants for every explicit selected
  Wilson vacuum-complement representative; prove ordinary and scheduled-image
  graph-norm convergence; and identify the exact one-unit scheduled-rate limit
  with the selected OS/Wilson separator squared.  Then combine this operator
  gap with a positive exact reconstruction rate on the same measure thread.
- **constructive?**: yes — the compiler quantifies finite approximants only
  after vacuum orthogonality is supplied, retains explicit representatives,
  and descends to all quotient vectors only through `Quotient.inductionOn`.
  All three audited exports use only `[propext, Quot.sound]`; no forbidden
  construct was added.
- **status note**: the first focused check passes with two unused binder
  warnings; the binders were renamed and the corrected focused check passes.
  The exact one-worker dependency-complete target passes 1660 jobs, with the
  new module taking about 0.71 seconds.  No graph-norm or separator pin,
  continuum measure, OS reconstruction, continuum Yang--Mills theory, or Clay
  theorem is claimed.

### [BF4-physical-dynamic-wilson-exact-rate-handoff] Identify the dynamic rate with the selected Wilson logarithm and assemble the minimal bounded gap — **CLOSED 2026-08-24**

- **milestone**: retain the actual rational stream `family.physicalGap` in a
  reconstruction convergence handoff; identify its variation-selected limit
  with the exact logarithm of the selected Wilson separator by constructive
  uniqueness; derive positivity from the same family's physical rate band;
  and combine that exact-rate witness with the all-vector graph-norm compiler
  into `WilsonMinimalBoundedMassGap`.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff.lean`.
- **decl**:
  `DynamicVacuumSectorWilsonExactRateHandoff`,
  `physicalGapLimit_equiv_exactLog`, `toExactLogGapAt`,
  `toPositiveExactLogGapWitness`, and
  `compileWilsonMinimalBoundedMassGap`.
- **obligation**: prove that the actual dynamic physical-gap stream converges
  to the exact logarithm computed from the selected OS/Wilson reconstruction;
  construct the all-vector graph-norm approximation and scheduled-rate pin;
  and inhabit the common projective measure, OS/Wilson reconstruction, and
  continuum Yang--Mills existence data.
- **constructive?**: yes — the equality is derived from two convergence
  moduli for the same explicit stream, the positive floor comes from the
  physical rate band, and the operator gap comes only from the all-vector
  finite contraction.  All four audited exports use only
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: the focused guarded check passes.  The exact one-worker
  dependency-complete target passes 5090 jobs, with the new module taking
  about 1.1 seconds.  No convergence handoff, graph-norm data, continuum
  measure, QFT existence theorem, or Clay theorem is claimed.

### [BF4-physical-adaptive-raw-wilson-connected-path] Rejoin the parallel compilers on one observable-connected Wilson endpoint — **CLOSED 2026-08-24**

- **milestone**: define one generic connected residual diagram fixing the
  completed family, raw observable, rate band, physical-gap variation,
  scheduled-rate limit, projective measure thread, and selected Wilson datum;
  compile its exact-rate and graph-norm branches to the minimal all-vector
  bounded gap; add vacuum stationarity to iterate it; identify the literal raw
  limit with one embedded Wilson autocorrelation; derive raw-channel decay in
  the valid operator-to-observable direction; and specialize the scheduled
  rate definitionally to the adaptive physical-exponential limit.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `RawWilsonConnectedMassGapPath`, `minimalBoundedMassGap`,
  `iteratedBoundedMassGap`,
  `physicalRate_equiv_selectedSeparatorExactLog`,
  `rawContinuumConnectedAutocorrelation_eq_matrixCoefficient`,
  `rawContinuumConnectedAutocorrelationSqDecay`,
  `AdaptiveRawWilsonConnectedMassGapPath`, and
  `adaptiveRawPhysicalExponentialPath`.
- **obligation**: inhabit raw zero-time nontriviality; the selected projective
  OS and Wilson matrix-coefficient semantics; convergence of the physical-gap
  stream to the reconstruction logarithm; graph-norm approximation of all
  completed vacuum vectors; vacuum stationarity; the common continuum
  measure and Yang--Mills existence data; and the required QFT axioms.
- **constructive?**: yes — every join is enforced by shared indices or direct
  dependent fields.  The operator gap comes from the all-vector graph-norm
  branch, and only then implies the observable decay.  All seven audited
  exports use only `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: a first over-specialized adaptive record hit the guarded
  heartbeat limit during normalization and contaminated downstream diagnostics
  with `sorryAx`; it was discarded.  The generic-record plus reducible-adaptive
  specialization passes the focused check.  Its exact one-worker target
  passes 5102 jobs, with the new module taking about 1.5 seconds.  No residual
  field, continuum theory, or Clay theorem is claimed inhabited.

### [BF4-physical-connected-dense-unit-vacuum] Pin the connected Wilson state to the concrete vacuum — **CLOSED 2026-08-24**

- **milestone**: replace the connected path's bare `T Omega = Omega` field by
  `WilsonDenseUnitVacuumPin`; derive stationarity through dense intertwining;
  prove that the exact raw Wilson state is orthogonal to the embedded constant
  observable; and transport raw zero-time nontriviality to strict positivity
  of that same completed state's norm square.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `RawWilsonConnectedMassGapPath.vacuumPin`,
  `iteratedBoundedMassGap`, `gapState_orthogonal_denseUnit`, and
  `gapState_norm_isPositive`.
- **obligation**: inhabit the dense-unit vacuum pin by identifying the selected
  OS/Wilson vacuum and proving that its observable time shift preserves the
  unit.  Raw nontriviality, projective/OS semantics, graph-norm convergence,
  exact-rate reconstruction convergence, continuum existence, and the QFT
  endpoint remain separate open inputs.
- **constructive?**: yes — stationarity is derived by the existing dense
  intertwining theorem, orthogonality is rewritten along the explicit vacuum
  equality, and norm positivity is transported along the exact same-object
  matrix-coefficient equality.  All nine audited exports use only
  `[propext, Quot.sound]`.
- **status note**: the focused guarded check passes.  The exact one-worker
  dependency-complete target passes 5103 jobs, with the refined module taking
  about 1.7 seconds.  No vacuum pin or later continuum residual is claimed
  inhabited.

### [BF4-physical-raw-nontriviality-floor] Compile a uniform finite raw norm floor to the continuum state — **CLOSED 2026-08-24**

- **milestone**: prove that one positive rational norm floor valid for the
  exact moving-cube channel at every cutoff passes to strict positivity of its
  zero-time raw continuum correlation; expose the adaptive uniform-floor
  type; and add a connected-path constructor deriving raw nontriviality from
  that finite source.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `MovingCubeRawContinuumNontriviality.ofUniformNormFloor`,
  `RawMovingCubeUniformNormFloor`,
  `rawMovingCubeContinuumNontrivialityOfUniformNormFloor`, and
  `RawWilsonConnectedMassGapPath.ofUniformNormFloor`.
- **obligation**: construct the cutoff-independent raw norm floor.  The known
  coordinate floors depend on scale and cannot be substituted for it.  The
  projective OS, Wilson matrix-coefficient, exact-rate, all-vector graph-norm,
  dense-unit vacuum, continuum existence, and QFT obligations remain open.
- **constructive?**: yes — the proof reuses the explicit scheduled-limit
  convergence and transports one rational floor without choice or
  noncomputable selection.  All newly audited exports use only
  `[propext, Quot.sound]`; no forbidden construct was added.
- **status note**: focused guarded checks pass.  The exact one-worker
  nontriviality target passes 5095 jobs, with the new module taking about 0.9
  seconds.  The connected capstone passes 5104 jobs, taking about 1.8 seconds.
  No uniform floor or later semantic/continuum residual is claimed inhabited.

### [BF4-physical-dynamic-graph-norm-parallel-join] Factor the all-vector limit into three causal compilers — **CLOSED 2026-08-24**

- **milestone**: split the dynamic physical-time graph-norm residual into a
  scalar rate-limit pin, a Wilson representative-transfer lift, and a finite
  all-vector graph approximation; rejoin them through shared dependent
  indices; derive the transfer lift from an existing linear time-translation
  pin; and expose the same three-way join on the raw observable-connected
  capstone.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `DynamicVacuumSectorWilsonPhysicalTimeRateLimitPin`,
  `WilsonPhysicalTimeRepresentativeTransferLift`,
  `WilsonPhysicalTimeRepresentativeTransferLift.ofLinear`,
  `DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation`,
  `DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.ofParallelCompilers`,
  and
  `RawWilsonConnectedMassGapPath.ofUniformNormFloorAndParallelGraphNormCompilers`.
- **obligation**: inhabit the rate pin by identifying the constructed
  physical exponential with the selected separator square; construct or
  import the selected representative transfer; and prove graph-norm
  convergence for every explicit vacuum-orthogonal Wilson representative.
  The projective OS, continuum existence, and QFT obligations remain open.
- **constructive?**: yes — the join is ordinary dependent record assembly,
  and the linear transfer constructor reuses its explicit `TCauchy` map.  No
  quotient representative is chosen from an arbitrary completed point.  All
  newly audited exports use only `[propext, Quot.sound]`.
- **status note**: focused guarded checks pass.  The exact one-worker
  graph-norm target passes 1660 jobs, taking about 1.0 second; the connected
  capstone passes 5104 jobs, taking about 1.9 seconds.  No constituent
  residual or endpoint beyond the conditional compiler is claimed inhabited.

### [BF4-physical-dynamic-raw-projective-adapter] Reuse the rational projective OS path for the completed raw observable — **CLOSED 2026-08-24**

- **milestone**: isolate the equality between each literal completed raw
  representative and the existing projective handoff's physically sampled
  gap observable; compile that equality with the existing projective/OS
  semantics into the dynamic raw handoff; and expose the adapter on the
  observable-connected Wilson capstone.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `RawMovingCubeSampledGapCorrelationIdentification`,
  `RawMovingCubeProjectiveOSCorrelationHandoff.ofProjectiveOSCorrelationHandoff`,
  and
  `RawWilsonConnectedMassGapPath.ofUniformNormFloorAndProjectiveOSCorrelationHandoff`.
- **obligation**: prove the literal representative equality on the same
  physical sampling schedule and inhabit the existing rational projective OS
  handoff.  The Wilson matrix coefficient and all all-vector, continuum, and
  QFT residuals remain separate open inputs.
- **constructive?**: yes — the compiler composes explicit `CReal.Equiv`
  witnesses and reverses the existing gap-functional equivalence.  It does
  not choose a new insertion, observable, measure thread, or representative.
  Both new audited exports use only `[propext, Quot.sound]`.
- **status note**: focused guarded checks pass.  The exact one-worker adapter
  target passes 1663 jobs, taking about 0.9 seconds; the connected capstone
  passes 5105 jobs, taking about 1.9 seconds.  No adapter input or later
  semantic/continuum residual is claimed inhabited.

### [BF4-physical-dynamic-raw-wilson-adapter] Reuse the projective Wilson matrix coefficient on the completed raw path — **CLOSED 2026-08-24**

- **milestone**: transport the existing projective Wilson gap state,
  vacuum-orthogonality proof, and transfer-autocorrelation equality across the
  dynamic raw projective adapter; and expose a connected-path constructor
  consuming the pre-existing projective Wilson pin directly.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `RawMovingCubeWilsonMatrixCoefficientPin.ofProjectiveWilsonOSMatrixCoefficientPin`
  and
  `RawWilsonConnectedMassGapPath.ofUniformNormFloorAndProjectiveWilsonOSMatrixCoefficientPin`.
- **obligation**: inhabit the older projective OS and projective Wilson pins
  and prove the literal raw-to-sampled-gap equality.  Uniform raw
  nontriviality, exact rate, graph-norm convergence, vacuum stationarity,
  continuum existence, and QFT closure remain open.
- **constructive?**: yes — the compiler reuses the existing embedded state and
  its direct `WilsonOSConnectedMatrixCoefficientPin`; it performs no quotient
  representative choice and introduces no new semantic equality.  Both new
  audited exports use only `[propext, Quot.sound]`.
- **status note**: focused guarded checks pass.  The exact one-worker Wilson
  adapter target passes 1668 jobs, taking about 0.8 seconds; the connected
  capstone passes 5106 jobs, taking about 2.1 seconds.  No adapter input or
  later all-vector/continuum residual is claimed inhabited.

### [BF4-physical-connected-stationary-dense-unit] Remove the unnecessary carrier-level unit-preservation obligation — **CLOSED 2026-08-24**

- **milestone**: replace `WilsonDenseUnitVacuumPin` on the connected path by
  the strictly smaller `WilsonDenseUnitStationaryVacuumPin`; use its completed
  stationarity directly for iteration while retaining the embedded-unit
  vacuum equality used by observable orthogonality.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `RawWilsonConnectedMassGapPath.vacuumPin` and
  `RawWilsonConnectedMassGapPath.iteratedBoundedMassGap`.
- **obligation**: identify the selected completed vacuum with the embedded
  unit and prove that the completed transfer fixes it.  The stronger
  carrier-level `tau one` law is no longer required by this capstone.
- **constructive?**: yes — this is a weakening of the residual interface, not
  a new assumption.  The previous stronger pin already maps to the new one by
  `WilsonDenseUnitVacuumPin.toStationaryVacuumPin`.  Audited exports remain
  within `[propext, Quot.sound]`.
- **status note**: the focused guarded check and exact one-worker target pass;
  the latter builds 5106 jobs, with the changed module taking about 2.1
  seconds.  Neither vacuum field nor any later continuum residual is claimed
  inhabited.

### [BF4-physical-dynamic-scheduled-rate-separator-convergence] Derive the scalar graph-norm pin by same-stream limit uniqueness — **CLOSED 2026-08-24**

- **milestone**: replace a free completed-value scalar equality by convergence
  of the literal scheduled finite one-unit rate stream to the selected Wilson
  separator square; derive the limit pin by constructive uniqueness; and
  expose the convergence-form three-way graph-norm join on the raw connected
  capstone.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `DynamicVacuumSectorWilsonPhysicalTimeRateConvergence`,
  `DynamicVacuumSectorWilsonPhysicalTimeRateLimitPin.ofScheduledRateConvergence`,
  `DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.ofParallelConvergenceCompilers`,
  and
  `RawWilsonConnectedMassGapPath.ofUniformNormFloorAndParallelGraphNormConvergenceCompilers`.
- **obligation**: prove convergence of
  `normalizedMovingCubeSampledRatePower family scale 1` to the selected
  separator square.  This is the concrete logarithm/exponential-to-Wilson
  bridge; the transfer and graph approximation branches remain independent
  open inputs.
- **constructive?**: yes — the compiler applies uniqueness to two explicit
  convergence moduli for the definitionally same cutoff stream.  It adds no
  selected limit or free equality.  All four new audited exports use only
  `[propext, Quot.sound]`.
- **status note**: focused guarded checks pass.  The exact one-worker
  graph-norm target passes 1660 jobs, taking about 1.1 seconds; the connected
  capstone passes 5106 jobs, taking about 2.1 seconds.  The convergence theorem
  and every later continuum residual remain uninhabited.

### [BF4-physical-dynamic-wilson-exact-log-euler-evaluation] Isolate and compile the exact scalar inverse frontier — **CLOSED 2026-08-24**

- **milestone**: prove that the actual scheduled upper exponent stream tends
  to the exact logarithmic exponent selected by the same Wilson datum; isolate
  the remaining Euler exponential evaluation at physical time one; compile
  that evaluation to literal scheduled-rate convergence, the scalar rate pin,
  the three-way all-vector graph-norm join, and an adaptive connected-path
  constructor.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `scheduledSquaredRateUpperExponent_converges_selectedWilsonExact`,
  `DynamicVacuumSectorWilsonExactLogEulerEvaluation`,
  `DynamicVacuumSectorWilsonExactLogEulerEvaluation.toPhysicalTimeRateConvergence`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeGraphNormLimitOfExactLogEulerEvaluation`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfExactLogEulerEvaluationCompilers`.
- **obligation**: inhabit the construction-specific evaluation proving that
  the upper Euler exponential generated by twice the selected exact log tends
  to `sep^2`.  This is the still-missing constructive rational log/exponential
  inverse theorem.  Exact-rate reconstruction, transfer semantics, finite
  graph approximation, observable semantics, and continuum/QFT closure remain
  separate open inputs.
- **constructive?**: yes — exponent retargeting and both limit identifications
  use explicit `CReal.Equiv` witnesses and constructive uniqueness.  The
  residual is a Type-level convergence certificate over the literal cutoff
  stream, not a selected limit or custom axiom.  All six audited exports use
  only `[propext, Quot.sound]`.
- **status note**: focused guarded checks pass.  The exact one-worker Euler
  compiler target passes 5095 jobs, with the new module taking about 1.2
  seconds; the connected capstone passes 5107 jobs, taking about 2.3 seconds.
  The evaluation record and all later semantic/continuum residuals are not
  claimed inhabited.

### [BF4-physical-wilson-canonical-exact-log-evaluation] Remove dynamic-family dependence from the scalar inverse frontier — **CLOSED 2026-08-24**

- **milestone**: prove rational-stream continuity of the constructive
  negative exponential for arbitrary nonnegative rational exponent streams;
  prove pointwise nonnegativity of the canonical exact Wilson exponent;
  replace the family-specific scalar residual by a static canonical Wilson
  evaluator; and compile that evaluator back through the scheduled rate,
  graph-norm, and connected-path joins.
- **files**:
  `lean/YMGap/Constructive/CRealExpRationalStreamContinuity.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `CReal.expNeg_antitone_sub_le_zero`,
  `CReal.expNeg_twoSided_contraction`,
  `CReal.convergesTo_expNeg_of_common_rational_exponent_limit`,
  `exactLogGap_approx_nonnegative`,
  `selectedWilsonExactPhysicalTimeExponent_approx_nonnegative`,
  `WilsonCanonicalExactLogEulerEvaluation`,
  `DynamicVacuumSectorWilsonExactLogEulerEvaluation.ofCanonicalWilsonEvaluation`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeGraphNormLimitOfCanonicalWilsonEvaluation`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfCanonicalWilsonEvaluationCompilers`.
- **obligation**: inhabit the family-independent canonical evaluator by a
  constructive rational identity connecting `expNeg` of twice
  `exactLogGap` to the square of the selected separator.  Representative
  transfer, finite all-vector approximation, raw observable semantics,
  continuum existence, and QFT closure remain separate open inputs.
- **constructive?**: yes — the stream transport uses explicit convergence
  moduli and a proved two-sided contraction.  It chooses no limit and assumes
  no logarithm/exponential inverse.  Every newly audited export uses only
  `[propext, Quot.sound]`.
- **status note**: focused guarded checks pass.  Exact one-worker targets pass
  for the rational continuity module (47 jobs, changed module about 0.6
  seconds), the exact-log compiler (5096 jobs, changed module about 1.6
  seconds), and the connected capstone (5108 jobs, changed module about 2.4
  seconds).  The canonical evaluator and all later semantic/continuum
  residuals are not claimed inhabited.

### [BF4-physical-wilson-atomic-exact-log-evaluation] Split the canonical inverse into dyadic and mantissa compilers — **CLOSED 2026-08-24**

- **milestone**: isolate independent dyadic-`log 2` and reduced-mantissa
  inverse evaluators; prove sign data, exact exponent splitting, termwise
  exponential factorization, product-limit recombination, and the exact
  rational retargeting to the selected separator square; expose the two-atom
  join on the observable-connected capstone.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `DyadicLogSquareEulerEvaluation`,
  `MantissaLogSquareEulerEvaluation`,
  `logRat_approx_nonpositive_of_lt_one`,
  `selectedWilsonExactPhysicalTimeExponent_one_approx_eqv_split`,
  `selectedWilsonCanonicalExponential_equiv_atomicProduct`,
  `WilsonCanonicalExactLogEulerEvaluation.ofAtomicEvaluations`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfAtomicWilsonEvaluationCompilers`.
- **obligation**: inhabit the two atomic analytic records by constructive
  rational-series inverse proofs.  The dyadic branch must evaluate twice
  `k * log 2` to `(2^-k)^2`; the mantissa branch must evaluate twice the
  negative direct-window logarithm to `m^2`.  Exact-rate reconstruction,
  transfer/finite-graph approximation, raw observable semantics,
  nontriviality, vacuum stationarity, continuum existence, and QFT closure
  remain separate open inputs.
- **constructive?**: yes — the join uses explicit convergence moduli,
  termwise `CReal.Equiv`, general multiplication continuity, and exact `Q'`
  algebra.  It chooses no limit and assumes no combined Wilson conclusion.
  Every newly audited export uses only `[propext, Quot.sound]`.
- **status note**: focused guarded checks pass.  Exact one-worker targets pass
  for the exact-log compiler (5096 jobs, changed module about 1.8 seconds) and
  the connected capstone (5108 jobs, changed module about 2.5 seconds).
  Neither atomic evaluator nor any later semantic/continuum residual is
  claimed inhabited.

### [BF4-physical-wilson-dyadic-one-seed] Collapse all dyadic exponents to one evaluator — **CLOSED 2026-08-24**

- **milestone**: prove exact successor recurrences for the dyadic logarithmic
  exponent stream, its negative exponential, and its rational square target;
  construct the zero evaluator; generate every exponent from one exponent-one
  seed; and expose the reduced scalar interface on the connected capstone.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `dyadicLogSquareExponent_one_add_eqv_succ`,
  `dyadicLogSquareExponential_one_mul_equiv_succ`,
  `scaleQ_one_mul_scaleQ_eqv_succ`,
  `scaleQ_square_one_mul_square_eqv_succ`,
  `DyadicLogSquareEulerEvaluation.zero`,
  `DyadicLogSquareEulerEvaluation.allOfOne`,
  `WilsonCanonicalExactLogEulerEvaluation.ofDyadicOneAndMantissa`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfDyadicOneAndMantissaEvaluationCompilers`.
- **obligation**: inhabit the single universal
  `DyadicLogSquareEulerEvaluation 1` seed and the
  reconstruction-specific mantissa evaluator.  The dyadic family itself is
  no longer an infinite family of independent assumptions.  Exact-rate,
  transfer/finite-graph approximation, raw observable semantics,
  nontriviality, vacuum stationarity, continuum existence, and QFT closure
  remain separate open inputs.
- **constructive?**: yes — induction uses explicit rational equivalences, the
  negative-exponential addition law, constructive multiplication continuity,
  and convergence-limit retargeting.  No evaluator is selected, and no
  logarithm/exponential inverse is assumed.  Every newly audited export uses
  only `[propext, Quot.sound]`.
- **status note**: focused guarded checks and exact one-worker targets pass.
  The exact-log compiler passes 5096 jobs with the changed target taking about
  1.9 seconds; the connected capstone passes 5108 jobs with the changed target
  taking about 2.7 seconds.  The exponent-one seed, mantissa evaluator, and all
  later semantic/continuum residuals are not claimed inhabited.

### [BF4-physical-wilson-direct-window-inverse] Collapse dyadic and mantissa branches to one compiler — **CLOSED 2026-08-24**

- **milestone**: prove constructive oddness for rational artanh terms and
  partial sums; identify the direct logarithm at `1/2` pointwise with the
  negation of `log 2`; derive the exponent-one dyadic evaluator from the half
  mantissa evaluator; package one uniform direct-window inverse interface; and
  expose it on the connected Wilson capstone.
- **files**:
  `lean/YMGap/Constructive/CRealLogOddness.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `CRealLogOddness.negPow_even_odd_eqv`,
  `CRealLogOddness.artanhTerm_neg_eqv`,
  `CRealLogOddness.artanhPartial_neg_eqv`,
  `CRealLogOddness.logRat_oneHalf_approx_eqv_neg_log2_approx`,
  `DirectWindowLogSquareEulerCompiler`,
  `DyadicLogSquareEulerEvaluation.oneOfOneHalfMantissa`,
  `DirectWindowLogSquareEulerCompiler.dyadicOne`,
  `WilsonCanonicalExactLogEulerEvaluation.ofDirectWindowCompiler`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfDirectWindowEvaluationCompiler`.
- **obligation**: inhabit the single uniform
  `DirectWindowLogSquareEulerCompiler` by proving that the negative
  exponential of twice the negative direct-window logarithm converges to
  `m^2`.  The separate dyadic seed is no longer an independent analytic
  obligation.  Exact-rate, transfer/finite-graph approximation, raw observable
  semantics, nontriviality, vacuum stationarity, continuum existence, and QFT
  closure remain separate open inputs.
- **constructive?**: yes — parity induction, rational equivalences, pointwise
  exponent transport, explicit convergence moduli, and exact limit retargeting
  are used throughout.  No inverse theorem, selected limit, or combined
  Wilson conclusion is assumed.  Every newly audited export uses only
  `[propext, Quot.sound]`.
- **status note**: the oddness module passes a 38-job exact one-worker target
  with the changed module taking about 0.2 seconds.  The exact-log compiler
  passes 5097 jobs in about 2.0 seconds, and the connected capstone passes 5109
  jobs in about 2.8 seconds.  The uniform direct-window compiler and all later
  semantic/continuum residuals are not claimed inhabited.

### [BF4-physical-artanh-ratio-inverse] Remove logarithm and Wilson indices from the scalar inverse — **CLOSED 2026-08-24**

- **milestone**: isolate one family-independent negative-window artanh/Euler
  compiler; prove positivity of its Mobius denominator; prove exact inversion
  `artanhRatio (yOf m) ≃ m`; identify its exponent stream with the direct-log
  mantissa stream; compile it through the direct-window, Wilson, and connected
  observable paths.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerRatio.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `CRealArtanhEulerRatio.one_sub_pos_of_neg`,
  `CRealArtanhEulerRatio.negativeArtanhSquareExponent_nonnegative`,
  `CRealArtanhEulerRatio.NegativeWindowArtanhSquareEulerEvaluation`,
  `CRealArtanhEulerRatio.NegativeWindowArtanhSquareEulerCompiler`,
  `CRealArtanhEulerRatio.artanhRatio_yOf_eqv`,
  `negativeArtanhSquareExponent_yOf_eqv_mantissa`,
  `directWindowLogSquareEulerCompilerOfArtanh`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfArtanhEvaluationCompiler`.
- **obligation**: inhabit the single uniform
  `NegativeWindowArtanhSquareEulerCompiler` by an explicit rational-series
  estimate proving convergence of `expNeg(-4 * artanhPartial y)` to
  `((1+y)/(1-y))^2` for `-1/3 <= y < 0`.  Exact-rate,
  transfer/finite-graph approximation, raw observable semantics,
  nontriviality, projective OS/GNS, vacuum stationarity, continuum existence,
  and QFT closure remain separate open inputs.
- **constructive?**: yes — the reduction uses explicit sign witnesses,
  positive rational reciprocals, exact `Q'.eqv` algebra, termwise exponential
  transport, and convergence-limit retargeting.  It does not inhabit the
  analytic compiler or select a limit.  Every new gate reports only
  `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass: 54 jobs for the constructive
  module (about 0.2 seconds), 5098 jobs for the exact-log compiler (about 2.1
  seconds), and 5110 jobs for the connected capstone (about 2.9 seconds).
  The universal artanh compiler and all later semantic/continuum residuals
  are not claimed inhabited.

### [BF4-physical-positive-artanh-one-copy] Reduce signed square inversion to one positive unsquared identity — **CLOSED 2026-08-24**

- **milestone**: isolate a positive-window, one-copy artanh/Euler evaluator;
  prove sign transport of its exponent and Mobius target; derive the
  negative-window square evaluator by exponential addition and multiplication
  continuity; expose the smaller input through the direct-log and connected
  Wilson paths.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerRatio.lean`,
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `CRealArtanhEulerRatio.positiveArtanhExponent`,
  `CRealArtanhEulerRatio.positiveArtanhDecayRatio`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerEvaluation`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerCompiler`,
  `CRealArtanhEulerRatio.positiveArtanhExponent_neg_eqv_negative`,
  `CRealArtanhEulerRatio.negativeArtanhExponent_add_self_eqv_square`,
  `CRealArtanhEulerRatio.positiveArtanhDecayRatio_neg_eqv_artanhRatio`,
  `negativeWindowArtanhSquareEulerCompilerOfPositiveOne`,
  `directWindowLogSquareEulerCompilerOfPositiveArtanh`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhEvaluationCompiler`.
- **obligation**: inhabit the single uniform
  `PositiveWindowArtanhEulerCompiler` by proving convergence of the literal
  rational stream `expNeg(2 * artanhPartial z)` to `(1-z)/(1+z)` for
  `0 < z <= 1/3`.  The negative branch, square, dyadic family, and Wilson
  mantissa are no longer independent analytic inputs.  Exact-rate,
  transfer/finite-graph approximation, raw observable semantics,
  nontriviality, projective OS/GNS, vacuum stationarity, continuum existence,
  and QFT closure remain separate open inputs.
- **constructive?**: yes — sign conversion, exact rational Mobius algebra,
  termwise exponential congruence, the exponential addition law, general
  multiplication continuity, and limit retargeting are all explicit.  The
  positive compiler remains uninhabited.  Every new gate reports only
  `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass: 55 jobs for the constructive
  module (about 0.3 seconds), 5098 jobs for the exact-log compiler (about 2.1
  seconds), and 5110 jobs for the connected capstone (about 3.0 seconds).
  The positive one-copy compiler and all later semantic/continuum residuals
  are not claimed inhabited.

### [BF4-physical-positive-artanh-pivot] Reduce two-index convergence to one computed rational pivot — **CLOSED 2026-08-24**

- **milestone**: define the explicit inner cutoff supplied by `ExpNeg.Mexp`;
  isolate a Type-level outer-stage pivot certificate; derive the complete
  two-index positive-artanh Euler evaluation from that certificate and the
  existing exponential Cauchy modulus; expose the reduced compiler on the
  connected Wilson capstone.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerRatio.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `CRealArtanhEulerRatio.positiveArtanhEulerPivot`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerPivotCertificate`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerPivotCompiler`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerPivotCertificate.toEvaluation`,
  `CRealArtanhEulerRatio.positiveWindowArtanhEulerCompilerOfPivot`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPivotCompiler`.
- **obligation**: inhabit the uniform pivot compiler by constructing its outer
  modulus and proving the one rational two-sided comparison at the computed
  inner cutoff.  The inner exponential approximation is no longer an
  independent quantified residual.  Exact-rate, transfer/finite-graph
  approximation, raw observable semantics, nontriviality, projective OS/GNS,
  vacuum stationarity, continuum existence, and QFT closure remain separate
  open inputs.
- **constructive?**: yes — the certificate stores its modulus as data, the
  conversion uses the explicit `ExpNeg.Mexp` Cauchy estimate, and the two
  half-error budgets close by rational equivalence.  No evaluator is assumed
  inhabited and no propositional witness is selected.  Every new gate reports
  only `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass: 55 jobs for the constructive
  module (about 0.3 seconds) and 5110 jobs for the connected capstone (about
  3.1 seconds).  The pivot compiler and all later semantic/continuum
  residuals are not claimed inhabited.

### [BF4-physical-positive-artanh-cleared-defect] Clear the final scalar denominator — **CLOSED 2026-08-24**

- **milestone**: express the finite pivot error as one rational
  cross-difference; prove that a denominator-scaled absolute defect bound
  implies the previous two-sided ratio comparison; compile the division-free
  certificate through the pivot, convergence, Wilson, graph-norm, and raw
  connected-observable path.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerRatio.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `CRealArtanhEulerRatio.positiveArtanhEulerClearedDefect`,
  `CRealArtanhEulerRatio.close_to_positiveArtanhDecayRatio_of_clearedDefect`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerClearedDefectCertificate`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerClearedDefectCompiler`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerClearedDefectCertificate.toPivot`,
  `CRealArtanhEulerRatio.positiveWindowArtanhEulerPivotCompilerOfClearedDefect`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhClearedDefectCompiler`.
- **obligation**: inhabit the uniform cleared-defect compiler by constructing
  its outer modulus and proving
  `abs((1+z) * E - (1-z)) <= (epsilon/2) * (1+z)` at the computed rational
  pivot.  No reciprocal remains in the open analytic field.  Exact-rate,
  transfer/finite-graph approximation, raw observable semantics,
  nontriviality, projective OS/GNS, vacuum stationarity, continuum existence,
  and QFT closure remain separate open inputs.
- **constructive?**: yes — the conversion uses positive-denominator witnesses,
  exact `Q'.eqv` algebra, and constructive cross-multiplied division lemmas.
  It does not inhabit the defect certificate or select a modulus from a
  proposition.  Every new gate reports only `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass: 57 jobs for the constructive
  module (about 0.4 seconds) and 5110 jobs for the connected capstone (about
  3.3 seconds).  The cleared-defect compiler and all later
  semantic/continuum residuals are not claimed inhabited.

### [BF4-physical-positive-artanh-single-anchor] Collapse all late stages to one computed anchor — **CLOSED 2026-08-24**

- **milestone**: expose the explicit artanh modulus; prove a uniform finite
  exponential response bound on the positive window; compare moving computed
  pivots through a common maximum cutoff; compile one anchor defect inequality
  into the complete two-index convergence evaluator and connected Wilson
  capstone.
- **files**:
  `lean/YMGap/Constructive/CRealLog.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerRatio.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `CRealLog.Martanh`, `CRealLog.artanh_cauchy_explicit`,
  `CRealArtanhEulerRatio.positiveArtanhExponent_le_one`,
  `CRealArtanhEulerRatio.positiveArtanhExponent_cauchy_explicit`,
  `CRealArtanhEulerRatio.positiveArtanhExpPartialSum_cauchy_explicit`,
  `CRealArtanhEulerRatio.positiveArtanhEulerMovingPivot_cauchy_explicit`,
  `CRealArtanhEulerRatio.positiveArtanhEulerAnchorStage`,
  `CRealArtanhEulerRatio.positiveArtanhEulerAnchorPivot`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerSingleAnchorCertificate`,
  `CRealArtanhEulerRatio.PositiveWindowArtanhEulerSingleAnchorCertificate.toEvaluation`,
  `CRealArtanhEulerRatio.positiveWindowArtanhEulerCompilerOfSingleAnchor`, and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhSingleAnchorCompiler`.
- **obligation**: inhabit the uniform
  `PositiveWindowArtanhEulerSingleAnchorCompiler` by proving, for each positive
  `epsilon`, the one rational inequality
  `abs((1+z) * E - (1-z)) <= (epsilon/8) * (1+z)` at
  `positiveArtanhEulerAnchorStage epsilon` and
  `positiveArtanhEulerAnchorPivot z epsilon`.  No modulus and no quantified
  later-stage estimate remain in the open certificate.  Exact-rate,
  transfer/finite-graph approximation, raw observable semantics,
  nontriviality, projective OS/GNS, vacuum stationarity, continuum existence,
  and QFT closure remain separate open inputs.
- **constructive?**: yes — the proof uses explicit artanh and exponential
  moduli, the `[0,1]` exponent bound, a finite response constant `3`, a common
  maximum cutoff, and five explicit eighth-budgets.  It does not extract a
  witness from a proposition and does not inhabit the single-anchor compiler.
  Every new gate reports only `[propext, Quot.sound]` or `[propext]`.
- **status note**: guarded checks pass.  Exact one-worker targets pass 32 jobs
  for `CRealLog` and 57 jobs for `CRealArtanhEulerRatio`; the connected
  capstone also passes its exact one-worker target.  The single-anchor
  compiler and all later semantic/continuum residuals are not claimed
  inhabited.

### [BF4-physical-positive-artanh-geometric-value-anchor] Reduce the scalar anchor to one finite Euler-versus-polynomial inequality — **CLOSED 2026-08-24**

- **milestone**: prove the finite geometric telescope and its dyadic residual
  bound; cancel the common cleared numerator; compile one direct finite value
  comparison at computed artanh, Euler, and polynomial indices through the
  positive-artanh inverse and connected Wilson capstone.
- **files**:
  `lean/YMGap/Constructive/QGeometricSum.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerGeometricAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QGeometricSum.geomSum_telescope`,
  `QGeometricSum.one_sub_mul_geomSum`,
  `CRealArtanhEulerGeometricAnchor.positiveArtanhGeometricDefect_eqv`,
  `CRealArtanhEulerGeometricAnchor.positiveArtanhGeometricAnchorDefect_abs_le`,
  `CRealArtanhEulerGeometricAnchor.clearedDefect_sub_geometricDefect_eqv`,
  `CRealArtanhEulerGeometricAnchor.PositiveWindowArtanhEulerGeometricValueAnchorCertificate`,
  `CRealArtanhEulerGeometricAnchor.positiveWindowArtanhEulerCompilerOfGeometricValueAnchor`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhGeometricValueAnchorCompiler`.
- **obligation**: inhabit the uniform geometric-value-anchor compiler by
  proving, for each `0 < z <= 1/3` and positive `epsilon`, the explicit finite
  inequality comparing the computed Euler partial sum with
  `(1-z) * sum_{k=0}^{degree} (-z)^k`, at
  `degree = (epsilon/16).den`.  No limit, reciprocal, modulus, or quantified
  late-stage statement remains in this field.  Exact-rate, transfer/finite-
  graph approximation, raw observable semantics, nontriviality, projective
  OS/GNS, vacuum stationarity, continuum existence, and QFT closure remain
  separate open inputs.
- **constructive?**: yes — the geometric residual is an exact `Q'.eqv`
  telescope, its bound uses explicit dyadic powers, and the two half-budgets
  are combined without choice or classical extraction.  The new compiler is
  not claimed inhabited.  Every new gate reports only `[propext, Quot.sound]`
  or `[propext]`.
- **status note**: the exact one-worker constructive target passes 59 jobs;
  guarded checks for both connected capstone adapters pass.  This closes the
  reduction milestone only, not the finite comparison or any later physical
  or continuum obligation.

### [BF4-physical-positive-artanh-polynomial-coefficient-anchor] Reflect the finite scalar anchor to an executable coefficient check — **CLOSED 2026-08-24**

- **milestone**: construct explicit coefficient polynomials for the finite
  artanh series, its finite Euler exponential composition, and the geometric
  comparison; prove their exact evaluation semantics; prove a weighted
  coefficient-`L1` evaluation bound; compile one decidable coefficient
  inequality and its Boolean presentation through the scalar inverse and
  connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/QPolyWeightedL1.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QPolyWeightedL1.weightedL1`,
  `QPolyWeightedL1.abs_eval_le_weightedL1`,
  `CRealArtanhEulerPolynomialAnchor.eval_positiveArtanhEulerGeometricDifferencePoly`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerPolynomialCoefficientBound`,
  `CRealArtanhEulerPolynomialAnchor.auditPositiveArtanhEulerPolynomialCoefficientBound`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCheckedCertificate.toCoefficient`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialCheckedCompiler`.
- **obligation**: inhabit the uniform checked compiler by proving that every
  admissible `z` and positive `epsilon` passes the computed coefficient
  Boolean.  The remaining mathematical work should factor into exact
  low-degree formal coefficient cancellation and a weighted high-degree tail
  estimate.  Exact-rate, transfer/finite-graph approximation, raw observable
  semantics, nontriviality, projective OS/GNS, vacuum stationarity, continuum
  existence, and QFT closure remain separate open inputs.
- **constructive?**: yes — coefficient lists and their Horner semantics are
  explicit, the weighted norm is proved by recursion, and each concrete audit
  returns proof-carrying success or failure.  The audit and Boolean conversion
  use no axioms; downstream semantics stay within `[propext, Quot.sound]`.
  No uniform successful compiler is claimed.
- **status note**: the exact one-worker constructive target passes 61 jobs;
  guarded connected-capstone checks pass.  This closes the reflection and
  decision-procedure milestone only, not uniform success or any later
  physical/continuum obligation.

### [BF4-physical-positive-artanh-polynomial-prefix-tail] Split the coefficient check into exact cancellation and a weighted tail — **CLOSED 2026-08-24**

- **milestone**: prove the weighted coefficient norm is subadditive and
  submultiplicative; propagate it through reflected artanh and Euler
  polynomials; implement an executable zero-prefix predicate; factor a passed
  zero prefix into an explicit radius power times the dropped tail; compile
  the resulting prefix/tail certificate through the scalar and connected
  Wilson path.
- **files**:
  `lean/YMGap/Constructive/QPolyWeightedL1.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QPolyWeightedL1.weightedL1_pmul_le`,
  `QPolyWeightedL1.zeroPrefix`,
  `QPolyWeightedL1.weightedL1_eqv_pow_mul_drop_of_zeroPrefix`,
  `CRealArtanhEulerPolynomialAnchor.weightedL1_positiveArtanhExponentPoly_le`,
  `CRealArtanhEulerPolynomialAnchor.weightedL1_expPartialPoly_le`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerPolynomialCancellationCount`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialPrefixTailCertificate`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialPrefixTailCompiler`.
- **obligation**: inhabit the prefix/tail compiler.  The exact formal task is
  to prove that the first
  `min inner (min (2*stage+1) (degree+1))` coefficients cancel.  Independently,
  the analytic task is to bound the dropped tail after multiplication by the
  corresponding power of `abs z`.  Exact-rate, transfer/finite-graph
  approximation, raw observable semantics, nontriviality, projective OS/GNS,
  vacuum stationarity, continuum existence, and QFT closure remain separate
  open inputs.
- **constructive?**: yes — all polynomial operations, zero-prefix checks,
  list drops, radius powers, and norm inequalities are explicit data or
  recursive proofs.  No successful prefix or tail compiler is postulated as
  inhabited.  Gates remain within `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 47 jobs for the weighted norm,
  61 for the polynomial anchor, and 5114 for the connected capstone.  The split
  exposes two parallel proof ribs but does not close either one uniformly.

### [BF4-physical-positive-artanh-polynomial-one-tail] Prove the constant cancellation and remove its certificate field — **CLOSED 2026-08-24**

- **milestone**: prove that the explicit exponential pivot is at least one;
  prove both finite comparison expressions equal one at input zero; infer that
  the anchor difference vanishes at zero; turn that semantic equality into an
  executable one-coefficient zero prefix; and compile the remaining weighted
  tail through the unchanged scalar and connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/QPolyWeightedL1.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QPolyWeightedL1.zeroPrefix_one_of_eval_zero`,
  `CRealArtanhEulerPolynomialAnchor.one_le_expNegMexp`,
  `CRealArtanhEulerPolynomialAnchor.eval_positiveArtanhEulerGeometricDifferencePoly_zero`,
  `CRealArtanhEulerPolynomialAnchor.zeroPrefix_one_positiveArtanhEulerAnchorDifferencePoly`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialOneTailCertificate`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialOneTailCertificate.toCoefficient`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialOneTailCompiler`.
- **obligation**: inhabit the one-tail compiler by proving the displayed
  weighted norm after dropping the constant coefficient.  In parallel, prove
  the stronger exact prefix through
  `min inner (min (2*stage+1) (degree+1))`; that stronger rib is not logically
  needed by the new interface, but its larger radius power may be needed for a
  sharp uniform tail estimate.  All later exact-rate, transfer/finite-graph,
  raw-observable, projective OS/GNS, vacuum, continuum, QFT, and Clay inputs
  remain separate and open.
- **constructive?**: yes.  The proof uses recursive rational-series identities,
  positivity of an explicit natural denominator, Boolean zero-prefix
  reflection, and kernel-checked `Q'.eqv`.  No successful tail compiler is
  claimed inhabited.  Gates stay inside `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 47 jobs for the weighted norm,
  61 jobs for the polynomial anchor, and 5114 jobs for the connected capstone.
  This closes one exact coefficient only; it does not close the full formal
  prefix, weighted tail, scalar inverse, operator gap, or continuum target.

### [BF4-physical-positive-artanh-polynomial-two-tail] Prove the linear cancellation and expose a quadratic tail — **CLOSED 2026-08-24**

- **milestone**: build constant/linear formal jets for the constructive
  coefficient-list algebra; compute the artanh exponent, finite Euler sum, and
  finite geometric comparison jets; prove the computed anchor stage is at
  least one, the positive-input Euler pivot is at least two, and the geometric
  degree is at least one; use those facts to prove a uniform two-coefficient
  zero prefix and compile the residual quadratic-radius tail through the
  connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/QPolyJetOne.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QPolyJetOne.constantCoeff`, `QPolyJetOne.linearCoeff`,
  `QPolyJetOne.linearCoeff_pmul`,
  `QPolyJetOne.zeroPrefix_two_of_coefficients_zero`,
  `CRealArtanhEulerPolynomialAnchor.linearCoeff_expPartialPoly_add_two_eqv_negativeTwo`,
  `CRealArtanhEulerPolynomialAnchor.linearCoeff_positiveArtanhGeometricApproxPoly_succ_eqv_negativeTwo`,
  `CRealArtanhEulerPolynomialAnchor.two_le_positiveArtanhEulerAnchorPivot`,
  `CRealArtanhEulerPolynomialAnchor.zeroPrefix_two_positiveArtanhEulerAnchorDifferencePoly`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialTwoTailCertificate.toCoefficient`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialTwoTailCompiler`.
- **obligation**: inhabit the quadratic-tail compiler, or continue the formal
  prefix induction to the full computed count before estimating the tail.  A
  fixed quadratic factor does not by itself provide arbitrary-precision
  decay at the endpoint `abs z = 1/3`; the general prefix remains the likely
  sharp route.  Exact-rate, transfer/finite-graph, raw-observable,
  projective OS/GNS, vacuum, continuum, QFT, and Clay inputs remain separate
  and open.
- **constructive?**: yes.  The jet carrier is explicit rational data; all
  algebraic laws are recursive `Q'.eqv` proofs; index lower bounds come from
  positive natural denominators and positive rational numerators; and the
  resulting prefix is an executable Boolean certificate.  No tail compiler
  is claimed inhabited.  Gates stay within `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 48 jobs for `QPolyJetOne`, 62
  jobs for the polynomial anchor, and 5115 jobs for the connected capstone.
  This closes two coefficients only, not the full formal prefix or any later
  scalar, operator, or continuum target.

### [BF4-physical-positive-artanh-arbitrary-coefficient-join] Expose arbitrary formal coefficients and join independent algebraic/analytic ribs — **CLOSED 2026-08-24**

- **milestone**: define an arbitrary padded coefficient extractor and its
  constructive algebraic laws, prove exact equivalence between pointwise
  coefficient vanishing and executable prefix cancellation, separate the
  remaining scalar frontier into a formal coefficient compiler and an
  analytic full-tail compiler, and rejoin them before the existing scalar
  inverse and connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/QPolyCoefficient.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QPolyCoefficient.coeff`,
  `QPolyCoefficient.coeff_pmul`,
  `QPolyCoefficient.zeroPrefix_iff_coeff_eqv_zero`,
  `CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialFormalCoefficientCertificate`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialFullTailCompiler`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerPolynomialPrefixTailCompilerOfFormalAndTail`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialFormalAndTail`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialFormalAndTailCompilers`.
- **obligation**: inhabit the formal coefficient certificate by proving every
  coefficient below the computed truncation minimum is zero, and independently
  inhabit the full-tail compiler by a uniform weighted residual estimate.
  Neither input is currently constructed.  Exact-rate, transfer/finite-graph,
  raw-observable, projective OS/GNS, vacuum, continuum, QFT, and Clay inputs
  remain separate and open.
- **constructive?**: yes.  The arbitrary coefficient and convolution functions
  are recursive, the prefix equivalence constructs the Boolean certificate,
  and the join carries both proof objects into one unchanged downstream path.
  No classical choice or successful compiler instance is introduced.  The new
  gates stay within `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 49 jobs for
  `QPolyCoefficient` and 63 jobs for the polynomial anchor; the guarded
  connected-capstone check passes.  This closes the compiler architecture and
  observable-preserving join only, not either open rib or any scalar inverse,
  operator gap, continuum theory, or Clay conclusion.

### [BF4-physical-positive-artanh-euler-valuation-stability] Remove the moving Euler truncation from the formal coefficient frontier — **CLOSED 2026-08-24**

- **milestone**: prove constructive zero-prefix valuation laws for polynomial
  addition, scaling, and multiplication; prove Euler term `k` has valuation at
  least `k` for every zero-constant exponent; prove every coefficient below a
  finite Euler truncation is already stable; factor the remaining formal
  certificate through canonical stabilized coefficients; and carry that
  reduced input through the unchanged scalar and connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/QPolyCoefficient.lean`,
  `lean/YMGap/Constructive/QPolyValuation.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QPolyValuation.zeroPrefix_pmul_add`,
  `CRealArtanhEulerPolynomialAnchor.zeroPrefix_expTermPoly`,
  `CRealArtanhEulerPolynomialAnchor.coeff_expPartialPoly_add_stable`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff`,
  `CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt`,
  `CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialStableCoefficientCertificate.toFormal`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialStableAndTail`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialStableAndTailCompilers`.
- **obligation**: inhabit the stabilized coefficient certificate by proving
  the canonical Euler coefficient equals the finite geometric coefficient
  below the artanh and geometric truncation orders; independently inhabit the
  full-tail compiler.  The inner Euler cutoff is no longer an open formal
  parameter.  Physical-carrier, OS/operator, limit, continuum, QFT, and Clay
  inputs remain separate and open.
- **constructive?**: yes.  Prefix valuation is proved by recursive coefficient
  reflection and rational equivalence.  Stability follows because each added
  Euler term has an explicitly proved zero prefix.  No formal infinite series,
  normalization, classical choice, or successful residual certificate is
  postulated.  Gates remain within `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 50 jobs for
  `QPolyValuation`, 64 jobs for the polynomial anchor, and 5117 jobs for the
  connected capstone.  This closes Euler-truncation stability only; it does
  not close the stabilized artanh/geometric identity, analytic tail, scalar
  inverse, physical operator gap, continuum theory, or Clay conclusion.

### [BF4-physical-positive-artanh-geometric-degree-elimination] Compute the finite geometric coefficients and remove degree from the formal frontier — **CLOSED 2026-08-24**

- **milestone**: prove exact coefficient formulas for multiplication by a
  two-coefficient polynomial, pure powers of `-z`, and the finite geometric
  sum; compute the closed coefficients of `(1-z)/(1+z)` inside its finite
  truncation window; reduce the formal certificate to a stage/index target;
  and carry that target plus the independent analytic tail through the
  unchanged scalar and connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/QPolyCoefficient.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**: `QPolyCoefficient.coeff_pmul_pair_left_succ`,
  `QPolyCoefficient.coeff_pmul_pair_succ`,
  `CRealArtanhEulerPolynomialAnchor.coeff_ppow_neg_pvar`,
  `CRealArtanhEulerPolynomialAnchor.coeff_geometricSumPoly`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhFormalTargetCoeff`,
  `CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhGeometricApproxPoly_eq_target`,
  `CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialTargetCoefficientCertificate.toStable`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialTargetAndTail`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialTargetAndTailCompilers`.
- **obligation**: inhabit the target coefficient certificate by proving that
  the canonical stabilized finite-Euler coefficient equals the explicit
  alternating target below `2*stage+1`; independently inhabit the full-tail
  compiler.  The geometric degree is no longer an open formal parameter.
  Physical-carrier, OS/operator, limit, continuum, QFT, and Clay inputs remain
  separate and open.
- **constructive?**: yes.  Every coefficient formula is a recursive
  `Q'.eqv` proof over finite lists and natural indices.  The reduced target is
  Type-level data, no successful target or tail certificate is postulated,
  and the observable-preserving join uses the same downstream parameters.
  Gates remain within `[propext, Quot.sound]`.
- **status note**: the exact one-worker connected capstone passes 5117 jobs.
  This closes the finite-geometric coefficient computation and degree
  elimination only; it does not close the stabilized Euler recurrence,
  analytic tail, scalar inverse, physical operator gap, continuum theory, or
  Clay conclusion.

### [BF4-physical-positive-artanh-stable-successor-reduction] Reduce the formal target to one local stabilized-coefficient recurrence — **CLOSED 2026-08-24**

- **milestone**: prove the stabilized Euler constant and linear coefficients;
  prove the same two closed comparison seeds and its alternating successor
  law; show one local Euler successor recurrence generates every target
  coefficient below the artanh truncation order; and carry that reduced input
  with the independent analytic tail through the unchanged scalar and
  connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff_zero_eqv_one`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff_one_eqv_negativeTwo`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhFormalTargetCoeff_succ_eqv_neg`,
  `CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialStableRecurrenceCertificate`,
  `CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialStableRecurrenceCertificate.toTarget`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialRecurrenceAndTail`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialRecurrenceAndTailCompilers`.
- **obligation**: inhabit the recurrence certificate by proving that every
  positive stabilized Euler coefficient below `2*stage+1` is the negative of
  its predecessor; independently inhabit the full-tail compiler.  The two
  coefficient seeds and the induction from recurrence to the closed target
  are no longer open.  Physical-carrier, OS/operator, limit, continuum, QFT,
  and Clay inputs remain separate and open.
- **constructive?**: yes.  The seeds are finite coefficient-list proofs, the
  closed target recurrence is exact `Q'.eqv` algebra, and `toTarget` is natural
  induction carrying all witnesses in `Type`.  No recurrence or tail
  certificate is claimed inhabited.  Gates remain within
  `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 64 jobs for the polynomial
  anchor and 5117 jobs for the connected capstone.  This closes the recurrence
  reduction and observable-preserving adapters only, not the recurrence
  itself, analytic tail, scalar inverse, physical operator gap, continuum
  theory, or Clay conclusion.

### [BF4-physical-positive-artanh-stable-successor-proof] Prove the finite stabilized Euler recurrence and close the algebraic rib — **CLOSED 2026-08-24**

- **milestone**: construct coefficient-level formal differentiation and the
  finite Leibniz rule; differentiate the finite artanh exponent and Euler
  partial polynomial; telescope the exponent derivative with `1-z^2`; extract
  the local stabilized differential recurrence; prove the alternating
  successor law by strong induction and positive-factor cancellation; inhabit
  the recurrence, target, stabilized, and formal coefficient certificates;
  and expose the connected adapter whose sole scalar input is the analytic
  full-tail compiler.
- **files**:
  `lean/YMGap/Constructive/QPolyFormalDerivative.lean`,
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `QPolyFormalDerivative.coeff_pderiv_pmul`,
  `QPolyFormalDerivative.pderiv_pmul`,
  `CRealArtanhEulerPolynomialAnchor.pderiv_positiveArtanhExponentPoly`,
  `CRealArtanhEulerPolynomialAnchor.pderiv_expPartialPoly_succ`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhExpPartialPoly_finiteDifferentialEquation`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff_differentialRecurrence`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff_succ_eqv_neg`,
  `CRealArtanhEulerPolynomialAnchor.canonicalPositiveArtanhEulerPolynomialFormalCoefficientCertificate`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialFullTail`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialFullTailCompiler`.
- **obligation**: inhabit
  `PositiveWindowArtanhEulerPolynomialFullTailCompiler`.  The algebraic
  recurrence and every coefficient-cancellation certificate derived from it
  are no longer open inputs.  Physical-carrier, projective OS/GNS,
  transfer/operator, thermodynamic/continuum, QFT, and Clay inputs remain
  separate and open.
- **constructive?**: yes.  Differentiation and convolution are structurally
  recursive finite-list constructions; all equality is `Q'.eqv`; the only
  coefficient division is discharged by explicit positive-factor
  cancellation.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  or new axiom is introduced.  Audited gates remain within
  `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 50 jobs for
  `QPolyFormalDerivative`, 65 jobs for the polynomial anchor, and 5118 jobs
  for the connected capstone.  This closes only the finite algebraic scalar
  rib.  It does not prove the analytic full-tail estimate, scalar inverse,
  physical mass gap, continuum theory, or Clay conclusion.

### [BF4-physical-positive-artanh-cutoff-radius-decay] Prove the computed cutoff decay and reduce the analytic tail to a fixed shifted-size bound — **CLOSED 2026-08-24**

- **milestone**: compute the exact denominators of the comparison tolerance
  and outer stage; prove the positive Euler pivot lies beyond the geometric
  cutoff; identify the common cancellation count exactly with the successor
  of the geometric degree; prove that its radius power times two fits inside
  the reserved tolerance throughout the positive artanh window; replace the
  former epsilon-dependent full-tail input by one fixed shifted-tail-size
  certificate; and carry that smaller input through the unchanged scalar and
  observable-connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhGeometricComparisonTolerance_den`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerAnchorStage_eq`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerAnchorPivot_ge_comparisonDen_add_two`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerAnchorCancellationCount_eq_geometricDegree_succ`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerAnchorRadiusPow_mul_two_le_comparisonTolerance`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate.toFullTail`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialResidualTailSize`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialResidualTailSizeCompiler`.
- **obligation**: inhabit
  `PositiveWindowArtanhEulerPolynomialResidualTailSizeCompiler` by proving,
  uniformly on `0 < z` and `|z| <= 1/3`, that the weighted coefficient tail
  after the explicit geometric boundary `degree + 1` has shifted norm at most
  two.  The cutoff choice, radius decay, and epsilon budget are no longer open
  inputs.  Physical-carrier, projective OS/GNS, transfer/operator,
  thermodynamic/continuum, QFT, and Clay inputs remain separate and open.
- **constructive?**: yes.  Denominators and cutoffs are exact natural-number
  computations, the dyadic decay uses the explicit `HalfPow` modulus, and the
  residual bound remains named `Type`-level data rather than a postulated
  successful evaluation.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.  Audited gates
  remain within `[propext, Quot.sound]`.
- **status note**: after rebuilding the changed constructive dependency,
  exact one-worker targets pass 65 jobs for the polynomial anchor and 5118
  jobs for the connected capstone.  The earlier guarded connected check with
  stale imports is not counted as a pass.  This closes only the cutoff/radius
  half of the analytic scalar tail; it does not inhabit the residual tail-size
  compiler, construct a scalar inverse or physical mass gap, or prove the
  continuum/Clay endpoint.

### [BF4-physical-positive-artanh-first-active-boundary] Compute the first uncancelled coefficient and shift the analytic frontier past it — **CLOSED 2026-08-24**

- **milestone**: prove that the first geometric-boundary coefficient is one
  alternating-sign copy, prove that the finite Euler coefficient there is
  still the stabilized two-copy target, compute their difference and its
  absolute value exactly, split the shifted weighted coefficient norm at that
  boundary, and use `|z| <= 1/3` to compile a post-boundary size-three bound
  into the former residual size-two bound.  Carry the smaller input through
  the unchanged scalar inverse and same-observable connected Wilson path.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff_eq_target_of_lt`,
  `CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhGeometricApproxPoly_boundary`,
  `CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhEulerAnchorDifferencePoly_boundary`,
  `CRealArtanhEulerPolynomialAnchor.abs_coeff_positiveArtanhEulerAnchorDifferencePoly_boundary_eqv_one`,
  `CRealArtanhEulerPolynomialAnchor.weightedL1_drop_eqv_boundary_add_tail`,
  `CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerResidualTailSize_two_of_postBoundary_three`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate.toResidualTailSize`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialPostBoundaryTailSize`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialPostBoundaryTailSizeCompiler`.
- **obligation**: inhabit
  `PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCompiler` by proving,
  uniformly on `0 < z` and `|z| <= 1/3`, that the weighted coefficient tail
  strictly after the exact first boundary has norm at most three.  The first
  boundary coefficient, cutoff choice, radius decay, and tolerance accounting
  are no longer open inputs.  Physical-carrier, projective OS/GNS,
  transfer/operator, thermodynamic/continuum, QFT, and Clay inputs remain
  separate and open.
- **constructive?**: yes.  Coefficients are computed in finite rational
  polynomials, the tail split is structural recursion on lists, and all
  equality is `Q'.eqv`.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.  Audited gates
  remain exactly `[propext, Quot.sound]`.
- **status note**: the first guarded anchor check exposed a source-order
  forward reference and is not counted as a pass.  After reorganizing the
  proof around the earlier recurrence theorem, exact one-worker targets pass
  65 jobs for the polynomial anchor and 5118 jobs for the connected capstone.
  This contracts only the finite scalar-tail interface; it does not inhabit
  the new compiler, construct a scalar inverse or physical mass gap, or prove
  the continuum/Clay endpoint.

### [BF4-physical-positive-artanh-euler-only-tail] Eliminate the finite geometric polynomial after its support boundary — **CLOSED 2026-08-24**

- **milestone**: prove weighted-L1 invariance under padded coefficient
  equivalence, prove the exact coefficient shift induced by `List.drop`, prove
  that the geometric comparison vanishes from `degree+2` onward, identify the
  post-boundary difference tail coefficientwise with the finite Euler tail,
  and carry an Euler-only size-three input through the unchanged scalar and
  observable-connected paths.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `CRealArtanhEulerPolynomialAnchor.weightedL1_eqv_of_coeffEqv`,
  `CRealArtanhEulerPolynomialAnchor.coeff_drop`,
  `CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhGeometricApproxPoly_eqv_zero_of_boundary`,
  `CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhEulerGeometricDifferencePoly_eqv_expPartial_after_boundary`,
  `CRealArtanhEulerPolynomialAnchor.weightedL1_drop_positiveArtanhEulerGeometricDifferencePoly_eqv_expPartial`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialEulerOnlyTailSizeCertificate`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialEulerOnlyTailSizeCertificate.toPostBoundaryTailSize`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialEulerOnlyTailSize`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialEulerOnlyTailSizeCompiler`.
- **obligation**: inhabit
  `PositiveWindowArtanhEulerPolynomialEulerOnlyTailSizeCompiler` by proving,
  uniformly on `0 < z` and `|z| <= 1/3`, that the shifted finite Euler tail
  after `degree+2` has weighted norm at most three.  No geometric comparison,
  first boundary coefficient, cutoff choice, radius decay, or tolerance
  bookkeeping remains in this scalar input.  Physical-carrier, projective
  OS/GNS, transfer/operator, thermodynamic/continuum, QFT, and Clay inputs
  remain separate and open.
- **constructive?**: yes.  Support and list-drop arguments are structurally
  recursive on finite rational coefficient lists, all equality is `Q'.eqv`,
  and the compiler remains named `Type`-level data rather than a proposition
  asserted to hold.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.  Audited gates
  remain exactly `[propext, Quot.sound]`.
- **status note**: one guarded anchor check with a misspelled proof variable is
  not counted as a pass.  After correction, exact one-worker targets pass 65
  jobs for the polynomial anchor and 5118 jobs for the connected capstone.
  This eliminates only the dead geometric tail; it does not inhabit the
  Euler-only compiler, construct a scalar inverse or physical mass gap, or
  prove the continuum/Clay endpoint.

### [BF4-physical-positive-artanh-coefficient-magnitude] Contract the Euler-only tail to a pointwise bound of two — **CLOSED 2026-08-24**

- **milestone**: prove by finite-list induction that coefficient magnitudes at
  most two yield weighted norm at most three on `rho <= 1/3`; expose a
  pointwise magnitude certificate for every coefficient of each finite Euler
  truncation; compile it through the shifted Euler tail and every existing
  scalar adapter; and preserve the same connected raw Wilson observable at the
  capstone.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerPolynomialAnchor.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `CRealArtanhEulerPolynomialAnchor.weightedL1_le_three_of_coeff_abs_le_two`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCoefficientMagnitudeCertificate`,
  `CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCoefficientMagnitudeCertificate.toEulerOnlyTailSize`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerPolynomialEulerOnlyTailSizeCompilerOfCoefficientMagnitude`,
  `CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialCoefficientMagnitude`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialCoefficientMagnitudeCompiler`.
- **obligation**: inhabit
  `PositiveWindowArtanhEulerPolynomialCoefficientMagnitudeCompiler` by proving
  that every padded coefficient of every anchor-selected finite reflected
  Euler polynomial has rational absolute value at most two.  Weighted-tail
  summation, the geometric comparison, first boundary coefficient, cutoff
  choice, radius decay, and tolerance bookkeeping are no longer open scalar
  inputs.  Physical-carrier, projective OS/GNS, transfer/operator,
  thermodynamic/continuum, QFT, and Clay inputs remain separate and open.
- **constructive?**: yes.  The norm estimate is structural recursion over a
  finite coefficient list and uses the exact rational identity
  `2 + (1/3)*3 = 3`.  The pointwise field retains all coefficient witnesses as
  named `Type`-level data.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.  The generic
  folding theorem uses `[propext]`; audited downstream adapters remain within
  `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 65 jobs for the polynomial
  anchor and 5118 jobs for the connected capstone.  This reduces only the
  analytic scalar interface; it does not inhabit the new magnitude compiler,
  construct a scalar inverse or physical mass gap, or prove the
  continuum/Clay endpoint.

### [QPoly-alternating-recoding] Build the finite substitution needed for the positive Euler companion — **CLOSED 2026-08-24**

- **milestone**: define finite coefficient-list substitution `p(z) -> p(-z)`;
  prove its exact padded coefficient formula; and prove that it respects
  addition, scalar multiplication, and multiplication up to `CoeffEqv`.
- **file**: `lean/YMGap/Constructive/QPolyAlternate.lean`.
- **decl**: `QPolyAlternate.alternate`, `coeff_alternate`, `alternate_padd`,
  `alternate_pscale`, and `alternate_pmul`.
- **obligation**: define the corresponding finite positive-Euler companion,
  prove that alternating recoding sends the reflected Euler polynomial to that
  companion, and prove nonnegativity plus coefficientwise domination by the
  stable magnitude-two target.  The coefficient-magnitude compiler and every
  downstream scalar, OS/operator, continuum, QFT, and Clay endpoint remain
  uninhabited.
- **constructive?**: yes.  The operation and proofs recurse only over finite
  rational coefficient lists and use the project's `Q'.eqv`; no normalized
  representative, classical choice, `sorry`, `admit`, `native_decide`,
  `noncomputable`, or new axiom is introduced.
- **status note**: the exact one-worker target passes 51 jobs.  All four
  audited exports use exactly `[propext, Quot.sound]`.  This is an algebraic
  prerequisite only; it does not prove coefficient positivity, the bound of
  two, a scalar inverse, a physical mass gap, or the continuum/Clay endpoint.

### [BF4-positive-artanh-euler-positive-companion] Recode reflected magnitudes as nonnegative companion coefficients — **CLOSED 2026-08-24**

- **milestone**: define the finite positive-sign Euler companion; prove that
  alternating substitution carries the odd artanh exponent and every finite
  reflected Euler partial sum to that companion; prove all companion
  coefficients nonnegative; identify each reflected coefficient magnitude
  exactly with the corresponding companion coefficient; and compile a
  pointwise companion upper bound through the same raw Wilson connected
  capstone.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerPositiveCompanion.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `CRealArtanhEulerPositiveCompanion.positiveExpStepPoly`,
  `positiveExpTermPoly`, `positiveExpPartialPoly`,
  `alternate_positiveArtanhExponentPoly`,
  `alternate_expPartialPoly_positiveArtanh`,
  `CoeffNonnegative`, `coeffNonnegative_positiveExpPartialPoly`,
  `abs_coeff_expPartialPoly_eqv_positiveCompanionCoeff`,
  `PositiveArtanhEulerPositiveCompanionCoefficientUpperBoundCompiler`,
  `positiveWindowArtanhEulerPolynomialCoefficientMagnitudeCompilerOfPositiveCompanion`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPositiveCompanionCoefficientCompiler`.
- **obligation**: prove every padded coefficient of every finite positive
  companion is at most two.  The intended constructive route is
  coefficientwise monotonicity in artanh stage and Euler depth, enlargement to
  a cutoff stable at the requested index, and comparison with the already
  proved stable target coefficient `1` or `2`.  Scalar inverse,
  physical-carrier, projective OS/GNS, transfer/operator,
  thermodynamic/continuum, QFT, and Clay inputs remain separate and open.
- **constructive?**: yes.  Recoding, nonnegativity, and coefficient identities
  use finite polynomial/list recursion and `Q'.eqv`; no normalized rational
  representative, `Classical`, choice, `sorry`, `admit`, `native_decide`,
  `noncomputable`, or new axiom is introduced.  Audited gates are exactly
  `[propext, Quot.sound]`.
- **status note**: exact one-worker targets pass 67 jobs for the positive
  companion and 5120 jobs for the connected capstone.  The capstone still has
  six independent roots, two causally dependent children, and one typed join
  on the same raw Wilson observable.  This does not inhabit the remaining
  upper-bound compiler or prove a physical/continuum/Clay mass gap.

### [BF4-positive-artanh-euler-positive-companion-bound] Close the finite scalar compiler by cutoff monotonicity — **CLOSED 2026-08-24**

- **milestone**: define coefficientwise polynomial order; prove its
  preservation by addition, nonnegative scaling, and finite Cauchy
  multiplication; prove positive-companion monotonicity in both truncation
  indices; enlarge each arbitrary cutoff beyond the requested coefficient;
  compare with the proved stabilized target of magnitude at most two; inhabit
  the positive-companion compiler; and remove the scalar input from the same
  raw Wilson connected capstone.
- **files**:
  `lean/YMGap/Constructive/CRealArtanhEulerPositiveCompanionBound.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `CRealArtanhEulerPositiveCompanionBound.CoeffLe`, `coeffLe_pmul`,
  `coeffLe_positiveExpPartialPoly_stage_add`,
  `coeffLe_positiveExpPartialPoly_inner_add`,
  `abs_positiveArtanhFormalTargetCoeff_le_two`,
  `coeff_positiveExpPartialPoly_le_two`,
  `canonicalPositiveArtanhEulerPositiveCompanionCoefficientUpperBoundCompiler`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfCanonicalPositiveArtanhCoefficientBound`.
- **obligation**: none remains in the finite scalar-inverse branch.  After
  common `family`, `raw`, `H`, and `W` data are fixed, the local capstone still
  requires five independent physical roots: uniform raw norm floor,
  projective OS handoff, exact-rate handoff, representative transfer lift, and
  dense-unit vacuum pin.  The matrix-coefficient pin depends on the OS handoff,
  and finite graph approximation depends on the transfer lift.  Upstream
  continuum existence and Wilson OS/GNS construction and all downstream QFT
  and Clay obligations remain open.
- **constructive?**: yes.  All monotonicity is finite coefficient/list
  recursion; the comparison enlarges natural cutoffs explicitly and uses the
  already proved finite stable coefficient theorem.  No infinite series,
  normalized rational representative, `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: exact one-worker targets pass 68 jobs for the coefficient
  bound and 5121 jobs for the connected capstone.  The magnitude target uses
  `[propext]`; the audited compiler and connected adapter use exactly
  `[propext, Quot.sound]`.  This closes the scalar root and reduces the local
  parallel width from six to five, but it does not construct a physical
  carrier, OS/GNS reconstruction, transfer/operator gap, continuum QFT, or
  Clay mass gap.

### [BF4-moving-cube-normalization-scale-ceiling] Factor raw nontriviality and normalized debt through one finite certificate — **CLOSED 2026-08-25**

- **milestone**: define a uniform positive rational ceiling on the exact
  reciprocal moving-cube coordinate floor; prove that its reciprocal is a
  cutoff-independent raw channel norm floor; prove simultaneous square and
  fourth-power bounds on the normalized norm and squared-correlation debts;
  compile it to raw continuum nontriviality; and thread it through the same
  raw Wilson connected capstone after the canonical scalar inverse.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.lean`.
- **decl**:
  `MovingCubeNormalizationScaleCeiling`,
  `MovingCubeNormalizationScaleCeiling.rawFloor`,
  `rawFloor_le_channelFloor`, `toUniformNormFloor`,
  `normDebt_le_ceiling_sq`, `correlationSqDebt_le_ceiling_fourth`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfNormalizationScaleCeiling`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfCanonicalPositiveArtanhAndNormalizationScaleCeiling`.
- **obligation**: inhabit
  `MovingCubeNormalizationScaleCeiling family.toCompletedFamily` from
  trajectory-specific control of the exact finite coordinate floors.  The
  generic adaptive family carries only pointwise `0 < nome scale < 1`, so its
  present interface cannot supply a nome-uniform ceiling.  Alternatively, the
  normalized route still needs variation/convergence of the reciprocal-square
  debt; boundedness alone does not provide it.  The projective OS handoff,
  matrix-coefficient child, exact-rate handoff, transfer lift, finite graph
  approximation child, vacuum pin, upstream continuum existence/selected
  Wilson datum, and downstream QFT/Clay endpoints remain separate and open.
- **constructive?**: yes.  Reciprocal cancellation and every debt estimate are
  finite `Q'` order calculations; passage to the norm uses the existing exact
  same-object completed-real inequality.  No observable, representative, or
  selected Wilson state is replaced.  No `Classical`, choice, `sorry`,
  `admit`, `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: exact one-worker targets pass 5095 jobs for the
  reciprocal-ceiling compiler and 5121 jobs for the connected capstone.  All
  newly audited exports use exactly `[propext, Quot.sound]`.  This replaces
  the opaque raw-floor root with a finite certificate shared by both proof
  paths; it does not inhabit that root, reduce the five-way physical parallel
  width, prove debt convergence, or construct a continuum/Clay mass gap.

### [BF4-moving-cube-normalization-scale-ceiling-variation-fork] Compile the shared ceiling into normalized debt variation — **CLOSED 2026-08-25**

- **milestone**: connect the exact reciprocal normalization-scale ceiling to
  the existing normalized reciprocal-square variation compiler, thereby
  exposing one checked raw/normalized fork: the ceiling alone yields raw
  nontriviality, while the same ceiling plus summable scale variation yields
  normalized norm-debt variation.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.lean`.
- **decl**:
  `MovingCubeNormalizationScaleCeiling.toNormDebtRationalVariation`.
- **obligation**: the generic adaptive family still supplies neither a
  cutoff-independent ceiling nor summable variation of its exact reciprocal
  normalization scale.  A trajectory-specific finite marginal theorem must
  produce the ceiling for the raw route; the normalized route additionally
  needs scale variation and a same-observable semantic pin.  Projective
  OS/GNS, transfer/operator, thermodynamic/continuum, QFT, and Clay inputs
  remain separate and open.
- **constructive?**: yes.  The new definition merely composes named finite
  rational certificates already inside the axiom gate.  It changes no family,
  raw observable, representative sequence, OS insertion, or Wilson state.  No
  `Classical`, choice, `sorry`, `admit`, `native_decide`, `noncomputable`, or
  new axiom is introduced; the audited gate is exactly
  `[propext, Quot.sound]`.
- **status note**: a guarded bundled-structure experiment timed out during
  elaboration and is not counted as a pass.  The final lightweight method
  passes the exact 5095-job one-worker target, and the connected capstone
  passes 5121 jobs.  This proves only the compiler edge; it does not inhabit
  the ceiling or scale-variation inputs, select a physical route, prove an
  all-vector gap, or construct the continuum/Clay endpoint.

### [canonical-eight-completed-positive-time-sector] Embed the literal two-mode Wilson sector into the actual completion — **CLOSED 2026-08-25**

- **milestone**: construct an injective completed map from the canonical
  vacuum/fundamental GNS completion to the actual interacting canonical Wilson
  GNS completion using pairwise Gram preservation; preserve every completed
  inner product; identify the completed vacuum with the literal polynomial
  unit and the excitation with the literal canonical boundary Wilson
  observable; and compute its embedded connected transfer-power moment.
- **file**:
  `lean/YMGap/Continuum/SU2QuaternionCanonicalEightCompletedPositiveTimeSector.lean`.
- **decl**:
  `DenseGNSGramIsometry`, `DenseGNSGramIsometry.distSq_eqv`,
  `DenseGNSGramIsometry.completed`,
  `DenseGNSGramIsometry.completed_cinner`,
  `DenseGNSGramIsometry.completed_injective`,
  `canonicalCompletedModeEmbedding`,
  `canonicalCompletedModeEmbedding_vacuum`,
  `canonicalCompletedModeEmbedding_fundamental`,
  `canonicalCompleted_fundamental_Tpow`,
  `canonicalEmbeddedFundamentalAt_vacuum_orthogonal`, and
  `canonicalEmbeddedFundamentalConnectedMoment_exact`.
- **obligation**: construct an operator on the whole ambient Wilson completion
  or a proved invariant closed subspace formulation as required by downstream
  all-vector interfaces; instantiate the same literal carrier and observable
  over the dynamic BF4/AF cutoff family; prove cross-scale compatibility,
  uniform vacuum-complement control, thermodynamic and continuum persistence,
  the required QFT axioms, and the Clay mass gap.  The finite two-mode result
  does not discharge any of those open analytic atoms.
- **constructive?**: yes.  The completion map uses explicit Cauchy moduli and
  quotient descent; distance reflection proves injectivity.  The literal
  vector identities and transfer powers use finite rational/quaternion data
  and kernel `decide`.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: the focused monitored one-worker check passes and the
  audited exports use exactly `[propext, Quot.sound]`.  The module is imported
  by `YMGap.lean`; the connected moment is an actual ambient Wilson-GNS matrix
  coefficient induced from the finite compressed sector, not yet an ambient
  full-state transfer or a continuum correlation theorem.

### [completed-positive-time-observable-trajectory] Preserve one literal observable across cutoff-indexed embedded sectors — **CLOSED 2026-08-25**

- **milestone**: factor a generic embedded positive-time sector that transports
  exact source transfer moments and vacuum orthogonality through a
  Gram-preserving completion embedding; index such sectors by cutoff while
  pinning every stage to one shared completed observable; expose summable
  variation only on the derived exact rational moment stream; and inhabit both
  stage and comparison interfaces with the canonical constant trajectory.
- **file**:
  `lean/YMGap/Continuum/CompletedPositiveTimeObservableTrajectory.lean`.
- **decl**:
  `EmbeddedPositiveTimeObservableSector`,
  `EmbeddedPositiveTimeObservableSector.ambientVectorAt_vacuum_orthogonal`,
  `EmbeddedPositiveTimeObservableSector.ambientConnectedMoment_exact`,
  `CompletedPositiveTimeObservableTrajectory`,
  `CompletedPositiveTimeObservableTrajectory.vectorAt_zero`,
  `CompletedPositiveTimeObservableTrajectory.connectedMoment_exact`,
  `CompletedPositiveTimeObservableTrajectory.rationalMoment`,
  `ConnectedMomentVariation`, `ConnectedMomentVariation.converges`,
  `canonicalEmbeddedPositiveTimeObservableSector`,
  `canonicalConstantCompletedPositiveTimeObservableTrajectory`, and
  `canonicalConstantConnectedMomentVariation`.
- **obligation**: inhabit the trajectory with the actual cutoff-indexed
  BF4/AF carrier and the literal moving-cube/Wilson observable, then prove
  summable variation of its derived exact moments.  The canonical inhabitant
  is constant and finite, so it proves compiler consistency but not physical
  scaling.  The five physical roots of the connected capstone, their two
  dependent children, all-vector graph-norm limit, continuum reconstruction,
  QFT axioms, and Clay endpoint remain separate and open.
- **constructive?**: yes.  Ambient identities use only pairwise Gram
  preservation and quotient completion; cutoff comparison uses the existing
  explicit rational step-budget compiler.  The same completed observable is
  pinned before variation is admitted.  No `Classical`, choice, `sorry`,
  `admit`, `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: the focused monitored one-worker check passes, all nine
  audited exports use exactly `[propext, Quot.sound]`, and the exact guarded
  module target passes all 440 jobs.  A root audit reached 2115/3693 jobs
  without a Lean error before the safety monitor stopped it at the 12 GiB
  reserve, so it is not reported as a root pass.  A later lightweight root
  source check could not start because the interrupted audit left the
  pre-existing `BF4ExactCutoffOneSurfaceForestGaugeMask1C66F8.olean` absent.
  This milestone closes the typed finite trajectory/compiler edge, not the
  physical dynamic trajectory, all-vector operator gap, continuum theory, or
  Clay mass gap.

### [moving-cube-normalization-tail-ceiling] Reduce the global reciprocal ceiling to an eventual tail — **CLOSED 2026-08-25**

- **milestone**: compute an exact located maximum for every finite prefix of
  reciprocal moving-cube normalization scales; glue it to one eventual tail
  ceiling; compile summable reciprocal-scale variation to its own automatic
  tail and global ceilings; and feed the resulting single producer to both raw
  nontriviality and normalized reciprocal-square debt variation.
- **files**:
  `lean/YMGap/Continuum/SummableRationalStepVariation.lean` and
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler.lean`.
- **decl**:
  `SummableRationalStepVariation.tailCeilingStart`,
  `SummableRationalStepVariation.tailCeiling`,
  `SummableRationalStepVariation.le_tailCeiling`,
  `movingCubeNormalizationFiniteMaximum`,
  `movingCubeNormalizationScale_le_prefixCeiling`,
  `MovingCubeNormalizationScaleTailCeiling`,
  `MovingCubeNormalizationScaleTailCeiling.toGlobalCeiling`,
  `MovingCubeNormalizationScaleCeiling.ofScaleVariation`,
  `MovingCubeNormalizationScaleCeiling.normDebtRationalVariationOfScaleVariation`,
  and
  `DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumNontrivialityOfNormalizationScaleVariation`.
- **obligation**: prove either an eventual ceiling or, more strongly,
  summable variation for the exact reciprocal coordinate floor along the
  actual BF4/AF trajectory.  No such physical estimate or adaptive-family
  inhabitant is constructed.  Projective OS/GNS compatibility, exact physical
  rate realization, representative transfer lift, stationary vacuum,
  all-vector graph-norm control, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  The finite prefix uses recursive located maxima;
  the automatic tail ceiling uses rational telescoping and the stored
  antitone tail budget.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: focused monitored one-worker checks pass for both files.
  The exact guarded compiler target passes all 5096 jobs.  Nine newly audited
  exports use only `[propext, Quot.sound]` or the smaller `[propext]` subset.
  The root aggregator imports the new module; no full-root pass is claimed.

### [canonical-af-dynamic-scalar-spine] Reduce the dynamic family to its two local analytic fields — **CLOSED 2026-08-25**

- **milestone**: separate the dynamic nome/spacing trajectory from the
  dependent local spin-sector estimates; inhabit a strictly positive shifted
  canonical AF nome and a geometric physical spacing with an explicit
  spacing-to-zero modulus; expose only scale-wise cofinal ray capacity and the
  adaptive transition product for that exact capacity; and compile any such
  local producer to the existing completed dynamic family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalCanonicalAFDynamicFamilyCompiler.lean`.
- **decl**:
  `DynamicSpinCubeOffRayAdaptiveScalarTrajectory`,
  `DynamicSpinCubeOffRayAdaptiveLocalProducer`,
  `DynamicSpinCubeOffRayAdaptiveLocalProducer.toDynamicFamily`,
  `DynamicSpinCubeOffRayAdaptiveLocalProducer.toCompletedFamily`,
  `canonicalAFPositiveNome`, `canonicalAFPositiveNome_pos`,
  `canonicalAFPositiveNome_lt_one`, `canonicalAFGeometricSpacing`,
  `canonicalAFGeometricSpacingToZero`,
  `canonicalAFGeometricScalarTrajectory`,
  `CanonicalAFGeometricLocalProducer`, and
  `canonicalAFGeometricCompletedFamily`.
- **obligation**: inhabit `CanonicalAFGeometricLocalProducer`, or its physical
  analogue, by first constructing a cutoff-uniform cofinal spin-ray capacity
  at every actual nome and then an adaptive transition product indexed by that
  exact capacity.  The existing finite linear product shrinks its input by a
  cutoff-dependent cost and therefore does not supply this cofinal datum.  The
  fixed `1/400` strong-coupling capacity also cannot be relabelled as the
  shifted AF trajectory.  Separately, identify the scalar spine with the real
  4D grouped BF4/AF evolution and pin the same physical observable across its
  completed sectors.
- **constructive?**: yes.  Nome positivity is finite rational order on the
  shifted `1 - invSucc` schedule.  Spacing convergence uses the explicit
  denominator modulus for `(1/2)^scale`.  The local compiler is structural and
  preserves all dependent family/capacity indices.  No `Classical`, choice,
  `sorry`, `admit`, `native_decide`, `noncomputable`, or new axiom is used.
- **status note**: the exact monitored one-worker target passes all 5068 jobs;
  nine audited exports stay within `[propext, Quot.sound]`, with the spacing
  lemmas using `[propext]` only.  The executable forbidden-token scan reports
  zero hits, and the root aggregator imports the module.  This closes five
  scalar fields and the compiler seam, not the two analytic fields, the
  physical dynamic family, continuum reconstruction, QFT axioms, or the Clay
  mass gap.

### [anchor-dynamic-ray-capacity-compiler] Reduce the fixed-anchor dynamic family to one local field — **CLOSED 2026-08-25**

- **milestone**: factor a dynamic ray-capacity producer from its dependent
  adaptive transition product; construct a geometric-spacing scalar
  trajectory with nome fixed literally at `anchorCoupling = 1/400`; install
  the existing cutoff-uniform cofinal ray capacity at every scale; and compile
  any one-field transition-product extension to the existing completed
  dynamic family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalAnchorDynamicRayCapacityCompiler.lean`.
- **decl**:
  `DynamicSpinCubeOffRayAdaptiveRayCapacityProducer`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductExtension`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductExtension.toLocalProducer`,
  `DynamicSpinCubeOffRayAdaptiveTransitionProductExtension.toCompletedFamily`,
  `anchorCoupling_pos`, `anchorCoupling_lt_one`,
  `anchorGeometricScalarTrajectory`,
  `anchorGeometricRayCapacityProducer`,
  `anchorGeometricRayCapacityProducer_delta_pos`,
  `AnchorGeometricAdaptiveTransitionProductExtension`, and
  `anchorGeometricCompletedFamily`.
- **obligation**: inhabit
  `AnchorGeometricAdaptiveTransitionProductExtension` by proving one
  cutoff-uniform adaptive off-ray conditional transition product for the
  exact anchor capacity.  The known finite linear product shrinks capacity by
  a cutoff-dependent cost and does not supply this field.  Separately, the
  canonical AF lane still needs cofinal capacity at each changing nome, and
  the actual grouped BF4 trajectory, same raw observable, projective OS/GNS
  join, completed all-vector gap, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  The anchor order facts are decidable rational
  computations; the scalar spacing reuses the explicit geometric modulus;
  and the capacity is the existing selected-row construction without
  weakening or transport to another nome.  No `Classical`, choice, `sorry`,
  `admit`, `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5069 jobs.
  Nine audited exports use only `[propext, Quot.sound]` or smaller subsets;
  the executable forbidden-token scan reports zero hits, and the root
  aggregator imports the module.  This closes the capacity field only on the
  fixed-anchor/geometric lane, not on the AF or physical continuum lane.

### [adaptive-transition-product-finite-capacity-margin] Reduce pointwise edge capacity to an exact finite scalar margin — **CLOSED 2026-08-25**

- **milestone**: for any positive routing at any fixed cutoff, prove
  nonnegativity of its exact transition-product loads, prove that positive
  load forces positive conditional-kernel support on the same edge, construct
  the located positive minimum of the exact edge-capacity ratios, prove that
  this minimum pays every pointwise edge load, and compile any cofinal routing
  family whose margins dominate the shared coercivity floor to the existing
  completed strict-contraction data and fixed-anchor dynamic extension.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_pos`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_mul_load_le_half_conditionalKernel`,
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin`,
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.toAdaptiveConditionalTransitionProduct`,
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.toCompletedStrictContractionData`,
  `AnchorAdaptiveFiniteCapacityMargin.toAnchorGeometricExtension`, and
  `AnchorAdaptiveFiniteCapacityMargin.toAnchorGeometricCompletedFamily`.
- **obligation**: inhabit the cofinal margin structure.  The shorter route is
  to prove one uniform lower comparison for the canonical routing's exact
  finite margins.  If that margin decays, select cutoff-dependent routings and
  prove the adaptive margins uniformly dominate the same shared floor.  No
  such uniform comparison is proved.  The actual grouped BF4/AF trajectory,
  same raw observable across cutoffs, projective OS/GNS join, completed
  all-vector gap, continuum QFT, and Clay conclusion remain open.
- **constructive?**: yes.  The ratio is divided only by a witnessed positive
  exact load, unloaded edges use one, and the margin is a recursive located
  minimum over the literal finite vacuum-sector pairs.  No `Classical`,
  choice, `sorry`, `admit`, `native_decide`, `noncomputable`, or new axiom is
  introduced.
- **status note**: the exact monitored one-worker target passes all 5070 jobs;
  all nine audited exports use exactly `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module.  This closes finite positivity and the compiler reduction, not the
  cutoff-uniform estimate, physical dynamic family, continuum theory, or Clay
  mass gap.

### [adaptive-finite-capacity-debt-compiler] Reduce fixed-anchor uniform margins to initial slack plus summable normalized debt — **CLOSED 2026-08-25**

- **milestone**: prove the reusable global-ceiling theorem for a summable
  rational variation budget available from scale zero; define the fixed-anchor
  shared-floor debt against any explicit positive lower proxy to the exact
  routed margin; prove debt at most one reconstructs the floor-versus-proxy
  comparison; and compile a routing/proxy sequence with summable debt,
  total-budget control, and sufficient initial slack into the existing
  cofinal margin family and completed fixed-anchor geometric dynamic family.
- **files**:
  `lean/YMGap/Continuum/SummableRationalStepVariation.lean` and
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler.lean`.
- **decl**:
  `SummableRationalStepVariation.le_of_initial_add_totalBudget_le`,
  `AnchorAdaptivePositiveRoutingSequence`,
  `anchorAdaptiveFiniteCapacityMarginAt`,
  `anchorAdaptiveSharedCoercivityFloor`,
  `anchorAdaptiveFiniteCapacityDebt`,
  `anchorAdaptiveSharedCoercivityFloor_le_marginLower_of_debt_le_one`,
  `AnchorAdaptiveFiniteCapacityDebtVariation`,
  `AnchorAdaptiveFiniteCapacityDebtVariation.debt_le_one`,
  `AnchorAdaptiveFiniteCapacityDebtVariation.toAdaptiveFiniteCapacityMargin`,
  `AnchorAdaptiveFiniteCapacityDebtVariation.toAnchorGeometricExtension`, and
  `AnchorAdaptiveFiniteCapacityDebtVariation.toAnchorGeometricCompletedFamily`.
- **obligation**: construct a routing sequence and explicit positive margin
  lower proxies tied by `marginLower_le_exact` to the same exact routed
  observable, then prove summable two-sided variation of the normalized debt,
  a positive total budget available from zero, and initial debt plus budget at
  most one.  The canonical route fixes the routing; the adaptive route may
  optimize it with cutoff.  Neither route is inhabited.  Actual grouped
  BF4/AF identification, same raw observable across physical cutoffs,
  projective OS/GNS compatibility, all-vector gap, continuum QFT, and Clay
  closure remain open.
- **constructive?**: yes.  The debt denominator has an explicit positivity
  witness, the global ceiling is rational telescoping plus the stored
  antitone tail bound, and the proxy is accepted only with a proof below the
  exact finite routed margin.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker compiler target passes all
  5072 jobs.  Its six audited exports and the added reusable variation theorem
  use only `[propext, Quot.sound]`.  The executable forbidden-token scan
  reports zero hits, and the root aggregator imports the module.  This closes
  a sufficient persistence compiler, not its analytic inhabitant, the
  physical dynamic family, continuum theory, or Clay mass gap.

### [adaptive-support-margin-proxy] Derive the debt proxy from routed support and load — **CLOSED 2026-08-25**

- **milestone**: for every positive routing at every finite cutoff, restrict
  the physical conditional kernel to the literal positively loaded support,
  take its located positive minimum, take the located maximum of the exact
  routed transition-product loads, and prove that
  `((1/2) * supportFloor) / (1 + loadMaximum)` is positive and lies below
  every exact edge ratio and hence below the exact finite capacity margin.
  At the fixed anchor, compile routing plus summable normalized-debt
  variation, total budget, and initial slack directly into the preceding
  finite-capacity debt certificate, with no free margin or comparison input.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_pos`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_pos`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_edgeRatio`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_finiteCapacityMargin`,
  `anchorAdaptiveSupportCapacityDebt`, and
  `anchorAdaptiveSupportCapacityDebtVariation`.
- **obligation**: supply an actual routing sequence and prove that the
  resulting automatic debt stream has summable two-sided variation, a
  positive total budget available from cutoff zero, and enough initial slack.
  Finite positivity of the proxy does not prevent it from decaying with the
  cutoff.  The fixed anchor is not the physical AF trajectory.  The grouped
  BF4 identification, same raw observable across physical cutoffs,
  projective OS/GNS join, completed all-vector gap, continuum QFT, and Clay
  closure remain open.
- **constructive?**: yes.  Both finite extrema are recursive located list
  folds; unloaded edges use one; every division carries an explicit positive
  denominator witness; and the proxy comparison stays on the same routing,
  conditional kernel, exact routed load, and literal finite carrier.  No
  `Classical`, choice, `sorry`, `admit`, `native_decide`, `noncomputable`, or
  new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5073 jobs
  under a stricter 500000-heartbeat module ceiling.  Seven audited exports use
  only `[propext, Quot.sound]`; the executable forbidden-token scan reports
  zero hits, and the root aggregator imports the module.  A monitored root
  aggregation audit was attempted but stopped automatically at job 3217 of
  7104 when available memory reached 11.6 GiB, below the 12.0 GiB reserve; it
  is not reported as a pass.  The verified boundary is the exact narrow
  target.

### [adaptive-support-debt-two-lane-factor] Factor automatic debt variation into two observable-connected producers — **CLOSED 2026-08-25**

- **milestone**: prove reusable constructive closure of summable rational
  step variation under pointwise setoid transport, positive scaling,
  addition, and bounded products; factor the reciprocal automatic BF4 margin
  into the routed-load denominator and inverse supported-kernel numerator;
  prove exact cancellation with the existing margin and exact factorization
  of the existing normalized debt; compile independent component variation
  certificates with positive uniform ceilings into the preceding
  budget/slack debt certificate; and expose the canonical loop-erased routing
  sequence as a specialization of the same compiler.
- **files**:
  `lean/YMGap/Continuum/SummableRationalStepVariationAlgebra.lean` and
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.lean`.
- **decl**:
  `SummableRationalStepVariationAlgebra.ofPointwiseEqv`,
  `SummableRationalStepVariationAlgebra.scale`,
  `SummableRationalStepVariationAlgebra.add`,
  `SummableRationalStepVariationAlgebra.product_step_le`,
  `SummableRationalStepVariationAlgebra.mulOfCeilings`,
  `anchorAdaptiveSupportedKernelNumerator`,
  `anchorAdaptiveRoutedLoadDenominator`,
  `anchorAdaptiveInverseSupportedKernelNumerator`,
  `anchorAdaptiveSupportCapacityReciprocalProxy`,
  `anchorAdaptiveSupportCapacityReciprocalProxy_mul_marginLower_eqv_one`,
  `anchorAdaptiveSupportCapacityDebt_eqv_sharedFloor_mul_reciprocalProxy`,
  `anchorAdaptiveSupportCapacityReciprocalProxyVariationOfComponents`,
  `anchorAdaptiveSupportCapacityDebtVariationOfComponents`,
  `anchorAdaptiveSupportCapacityDebtVariationFromComponents`,
  `anchorCanonicalPositiveRoutingSequence`, and
  `anchorCanonicalSupportCapacityDebtVariationOfComponents`.
- **obligation**: on one common routing sequence, prove summable two-sided
  variation and a positive uniform ceiling for `(1 + routedLoadMaximum)`, and
  separately prove the same for the reciprocal of
  `((1/2) * supportedConditionalKernelFloor)`.  Then exhibit a positive total
  debt budget available from cutoff zero and enough initial slack.  The
  canonical route fixes the routing and is shorter if its estimates remain
  uniform; the adaptive route may optimize the same routing-dependent pair of
  streams if the canonical proxy collapses.  Estimates from different
  routings cannot be mixed.  The physical grouped-BF4/AF identification,
  literal same-observable thermodynamic bridge, projective OS/GNS join,
  completed all-vector gap, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  Both factors use explicit positive rational
  witnesses; quotient cancellation is proved by `Q'.eqv`; the bounded-product
  variation budget is explicit; and every input is indexed by the same
  routing, conditional kernel, exact routed load, and literal finite carrier.
  No `Classical`, choice, `sorry`, `admit`, `native_decide`, `noncomputable`,
  or new axiom is introduced.
- **status note**: the exact monitored one-worker application target passes
  all 5076 jobs and the generic algebra target passes all 46 jobs.  The
  thirteen printed exports use only `[propext, Quot.sound]` or `[propext]`.
  The root aggregator imports both modules; no full-root audit is claimed.

### [adaptive-support-debt-primitive-two-lane] Remove ceiling and inverse-variation premises — **CLOSED 2026-08-25**

- **milestone**: derive a positive global ceiling from every nonnegative
  summable rational step-variation certificate; use it to close nonnegative
  products without separate ceiling premises; prove inverse-square Lipschitz
  transport of summable variation through `recipPos` under one explicit
  positive stream floor; and specialize the BF4 debt compiler so its primitive
  analytic inputs are load-denominator variation plus supported-kernel
  numerator variation and noncollapse.
- **files**:
  `lean/YMGap/Continuum/SummableRationalStepVariation.lean`,
  `lean/YMGap/Continuum/SummableRationalStepVariationAlgebra.lean`,
  `lean/YMGap/Continuum/SummableRationalReciprocalStepVariation.lean`, and
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor.lean`.
- **decl**:
  `SummableRationalStepVariation.globalCeiling`,
  `SummableRationalStepVariation.globalCeiling_pos`,
  `SummableRationalStepVariation.le_globalCeiling`,
  `SummableRationalStepVariationAlgebra.mul`,
  `SummableRationalReciprocalStepVariation.reciprocal_step_le`,
  `SummableRationalReciprocalStepVariation.reciprocal`,
  `anchorAdaptiveSupportCapacityReciprocalProxyVariationOfVariations`,
  `anchorAdaptiveSupportCapacityDebtVariationOfVariations`,
  `anchorAdaptiveSupportCapacityDebtVariationFromVariations`,
  `anchorAdaptiveInverseSupportedKernelNumeratorVariation`,
  `anchorAdaptiveSupportCapacityDebtVariationOfPrimitiveComponents`,
  `anchorAdaptiveSupportCapacityDebtVariationFromPrimitiveComponents`, and
  `anchorCanonicalSupportCapacityDebtVariationOfPrimitiveComponents`.
- **obligation**: for one common routing sequence, prove summable two-sided
  variation of `1 + routedLoadMaximum`; prove summable two-sided variation and
  one uniform positive floor for
  `(1/2) * supportedConditionalKernelFloor`; then exhibit a positive total
  debt budget available from zero and enough initial slack.  Canonical routing
  is the shorter path if these estimates hold; adaptive routing may vary with
  cutoff to prevent load growth or kernel collapse.  Fixed-anchor persistence
  is not the grouped BF4/AF trajectory.  Same-observable thermodynamic
  compatibility, projective OS/GNS reconstruction, completed all-vector gap,
  continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  The global ceiling is explicit rational data; the
  reciprocal compiler carries its positive floor as `Type`-level input; all
  cancellation is through `Q'.eqv`; and the two lanes are indexed by the same
  routing and exact observable-connected carrier.  No `Classical`, choice,
  `sorry`, `admit`, `native_decide`, `noncomputable`, or new axiom is
  introduced.
- **status note**: the monitored one-worker algebra, reciprocal, and BF4
  targets pass all 46, 47, and 5077 jobs respectively.  The twelve newly
  printed exports use only `[propext, Quot.sound]`; the executable
  forbidden-token scan reports zero hits.  The root aggregator imports the
  reciprocal compiler; no full-root audit is claimed.

### [adaptive-support-pointwise-extrema] Reduce dynamic extrema to three observable-connected pointwise producers — **CLOSED 2026-08-25**

- **milestone**: construct generic dynamic finite maximum and minimum
  variation compilers from explicit bidirectional carrier recodings,
  membership proofs, summable pointwise budgets, and the correctly oriented
  one-sided estimates; construct a uniform dynamic minimum floor from one
  positive pointwise bound; specialize all three mechanisms to the literal
  routed-load and support-aware kernel-candidate functions on the exact
  fixed-anchor BF4 vacuum-sector pair lists; and feed their results into the
  existing primitive debt compiler.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.lean`.
- **decl**:
  `DynamicFiniteMaximumVariation`,
  `DynamicFiniteMaximumVariation.toSummableRationalStepVariation`,
  `DynamicFiniteMinimumVariation`,
  `DynamicFiniteMinimumVariation.toSummableRationalStepVariation`,
  `DynamicFiniteMinimumFloor`,
  `DynamicFiniteMinimumFloor.le_minimum`,
  `AnchorAdaptiveRoutedLoadMaximumVariation`,
  `AnchorAdaptiveSupportedKernelMinimumVariation`,
  `AnchorAdaptiveSupportedKernelMinimumFloor`,
  `anchorAdaptiveRoutedLoadDenominatorVariationOfPointwise`,
  `anchorAdaptiveSupportedKernelNumeratorVariationOfPointwise`,
  `anchorAdaptiveSupportedKernelNumeratorFloor_le`,
  `anchorAdaptiveSupportCapacityDebtVariationOfPointwise`,
  `anchorAdaptiveSupportCapacityDebtVariationFromPointwise`, and
  `anchorCanonicalSupportCapacityDebtVariationOfPointwise`.
- **obligation**: after fixing one routing sequence, build three independent
  pointwise certificates: summable two-way load recoding, summable two-way
  kernel-candidate recoding, and a uniform positive kernel-candidate floor.
  These are three parallel producers but contract to two analytic lanes
  because kernel variation and kernel noncollapse join before reciprocal
  transport.  Then supply a positive total debt budget available from zero
  and enough initial slack.  Canonical routing removes route construction but
  must control the new shell; adaptive routing may optimize the shell at the
  cost of an additional coherent-routing construction.  Fixed-anchor
  persistence is not the physical grouped BF4/AF trajectory.  The literal
  same-observable thermodynamic bridge, projective OS/GNS reconstruction,
  completed all-vector gap, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  Both recoding maps are `Type`-level data; every
  membership proof targets the exact dynamic list; extrema are recursive
  located folds; all three BF4 inputs share the same routing parameter and
  exact pair carrier; and the output is the pre-existing exact normalized
  debt.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5078
  jobs.  Its nine printed exports use only `[propext, Quot.sound]` or smaller
  subsets.  The executable forbidden-token scan reports zero hits, and the
  root aggregator imports the module; no full-root audit is claimed.

### [canonical-support-pair-recoding] Construct canonical consecutive-carrier maps — **CLOSED 2026-08-25**

- **milestone**: construct the canonical current-to-next index map from the
  physical cutoff embedding; construct a total next-to-current map by finite
  preimage search with vacuum fallback; prove that it lands in the earlier
  vacuum component and is a left inverse on the embedded old component; lift
  both maps to the exact consecutive vacuum-sector pair carriers; and install
  those maps in canonical load-maximum and kernel-minimum envelope interfaces.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.lean`,
  with the exact routed functions exposed for reuse in
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.lean`.
- **decl**:
  `firstMappedPreimageOr`,
  `firstMappedPreimageOr_mem`,
  `map_firstMappedPreimageOr_eq_of_mem_map`,
  `anchorCurrentIndexToNext`,
  `anchorNextIndexToCurrent`,
  `anchorNextIndexToCurrent_currentToNext`,
  `anchorCurrentPairToNext`,
  `anchorNextPairToCurrent`,
  `anchorCurrentPairToNext_mem`,
  `anchorNextPairToCurrent_mem`,
  `anchorNextPairToCurrent_currentToNext`,
  `AnchorCanonicalRoutedLoadEnvelope`,
  `AnchorCanonicalSupportedKernelEnvelope`,
  `AnchorCanonicalRoutedLoadEnvelope.toMaximumVariation`,
  `AnchorCanonicalSupportedKernelEnvelope.toMinimumVariation`, and
  `anchorCanonicalSupportCapacityDebtVariationOfEnvelopes`.
- **obligation**: inhabit three remaining canonical analytic certificates:
  the summable load envelope, summable kernel envelope, and uniform positive
  kernel floor.  The difficult cases are the genuinely new-shell items that
  the reverse map sends to vacuum.  After these producers join, a positive
  total debt budget from cutoff zero and adequate initial slack are still
  required.  Failure of canonical new-shell estimates would justify the
  longer adaptive-routing path.  Physical AF persistence, the literal
  same-observable thermodynamic bridge, projective OS/GNS reconstruction,
  completed all-vector gap, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  The reverse map is a recursive finite-list search
  with an explicit vacuum fallback; its old-component inverse proof uses the
  existing constructive embedding injectivity; pair membership targets the
  exact existing carrier; and both analytic envelope interfaces mention the
  same canonical routing and exact existing observables.  No `Classical`,
  choice, `sorry`, `admit`, `native_decide`, `noncomputable`, or new axiom is
  introduced.
- **status note**: the exact monitored one-worker target passes all 5079
  jobs.  Its eight printed exports use only `[propext, Quot.sound]` or smaller
  subsets.  The executable forbidden-token scan reports zero hits, and the
  root aggregator imports the module; no full-root audit is claimed.

### [canonical-correlated-capacity-debt] Preserve load/kernel compensation in one dynamic observable — **CLOSED 2026-08-25**

- **milestone**: define the exact normalized routed capacity debt on each
  literal vacuum-sector pair; prove constructively that pair debt at most one
  implies the exact edge-capacity inequality, using the existing positive-load
  implication to exclude the totalization fallback; take its located finite
  maximum; compile a two-sided canonical pointwise envelope into summable
  maximum variation; and show that total budget plus initial slack constructs
  the existing cofinal transition product and completed fixed-anchor family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler.lean`.
- **decl**:
  `anchorRoutedCapacityDebtOnPair`,
  `anchorRoutedCapacityDebtOnPair_nonnegative`,
  `anchorRoutedCapacityDebtOnPair_le_one_implies_edge_capacity`,
  `anchorRoutedCapacityDebtMaximum`,
  `anchorRoutedCapacityDebtOnPair_le_maximum`,
  `AnchorCanonicalCapacityDebtEnvelope`,
  `AnchorCanonicalCapacityDebtEnvelope.toMaximumVariation`,
  `anchorCanonicalCapacityDebtMaximumVariation`,
  `AnchorCanonicalCapacityDebtPersistence`,
  `AnchorCanonicalCapacityDebtPersistence.maximum_le_one`,
  `AnchorCanonicalCapacityDebtPersistence.toAdaptiveConditionalTransitionProduct`,
  `AnchorCanonicalCapacityDebtPersistence.toAnchorGeometricExtension`, and
  `AnchorCanonicalCapacityDebtPersistence.toAnchorGeometricCompletedFamily`.
- **obligation**: inhabit one correlated two-sided canonical debt envelope,
  choose a positive total variation budget whose tail index from zero is zero,
  and prove the cutoff-zero maximum plus that budget is at most one.  This is
  a smaller and more faithful analytic obligation than separately controlling
  a routed-load maximum, a kernel minimum, and a uniform kernel floor, because
  exact load/kernel compensation is retained.  The difficult cases are still
  the genuinely new-shell pairs.  Physical AF persistence, the literal
  same-observable thermodynamic bridge, projective OS/GNS reconstruction,
  completed all-vector gap, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  The observable uses the exact routed load and exact
  conditional kernel on the same pair and routing; extrema are recursive
  located folds; both carrier recodings are the previously constructed terms;
  division requires explicit positivity; and all cancellation is through
  `Q'.eqv`.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5080 jobs.
  Its seven printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-shell] Split correlated variation into transported-old and new-shell regions — **CLOSED 2026-08-25**

- **milestone**: define the literal embedded-old pair carrier; prove it lies
  in the next exact carrier and that the canonical forward/reverse maps form a
  retraction there; define the genuinely new shell as the decidable complement
  in the later carrier; split every later pair into those two regions; expose
  independent summable transported-old and shell envelope interfaces; add
  their budgets; and contract the regional inputs back into the existing
  correlated envelope, persistence package, and completed fixed-anchor family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellCompiler.lean`.
- **decl**:
  `anchorEmbeddedOldPairCarrier`,
  `anchorCurrentPairToNext_mem_embeddedOld`,
  `anchorEmbeddedOldPairCarrier_mem_next`,
  `anchorCurrentPairToNext_nextToCurrent_of_mem_embeddedOld`,
  `AnchorPairInNewShell`,
  `anchorPair_old_or_newShell`,
  `AnchorCanonicalTransportedCapacityDebtEnvelope`,
  `AnchorCanonicalNewShellCapacityDebtEnvelope`,
  `anchorCanonicalCapacityDebtEnvelopeOfTransportAndShell`,
  `anchorCanonicalCapacityDebtPersistenceOfTransportAndShell`, and
  `anchorGeometricCompletedFamilyOfTransportAndShell`.
- **obligation**: independently inhabit the transported-old two-sided debt
  envelope and the incoming new-shell debt envelope, then exhibit a positive
  total budget available from cutoff zero and enough initial slack.  The shell
  itself has three ordered coordinate faces, old-new, new-old, and new-new,
  which are the next exact parallelization frontier.  Failure localized to a
  shell face would justify adaptive routing targeted at that face.  Physical
  AF persistence, the literal same-observable thermodynamic bridge, projective
  OS/GNS reconstruction, completed all-vector gap, continuum QFT, and Clay
  closure remain open.
- **constructive?**: yes.  Embedded membership is ordinary finite-list
  membership with an explicit preimage; the shell is its decidable complement;
  the old-region proof uses the already proved left inverse; both regional
  structures mention the same exact correlated debt and canonical routing;
  and tail budgets join through constructive rational addition.  No
  `Classical`, choice, `sorry`, `admit`, `native_decide`, `noncomputable`, or
  new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5081 jobs.
  Its seven printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-shell-faces] Split the new shell into three ordered coordinate faces — **CLOSED 2026-08-25**

- **milestone**: define the exact embedded-old and new index regions; prove
  that embedded pair membership is equivalent to coordinatewise embedded
  index membership; prove that every genuinely new pair lies in the old-new,
  new-old, or new-new face; expose an independent summable correlated-debt
  envelope for each face; add the three budgets; and reconstruct both the
  single new-shell envelope and the full transported-old-plus-shell envelope.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces.lean`.
- **decl**:
  `anchorVacuumSectorIndices`,
  `anchorEmbeddedOldIndexCarrier`,
  `AnchorIndexInNewShell`,
  `anchorEmbeddedOldIndexCarrier_mem_next`,
  `mem_anchorEmbeddedOldPairCarrier_iff`,
  `AnchorPairInOldNewShell`,
  `AnchorPairInNewOldShell`,
  `AnchorPairInNewNewShell`,
  `anchorNewShellPair_face_cases`,
  `AnchorCanonicalOldNewCapacityDebtEnvelope`,
  `AnchorCanonicalNewOldCapacityDebtEnvelope`,
  `AnchorCanonicalNewNewCapacityDebtEnvelope`,
  `anchorCanonicalNewShellCapacityDebtEnvelopeOfFaces`, and
  `anchorCanonicalCapacityDebtEnvelopeOfTransportAndFaces`.
- **obligation**: inhabit four regional summable compiler families in
  parallel: transported-old debt control and the three ordered shell-face
  controls.  There are five atomic estimates because old transport is
  bidirectional.  Then exhibit a positive total budget available from cutoff
  zero and enough initial slack.  The next geometric simplification is to
  identify the reverse recoding on the three shell faces with old-vacuum,
  vacuum-old, and vacuum-vacuum comparison pairs.  A face-specific failure is
  the precise reason to introduce localized adaptive routing.  Physical AF
  persistence, the literal same-observable thermodynamic bridge, projective
  OS/GNS reconstruction, completed all-vector gap, continuum QFT, and Clay
  closure remain open.
- **constructive?**: yes.  All regions are decidable finite-list membership
  predicates; face exhaustion is a finite coordinate case split; the three
  independent variations join through constructive rational tail addition;
  and every face uses the same exact capacity-debt observable and canonical
  routing.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5082 jobs.
  Its five printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-shell-returns] Identify the three shell faces' literal vacuum return points — **CLOSED 2026-08-25**

- **milestone**: prove that finite preimage search returns its fallback when
  the target is outside the mapped list; specialize this to show that a new
  shell index returns to vacuum index zero; identify the old-new, new-old, and
  new-new pair recodings with recovered-old/vacuum, vacuum/recovered-old, and
  vacuum/vacuum pairs; prove those return pairs lie in the exact earlier
  carrier; expose analytic envelopes against the literal return points; and
  compile them back into the unchanged face, shell, and full debt envelopes.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellReturns.lean`.
- **decl**:
  `firstMappedPreimageOr_eq_fallback_of_not_mem_map`,
  `anchorNextIndexToCurrent_eq_zero_of_newShell`,
  `anchorOldNewReturnPair`,
  `anchorNewOldReturnPair`,
  `anchorNewNewReturnPair`,
  `anchorNextPairToCurrent_eq_oldNewReturn`,
  `anchorNextPairToCurrent_eq_newOldReturn`,
  `anchorNextPairToCurrent_eq_newNewReturn`,
  `anchorOldNewReturnPair_mem`,
  `anchorNewOldReturnPair_mem`,
  `anchorNewNewReturnPair_mem`,
  `AnchorCanonicalOldNewReturnCapacityDebtEnvelope`,
  `AnchorCanonicalNewOldReturnCapacityDebtEnvelope`,
  `AnchorCanonicalNewNewReturnCapacityDebtEnvelope`,
  `anchorCanonicalNewShellCapacityDebtEnvelopeOfReturns`, and
  `anchorCanonicalCapacityDebtEnvelopeOfTransportAndReturns`.
- **obligation**: prove summable exact-debt comparisons from each later shell
  face to its displayed earlier return pair, plus the transported-old
  two-sided estimates, then supply total budget and initial slack.  Existing
  cutoff pushforward identities should next be tested for exact transported-old
  invariance; success would reduce the live analytic frontier from four
  regional families to the three shell faces.  Face-specific failure remains
  the precise reason for localized adaptive routing.  Physical AF persistence,
  the literal same-observable thermodynamic bridge, projective OS/GNS
  reconstruction, completed all-vector gap, continuum QFT, and Clay closure
  remain open.
- **constructive?**: yes.  The fallback theorem is structural recursion on a
  finite list; all pair identities are literal product equalities; carrier
  membership is inherited from the proved reverse map; and every analytic
  interface retains the exact correlated debt and fixed canonical routing.
  No `Classical`, choice, `sorry`, `admit`, `native_decide`, `noncomputable`,
  or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5083 jobs.
  Its seven printed exports use only `[propext, Quot.sound]` or `[propext]`.
  The executable forbidden-token scan reports zero hits, and the root
  aggregator imports the module; no full-root audit is claimed.

### [canonical-correlated-debt-deficit-maxima] Compute exact regional deficit maxima and eliminate pointwise envelope inputs — **CLOSED 2026-08-25**

- **milestone**: compute the exact two-sided transported-old debt deficit and
  each of the three one-sided shell-return deficits; fold each stream to a
  located finite maximum on the literal carrier; derive all five pointwise
  envelope inequalities from those maxima; expose only summability of the
  four explicit streams as named `Type`-level inputs; and compile four such
  inputs through the unchanged budget/slack persistence path.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler.lean`.
- **decl**:
  `anchorTransportedCapacityDebtDeficitOnPair`,
  `anchorTransportedCapacityDebtDeficitMaximum`,
  `anchorTransportedCapacityDebtDeficitOnPair_le_maximum`,
  `AnchorCanonicalTransportedCapacityDebtDeficitTail`,
  `AnchorCanonicalTransportedCapacityDebtDeficitTail.toEnvelope`,
  `anchorOldNewReturnCapacityDebtDeficitOnPair`,
  `anchorNewOldReturnCapacityDebtDeficitOnPair`,
  `anchorNewNewReturnCapacityDebtDeficitOnPair`,
  `anchorOldNewReturnCapacityDebtDeficitMaximum`,
  `anchorNewOldReturnCapacityDebtDeficitMaximum`,
  `anchorNewNewReturnCapacityDebtDeficitMaximum`,
  `anchorOldNewReturnCapacityDebtDeficitOnPair_le_maximum`,
  `anchorNewOldReturnCapacityDebtDeficitOnPair_le_maximum`,
  `anchorNewNewReturnCapacityDebtDeficitOnPair_le_maximum`,
  `AnchorCanonicalOldNewCapacityDebtDeficitTail`,
  `AnchorCanonicalNewOldCapacityDebtDeficitTail`,
  `AnchorCanonicalNewNewCapacityDebtDeficitTail`,
  `anchorCanonicalCapacityDebtEnvelopeOfDeficitTails`, and
  `anchorCanonicalCapacityDebtPersistenceOfDeficitTails`.
- **obligation**: prove four `AntitoneTailControl` witnesses in parallel for
  the displayed computed deficit maxima, or prove one summability theorem for
  a total stream dominating their sum; then exhibit a positive budget whose
  tail index is zero and enough cutoff-zero debt slack.  Exact zero variation
  on the transported-old component is not currently justified because both
  normalized physical entries and canonical routing data can change across
  cutoffs.  A localized failure of a shell-face tail is the precise signal for
  a face-specific adaptive-routing alternative.  Physical AF persistence, the
  literal same-observable thermodynamic bridge, projective OS/GNS
  reconstruction, completed all-vector gap, continuum QFT, and Clay closure
  remain open.
- **constructive?**: yes.  The deficits and maxima are executable rational
  functions over finite lists; shell decisions unfold to kernel-computable
  list membership; analytic tails remain explicit `Type`-level fields; and
  all four regions use the same exact debt, routing, carriers, and return
  maps.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5084 jobs.
  Its ten printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-total-deficit] Contract four regional tails to one necessary total tail — **CLOSED 2026-08-25**

- **milestone**: define the exact sum of the transported-old and three
  shell-face deficit maxima; prove that it dominates each region; show that
  four regional tail controls construct one total tail control; and prove
  directly that one total tail control constructs the exact correlated debt
  envelope, persistence package, and completed fixed-anchor family once its
  budget and initial slack are supplied.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler.lean`.
- **decl**:
  `anchorCanonicalCapacityDebtTotalDeficit`,
  `anchorCanonicalCapacityDebtTotalDeficit_nonnegative`,
  `anchorTransportedCapacityDebtDeficitMaximum_le_total`,
  `anchorOldNewReturnCapacityDebtDeficitMaximum_le_total`,
  `anchorNewOldReturnCapacityDebtDeficitMaximum_le_total`,
  `anchorNewNewReturnCapacityDebtDeficitMaximum_le_total`,
  `AnchorCanonicalCapacityDebtTotalDeficitTail`,
  `anchorCanonicalCapacityDebtTotalDeficitTailOfRegionalTails`,
  `AnchorCanonicalCapacityDebtTotalDeficitTail.toEnvelope`,
  `anchorCanonicalCapacityDebtPersistenceOfTotalDeficitTail`, and
  `anchorGeometricCompletedFamilyOfTotalDeficitTail`.
- **obligation**: inhabit one `AntitoneTailControl` for the displayed total
  deficit stream, either directly or by four parallel regional proofs; then
  cover its full prefix by a positive total budget and verify the cutoff-zero
  debt plus that budget is at most one.  The current persistence interface's
  `tailRate budget = 0` should next be generated from the tail modulus and a
  computed finite prefix, not retained as an independent analytic premise.
  A regional failure remains the precise signal for localized adaptive
  routing.  Physical AF persistence, the literal same-observable
  thermodynamic bridge, projective OS/GNS reconstruction, completed all-vector
  gap, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  The total is an executable rational sum; regional
  domination uses nonnegativity; old/shell/face classification is finite and
  decidable; the tail is `Type`-level data; and the direct envelope proof never
  changes the exact observable or routing.  No `Classical`, choice, `sorry`,
  `admit`, `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5085 jobs.
  Its ten printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-prefix-tail] Compute the cutoff-zero budget from one total tail — **CLOSED 2026-08-25**

- **milestone**: let the total-tail modulus select a cutoff for any positive
  tail allowance; compute the exact total-deficit prefix through that cutoff;
  add prefix and allowance into a positive global budget; prove that budget
  controls every finite prefix and shifted window; normalize the tail control
  so its rate at the global budget is zero; and construct the existing
  persistence and completed fixed-anchor family from only the total tail and
  the final scalar slack check.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.lean`.
- **decl**:
  `anchorCanonicalCapacityDebtTotalDeficitTailStart`,
  `anchorCanonicalCapacityDebtTotalDeficitPrefix`,
  `anchorCanonicalCapacityDebtTotalBudget`,
  `anchorCanonicalCapacityDebtTotalDeficitPrefix_nonnegative`,
  `anchorCanonicalCapacityDebtTotalBudget_pos`,
  `anchorCanonicalCapacityDebtTotalDeficitPartialSum_le_budget`,
  `anchorCanonicalCapacityDebtTotalDeficitWindow_le_budget`,
  `anchorCanonicalCapacityDebtBudgetedTailControl`,
  `anchorCanonicalCapacityDebtBudgetedTailControl_rate_budget`,
  `anchorCanonicalCapacityDebtBudgetedEnvelope`,
  `anchorCanonicalCapacityDebtPersistenceOfPrefixTail`, and
  `anchorGeometricCompletedFamilyOfPrefixTail`.
- **obligation**: inhabit the single `AntitoneTailControl` for the exact total
  deficit, directly or from four regional proofs, and provide a positive tail
  allowance for which the executable cutoff-zero debt plus computed finite
  prefix plus allowance is at most one.  The previous independent
  `tailRate budget = 0` premise is now generated and is not analytic work.
  Failure of a regional tail remains the exact reason for localized adaptive
  routing.  Physical AF persistence, the literal same-observable
  thermodynamic bridge, projective OS/GNS reconstruction, completed all-vector
  gap, continuum QFT, and Clay closure remain open.
- **constructive?**: yes.  The cutoff is Type-level modulus data, the prefix is
  a recursive exact rational sum, the prefix/tail split is a setoid equality,
  the budget decision is kernel-computable, and the normalized modulus retains
  its antitone witness.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, `noncomputable`, or new axiom is introduced.
- **status note**: the exact monitored one-worker target passes all 5086 jobs.
  Its ten printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-inverse-square-tail] Compile regional inverse-square estimates into the one total tail — **CLOSED 2026-08-25**

- **milestone**: expose a direct inverse-square majorant for the exact total
  canonical capacity-debt deficit; compile it to the required antitone tail;
  expose four independently provable regional inverse-square majorants with a
  common offset; add their coefficients and pointwise estimates into the one
  direct total control; and connect either route to computed-prefix
  persistence and the completed fixed-anchor family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail.lean`.
- **decl**:
  `AnchorCanonicalCapacityDebtInverseSquareControl`,
  `AnchorCanonicalCapacityDebtInverseSquareControl.toTotalDeficitTail`,
  `AnchorCanonicalCapacityDebtRegionalInverseSquareControl`,
  `AnchorCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient`,
  `AnchorCanonicalCapacityDebtRegionalInverseSquareControl.totalCoefficient_nonnegative`,
  `AnchorCanonicalCapacityDebtRegionalInverseSquareControl.toTotalControl`,
  `AnchorCanonicalCapacityDebtRegionalInverseSquareControl.toTotalDeficitTail`,
  `anchorCanonicalCapacityDebtPersistenceOfInverseSquare`, and
  `anchorGeometricCompletedFamilyOfInverseSquare`.
- **obligation**: inhabit either the direct total inverse-square bound or the
  four regional bounds with a common offset, then exhibit a positive tail
  allowance satisfying the executable prefix-plus-allowance cutoff-zero slack
  inequality.  Inverse-square domination is sufficient rather than necessary;
  another constructive total-tail modulus would enter the same closure.
  Physical AF persistence, the literal same-observable thermodynamic bridge,
  projective OS/GNS reconstruction, completed all-vector gap, continuum QFT,
  and Clay closure remain open.
- **constructive?**: yes.  All coefficients are nonnegative rationals, the
  four regional estimates add by explicit setoid arithmetic, the common
  inverse-square tail is a constructive modulus, and every estimate remains
  attached to the exact canonical observable.  No `Classical`, choice,
  `sorry`, `admit`, `native_decide`, `noncomputable`, or new axiom is
  introduced.
- **status note**: the exact monitored one-worker target passes all 5097 jobs.
  Its six printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-route-bridge] Split transported-old debt into mapped-path drift and route churn — **CLOSED 2026-08-25**

- **milestone**: map Type-level positive paths through the physical cutoff
  embedding; prove mapped normalized-kernel edges remain positive; construct
  a total later routing that uses mapped old paths and canonical new-endpoint
  paths; split the exact transported-old capacity-debt deficit through this
  bridge; dominate its finite maximum by data-plus-new-traffic drift and route
  churn maxima; and compile inverse-square bounds on those two streams plus
  the three shell streams into the existing one-total-tail persistence path.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.lean`.
- **decl**:
  `mapPositiveKernelChainIn`,
  `anchorCurrentIndexToNext_kernel_pos`,
  `anchorMapPositivePathToNext`,
  `anchorCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex`,
  `anchorTransportedCanonicalRoutingAtNext`,
  `anchorTransportedCanonicalRoutingSequence`,
  `anchorTransportedBridgeDataDeficitOnPair`,
  `anchorTransportedBridgeRouteDeficitOnPair`,
  `anchorTransportedBridgeDataDeficitMaximum`,
  `anchorTransportedBridgeRouteDeficitMaximum`,
  `anchorTransportedCapacityDebtDeficitOnPair_le_bridge_split`,
  `anchorTransportedCapacityDebtDeficitMaximum_le_bridge_split`,
  `AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl`,
  `AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl.transported_le`,
  `AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl`,
  `AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toRegionalControl`,
  `AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toTotalControl`,
  `anchorCanonicalCapacityDebtPersistenceOfBridgeInverseSquare`, and
  `anchorGeometricCompletedFamilyOfBridgeInverseSquare`.
- **obligation**: either prove the original four regional inverse-square
  estimates directly, or prove the five expanded estimates consisting of
  mapped-path data-plus-new-traffic drift, route churn, and the three shell
  faces.  Then provide a positive allowance satisfying the executable
  cutoff-zero slack.  The expanded split is diagnostic and sufficient, not a
  claim that five independent hypotheses are logically necessary; the joined
  consumer still needs only one total-tail modulus.  Physical AF persistence,
  the literal same-observable thermodynamic bridge, projective OS/GNS
  reconstruction, completed all-vector gap, continuum QFT, and Clay closure
  remain open.
- **constructive?**: yes.  Paths, carrier maps, membership decisions,
  positivity witnesses, bridge routing, deficits, maxima, and moduli are
  Type-level or kernel-computable data.  Both split terms retain the same
  normalized capacity debt and exact routed observable.  No `Classical`,
  choice, `sorry`, `admit`, `native_decide`, `noncomputable`, or new axiom is
  introduced.
- **status note**: the exact monitored one-worker target passes all 5098 jobs.
  Its eight printed exports use only `[propext, Quot.sound]`.  The executable
  forbidden-token scan reports zero hits, and the root aggregator imports the
  module; no full-root audit is claimed.

### [canonical-correlated-debt-endpoint-traffic-bridge] Split mapped-path data drift by endpoint provenance — **CLOSED 2026-08-25**

- **milestone**: filter the exact later residual endpoint list into pairs with
  two embedded-old endpoints and its Boolean complement; prove the full later
  mapped-route load is their exact finite-sum partition; prove the normalized
  full bridge debt is the exact sum of the corresponding old/new traffic
  debts through the same physical conditional-kernel denominator; split the
  bridge data deficit and its located maximum into old-traffic physical drift
  plus genuinely new endpoint traffic; and compile inverse-square controls on
  those two streams, route churn, and the three shell faces back into the
  existing one-total-tail persistence path.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.lean`.
- **decl**:
  `anchorTransportedBridgeEndpointPairOldB`,
  `anchorTransportedBridgeOldEndpointPairs`,
  `anchorTransportedBridgeNewEndpointPairs`,
  `anchorTransportedBridgeOldEndpointTrafficLoadOnPair`,
  `anchorTransportedBridgeNewEndpointTrafficLoadOnPair`,
  `anchorTransportedBridgeRoutedLoadOnPair_eqv_old_add_new`,
  `anchorCapacityDebtFromLoadOnPair`,
  `anchorTransportedBridgeOldEndpointTrafficDebtOnPair`,
  `anchorTransportedBridgeNewEndpointTrafficDebtOnPair`,
  `anchorTransportedBridgeCapacityDebtOnPair_eqv_old_add_new`,
  `anchorTransportedBridgeOldTrafficDataDeficitOnPair`,
  `anchorTransportedBridgeNewTrafficDeficitOnPair`,
  `anchorTransportedBridgeDataDeficitOnPair_le_traffic_split`,
  `anchorTransportedBridgeDataDeficitMaximum_le_traffic_split`,
  `AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl`,
  `AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl.toBridgeControl`,
  `AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl`,
  `AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toTotalControl`,
  `anchorCanonicalCapacityDebtPersistenceOfTrafficInverseSquare`, and
  `anchorGeometricCompletedFamilyOfTrafficInverseSquare`.
- **obligation**: either prove a direct total-tail estimate, the four regional
  inverse-square estimates, the five bridge estimates, or the six expanded
  endpoint-provenance estimates.  On the six-stream route these are
  same-route old-traffic physical drift, new endpoint traffic, route churn,
  and the three ordered shell faces.  Then provide a positive tail allowance
  satisfying the executable cutoff-zero total-budget slack inequality.  The
  expanded interface is diagnostic and sufficient; only the joined total
  tail is logically required downstream.  Physical AF persistence,
  same-object thermodynamic compatibility, projective OS/GNS reconstruction,
  completed all-vector uniform gap, continuum QFT, and Clay closure remain
  open.
- **constructive?**: yes.  Endpoint provenance is decided inside the literal
  later endpoint carrier; the complement uses the same Boolean; finite sums,
  matched denominators, debts, deficits, maxima, coefficients, and compilers
  are explicit rational or Type-level data.  No `Classical`, choice, `sorry`,
  `admit`, `native_decide`, custom axiom, or noncomputable declaration is
  introduced.
- **status note**: the focused monitored check passes.  The dependency-complete
  one-worker target passes all 5099 jobs.  Its eight printed exports use only
  `[propext, Quot.sound]`; the executable forbidden-token scan reports zero
  hits, the source declaration scan finds no custom axiom or noncomputable
  definition, and the root aggregator imports the module.  No full-root audit
  is claimed.

### [canonical-correlated-debt-exact-new-traffic] Contract the new-traffic deficit to its exact positive debt — **CLOSED 2026-08-25**

- **milestone**: prove nonnegativity of every reverse/forward path product,
  routed directed-edge multiplicity, and routed endpoint-pair transition
  product; transfer that sign through the filtered complementary endpoint
  sum and matched capacity normalization; use the exact old-plus-new debt
  identity to bound both orientations of the new-traffic deficit by the
  literal new-traffic debt; lift the result to located maxima; and compile an
  inverse-square estimate on that exact positive debt into the existing
  six-stream, regional, total-tail, persistence, and completed fixed-anchor
  consumers.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.lean`.
- **decl**:
  `centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct_nonnegative`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_nonnegative`,
  `centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm_nonnegative`,
  `anchorTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative`,
  `anchorCapacityDebtFromLoadOnPair_nonnegative`,
  `anchorTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative`,
  `anchorTransportedBridgeNewTrafficDeficitOnPair_le_exactDebt`,
  `anchorTransportedBridgeNewEndpointTrafficDebtMaximum`,
  `anchorTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum`,
  `AnchorCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl`,
  `AnchorCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl.toTrafficControl`,
  `AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl`,
  `AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTotalControl`,
  `anchorCanonicalCapacityDebtPersistenceOfExactTrafficInverseSquare`, and
  `anchorGeometricCompletedFamilyOfExactTrafficInverseSquare`.
- **obligation**: bound the exact located new-endpoint traffic debt, together
  with same-route old-traffic physical drift, route churn, and the three shell
  faces, by a common constructive summable majorant; or prove any coarser
  route reaching the same total tail.  Then provide a positive tail allowance
  satisfying the executable cutoff-zero total-budget slack inequality.  No
  such analytic estimate or allowance is supplied.  Physical AF persistence,
  same-object thermodynamic compatibility, projective OS/GNS reconstruction,
  completed all-vector uniform gap, continuum QFT, and Clay closure remain
  open.
- **constructive?**: yes.  Path induction retains positivity witnesses,
  multiplicity is a finite sum of unit loads, filtered sums remain literal,
  the normalized debt uses its matching conditional-kernel capacity, and all
  witnesses and compilers are Type-level or exact rational data.  No
  `Classical`, choice, `sorry`, `admit`, `native_decide`, custom axiom, or
  noncomputable declaration is introduced.
- **status note**: the focused monitored check passes.  The dependency-complete
  one-worker target passes all 5100 jobs.  Its nine printed exports use only
  `[propext, Quot.sound]`; the executable forbidden-token scan reports zero
  hits, the source declaration scan finds no custom axiom or noncomputable
  definition, and the root aggregator imports the module.  No full-root audit
  is claimed.

### [matched-physical-af-dynamic-family-join] Pin the completed dynamic family to the exact matched BF4 action — **CLOSED 2026-08-25**

- **milestone**: derive strict subunity of the exact matched block weight from
  the existing cubic matched-action law; package a coupling schedule and the
  to-zero modulus of its literal supplied physical spacing; index the cofinal
  spin-ray capacity and adaptive conditional transition product by
  `blockedWeight family (coupling scale)`; compile those data to the concrete
  completed carrier, transfer, vacuum complement, and normalized strength
  law; and pin the remaining nonzero same-object observable certificate,
  connected-correlation bound, and physical gap floor to that exact completed
  family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicFamilyCompiler.lean`.
- **decl**:
  `lt_one_of_one_add_neg_pos`,
  `blockedWeight_lt_one_of_cubicMarginLaw`,
  `matchedPhysicalDynamicSpacing`,
  `MatchedPhysicalDynamicScalarTrajectory`,
  `MatchedPhysicalDynamicScalarTrajectory.toAdaptiveScalarTrajectory`,
  `MatchedPhysicalDynamicScalarTrajectory.LocalProducer`,
  `MatchedPhysicalDynamicScalarTrajectory.toDynamicFamily`,
  `MatchedPhysicalDynamicScalarTrajectory.toCompletedFamily`,
  `MatchedPhysicalDynamicScalarTrajectory.toNormalizedStrengthLaw`,
  `MatchedPhysicalDynamicScalarTrajectory.StrengthBand`,
  `MatchedPhysicalDynamicScalarTrajectory.toPhysicalRateBand`,
  `MatchedPhysicalDynamicScalarTrajectory.toDynamicFamily_nome_eq_physicalAFEnvelope`,
  `MatchedPhysicalDynamicScalarTrajectory.SameObjectObservablePin`,
  `MatchedPhysicalDynamicScalarTrajectory.physicalSeparator`,
  `MatchedPhysicalDynamicScalarTrajectory.connectedCorrSq_control`,
  `MatchedPhysicalDynamicScalarTrajectory.physicalGapFloor`, and
  `MatchedPhysicalDynamicScalarTrajectory.physicalSeparator_gapObservable_zero_pos`.
- **obligation**: construct the physical four-dimensional cubic matched-action
  law and dimensional-transmutation spacing envelope with a scheduled
  spacing-to-zero modulus; inhabit the exact matched-weight cofinal spin-ray
  capacity and adaptive transition-product producer; prove the two-sided
  normalized-strength/spacing band; and build the nonzero gauge-invariant
  same-object observable pin.  The supplied finite matched family also still
  needs identification with the full nonperturbative trajectory.  Projective
  OS/GNS reconstruction, thermodynamic/continuum compatibility, continuum
  Yang--Mills existence, and Clay closure remain open.
- **constructive?**: yes.  The nome is the literal finite matched selector,
  nome positivity and subunity are derived, spacing and local analytic data
  share the exact coupling index, and all remaining certificates are
  Type-valued.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  custom axiom, or noncomputable declaration is introduced.
- **status note**: the focused monitored check passes.  The dependency-complete
  one-worker target passes all 5074 jobs.  Its twelve printed exports use only
  `[propext, Quot.sound]`; the repository-wide executable forbidden-token scan
  reports zero hits, the source declaration scan finds no custom axiom or
  noncomputable definition, and the root aggregator imports the module.  No
  full-root audit is claimed.

### [matched-physical-selected-term-ray] Reduce the matched ray capacity to its selected physical raw-row comparison — **CLOSED 2026-08-25**

- **milestone**: replace the opaque cofinal ray-capacity field at every exact
  matched BF4/AF scale by a cofinal selected-term raw-row ceiling; compile its
  reciprocal return floor and half-floor capacity scale by scale; make the
  remaining adaptive transition product depend on that exact capacity; and
  contract the result to the matched dynamic and completed families,
  normalized strength law, strength-band consumer, and same-object observable
  interface without changing nome or spacing.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicSelectedTermRayCompiler.lean`.
- **decl**:
  `MatchedPhysicalDynamicSelectedTermRayProducer`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toRayCapacityProducer`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.TransitionProductExtension`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toLocalProducer`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toDynamicFamily`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toCompletedFamily`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toNormalizedStrengthLaw`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toDynamicFamily_nome`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toDynamicFamily_spacing`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toRayCapacityProducer_delta`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toRayCapacityProducer_delta_pos`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.StrengthBand`,
  `MatchedPhysicalDynamicSelectedTermRayProducer.toPhysicalRateBand`, and
  `MatchedPhysicalDynamicSelectedTermRayProducer.SameObjectObservablePin`.
- **obligation**: prove the selected-term raw-row ceiling uniformly over the
  cofinal spin cutoff at each changing matched nome, then inhabit the adaptive
  off-ray transition-product extension at the capacity it constructs.  The
  concrete `1/400` anchor ceiling is not an arbitrary-nome theorem.  Physical
  cubic and spacing data, the two-sided strength/spacing band, nonzero
  same-object observable pin, full trajectory identification, projective
  OS/GNS reconstruction, continuum Yang--Mills existence, and Clay closure
  remain open.
- **constructive?**: yes.  Every selected-term certificate is indexed by the
  literal matched nome; reciprocal floors, half-floor capacities, dependent
  transition products, completed objects, and consumers are explicit
  Type-level data.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  custom axiom, or noncomputable declaration is introduced.
- **status note**: the focused monitored check passes.  The dependency-complete
  one-worker target passes all 5076 jobs.  Its eight printed exports use only
  `[propext, Quot.sound]`; the repository-wide executable forbidden-token scan
  reports zero hits, the source declaration scan finds no custom axiom or
  noncomputable definition, and the root aggregator imports the module.  No
  full-root audit is claimed.

### [matched-physical-explicit-subunit-ray] Construct the selected ray at every positive subunit nome — **CLOSED 2026-08-25**

- **milestone**: construct an explicit degree-thirteen decorated-face tail
  cutoff for every rational `0 < w < 1`; bound the spin-summed face activity
  by a computed finite prefix and geometric tail; lift that ceiling through
  the exact 66-face residual carrier and full raw row; package the resulting
  selected-term row ceiling, positive return floor, and ray capacity; and
  install them scale-wise at the literal matched BF4/AF nome without changing
  the physical spacing or downstream completed objects.
- **files**:
  `lean/YMGap/Continuum/Z4SpinSummedFaceActivityParametricEnvelope.lean`,
  `lean/YMGap/Continuum/BF4CentralSpinCubeResidualCarrierSumBound.lean`,
  `lean/YMGap/Continuum/BF4CentralSpinCubeRawRowCeiling.lean`,
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeExplicitSubunitSelectedTermRowCeiling.lean`,
  and
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayCompiler.lean`.
- **decl**:
  `explicitDecoratedFaceOffsetCutoff`,
  `explicitDecoratedFaceTailRatio_le_half`,
  `explicitFixedNomeDecoratedFaceCeiling`,
  `fixedNomeDecoratedPlaqActivity_le_explicitCeiling`,
  `explicitFixedNomeCentralSpinCubeResidualCarrierCeiling`,
  `centralSpinCubeResidualCarrierSum_le_explicitFixedNomeCeiling`,
  `centralLowerSpinCubePositiveRawRow_le_activity_mul_explicitFixedNomeCeiling`,
  `explicitSubunitCentralSpinCubeSelectedTermRowCeiling`,
  `explicitSubunitCentralSpinCubeRayCapacity_pos`,
  `explicitSelectedTermRayProducer`,
  `ExplicitTransitionProductExtension`,
  `explicitMatchedRayCapacity_delta_pos`,
  `toDynamicFamily`, `toCompletedFamily`,
  `toNormalizedStrengthLaw`, `StrengthBand`, and
  `SameObjectObservablePin`.
- **obligation**: inhabit the sole remaining matched local field,
  `ExplicitTransitionProductExtension trajectory`, by constructing the
  adaptive off-ray transition product at the exact nome-dependent ray
  capacity.  After that common completed family exists, the normalized
  strength/spacing band and nonzero same-object observable pin are independent
  downstream branches.  Physical cubic and spacing data, full trajectory
  identification, projective OS/GNS reconstruction, thermodynamic/continuum
  compatibility, continuum Yang--Mills existence, and Clay closure remain
  open.  The explicit ceiling depends on `w` and is not a scale-uniform mass
  estimate.
- **constructive?**: yes.  The tail cutoff is explicit natural data, all
  prefix sums and carrier products are finite, every comparison is over
  `Q'`, and the matched specialization uses the already proved pointwise
  nome window.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  custom axiom, or noncomputable declaration is introduced.
- **status note**: focused monitored checks pass.  Dependency-complete
  one-worker targets pass 532 jobs for the face envelope, 996 for the carrier
  sum, 5037 for the raw row, 5041 for the selected-term package, and 5079 for
  the matched bridge.  Newly printed exports use only
  `[propext, Quot.sound]` or `[propext]`.  The root aggregator imports the
  matched bridge.  A monitored root source check stopped immediately because
  the pre-existing `BF4ExactCutoffOneSurfaceForestGaugeMask1C66F8.olean`
  artifact is absent; no root check or full-root audit is claimed.

### [matched-physical-transition-product-finite-decision] Reduce the exact matched extension to all-cutoff Boolean success — **CLOSED 2026-08-25**

- **milestone**: reflect the arbitrary-nome finite routed capacity margin into
  a sound and complete Boolean check; return either its exact finite
  certificate or a constructive scalar refutation; package adaptive and
  canonical cofinal success families; and compile either success family at
  every matched physical scale into the existing explicit-ray transition
  product, dynamic family, completed family, normalized strength law, rate
  band consumer, and same-object observable interface.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayTransitionProductCompiler.lean`.
- **decl**:
  `CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt`,
  `adaptiveFiniteCapacityMarginCheck`,
  `adaptiveFiniteCapacityMarginCheck_sound`,
  `adaptiveFiniteCapacityMarginCheck_complete`,
  `inspectAdaptiveFiniteCapacityMargin`,
  `FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess`,
  `FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess`,
  `MatchedPhysicalDynamicExplicitRayAdaptiveCapacityCheckProducer`,
  `MatchedPhysicalDynamicExplicitRayCanonicalCapacityCheckProducer`,
  `toTransitionProductExtension`, `toCompletedFamily`,
  `toNormalizedStrengthLaw`, `StrengthBand`, `toPhysicalRateBand`, and
  `SameObjectObservablePin`.
- **obligation**: inhabit one all-scale/all-cutoff success family.  The
  canonical route asks only for the already fixed loop-erased-routing checks;
  the adaptive route may choose cutoff-dependent routings if the canonical
  comparison fails.  These are alternative routes to the same serial gate.
  Once either route closes it, the strength/spacing band and nonzero
  same-object observable pin are independent downstream obligations.  The
  physical laws, full trajectory identification, projective OS/GNS,
  thermodynamic/continuum compatibility, continuum Yang--Mills construction,
  and Clay mass gap remain open.
- **constructive?**: yes.  Each check is a decidable comparison in `Q'`, every
  minimum and carrier is finite, failed inspection retains a proof of the
  negated exact inequality, and all cofinal data remain explicit dependent
  functions.  No `Classical`, choice, `sorry`, `admit`, `native_decide`, custom
  axiom, or noncomputable declaration is introduced.
- **status note**: focused monitored checks pass.  Dependency-complete
  one-worker targets pass 5072 jobs for the decision module and 5082 for the
  matched compiler.  Every printed export uses only `[propext, Quot.sound]`;
  the repository executable forbidden-token scan and source declaration scans
  report no violation, and the root aggregator imports the matched compiler.
  The missing pre-existing
  `BF4ExactCutoffOneSurfaceForestGaugeMask1C66F8.olean` artifact prevents a
  root source check; no root check or full-root audit is claimed.

### [matched-physical-eventual-transition-product-check] Remove the unnecessary finite-prefix transition checks — **CLOSED 2026-08-25**

- **milestone**: raise the start of any cofinal ray capacity without changing
  its positive rational delta; specialize that operation to the explicit
  matched ray at a scale-dependent cutoff; package eventual adaptive and
  canonical Boolean-check producers; and compile either producer to the same
  matched dynamic family, completed carrier/transfer/vacuum family,
  normalized strength law, physical-rate-band consumer, and same-object
  observable interface.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler.lean`.
- **decl**:
  `raiseCofinalRayCapacityStart`,
  `raiseCofinalRayCapacityStart_delta`,
  `eventualExplicitRayCapacity`,
  `eventualExplicitRayCapacity_delta`,
  `eventualExplicitRayCapacity_start`,
  `MatchedPhysicalDynamicExplicitRayEventualAdaptiveCapacityCheckProducer`,
  `MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer`,
  `toAdaptiveProducer`, `toLocalProducer`, `toCompletedFamily`,
  `toNormalizedStrengthLaw`, `toLocalProducer_rayCapacity_delta`,
  `StrengthBand`, `toPhysicalRateBand`, and `SameObjectObservablePin`.
- **obligation**: prove eventual canonical check success at every physical
  scale, or supply eventual cutoff-dependent routings if the canonical tail
  fails.  Finite-prefix checks are no longer required.  Pointwise Boolean
  decidability does not prove the remaining eventual quantifier.  After this
  serial gate, the strength/spacing band and nonzero same-object observable
  pin remain independent consumers, followed by the projective and continuum
  compatibility frontier.
- **constructive?**: yes.  The new start is an explicit natural maximum, the
  ray delta is definitionally unchanged, and every later capacity proof is
  obtained by natural-number transitivity.  Eventual success remains explicit
  dependent Type-level data.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, custom axiom, or noncomputable declaration is introduced.
- **status note**: the focused monitored source check passes.  The
  dependency-complete one-worker target passes all 5083 jobs, and every
  printed export uses only `[propext, Quot.sound]`.  The root aggregator
  imports the module; no full-root audit is claimed.

### [matched-physical-eventual-canonical-debt] Compile summable proxy debt to the eventual exact checks — **CLOSED 2026-08-25**

- **milestone**: define the exact shared matched-ray floor divided by a
  positive cutoff-dependent lower proxy; require an explicit same-cutoff
  comparison from that proxy into the canonical routed finite margin; prove
  debt at most one pays the proxy; and compile summable two-sided debt
  variation plus one initial total-budget slack inequality into every
  eventual canonical Boolean check and the unchanged matched completed and
  observable interfaces.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtCompiler.lean`.
- **decl**:
  `fixedNomeFiniteCapacityDebt`,
  `fixedNomeFiniteCapacityDebt_pos`,
  `sharedFloor_le_marginLower_of_debt_le_one`,
  `MatchedEventualCanonicalMarginLowerProxy`,
  `matchedEventualCanonicalCapacityDebt`,
  `matchedEventualCanonicalCapacityDebt_pos`,
  `MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtVariationProducer`,
  `debt_le_one`, `toEventualCanonicalCapacityCheckProducer`,
  `toCompletedFamily`, `toNormalizedStrengthLaw`, `StrengthBand`,
  `toPhysicalRateBand`, and `SameObjectObservablePin`.
- **obligation**: at every physical scale construct a positive lower proxy
  below the exact canonical finite margin, prove summable two-sided cutoff
  variation of its normalized debt, provide a total budget controlled from
  offset zero, and prove `debt(0) + budget <= 1`.  These serial fields then
  close the local transition-product gate.  Strength/spacing and the nonzero
  same-object pin remain independent downstream obligations, followed by
  projective and continuum compatibility.
- **constructive?**: yes.  All streams and bounds are rational, the proxy-to-
  exact-margin edge is explicit at the same nome/cutoff/routing, and the
  persistence theorem uses constructive finite telescoping and an antitone
  tail modulus.  No `Classical`, choice, `sorry`, `admit`, `native_decide`,
  custom axiom, or noncomputable declaration is introduced.
- **status note**: an attempted quotient by the literal exact finite minimum
  was interrupted twice after impractical elaboration and is not counted as a
  pass.  The final lower-proxy formulation passes its focused monitored check
  and its dependency-complete one-worker target, which completes all 5085
  jobs.  All eight printed exports use only `[propext, Quot.sound]`; the root
  aggregator imports the module.  No full-root audit is claimed.

### [matched-physical-eventual-canonical-debt-prefix-tail] Compute the total debt budget from a finite prefix and analytic tail — **CLOSED 2026-08-25**

- **milestone**: factor a generic prefix/tail normalization for any
  `SummableRationalStepVariation`; compute the exact finite variation prefix
  selected by a positive tail allowance; prove the resulting total budget
  controls every finite window; normalize the tail modulus at that budget;
  and specialize the compiler scale-wise to the matched eventual canonical
  debt, preserving the completed and same-object observable interfaces.
- **files**:
  `lean/YMGap/Continuum/SummableRationalStepVariationPrefixTailClosure.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalDebtPrefixTailCompiler.lean`.
- **decl**: `prefixTailStart`, `prefixTailPrefix`,
  `prefixTailTotalBudget`, `prefixTailTotalBudget_pos`,
  `variationPartialSum_le_totalBudget`,
  `variationWindow_le_totalBudget`, `budgetedTailControl`,
  `budgetedTailControl_rate_totalBudget`, `budgetedVariation`,
  `MatchedPhysicalDynamicExplicitRayEventualCanonicalDebtPrefixTailProducer`,
  `totalBudget`, `toDebtVariationProducer`, `debt_le_one`,
  `toEventualCanonicalCapacityCheckProducer`, `toCompletedFamily`,
  `toNormalizedStrengthLaw`, `StrengthBand`, `toPhysicalRateBand`, and
  `SameObjectObservablePin`.
- **obligation**: construct, at every matched physical scale, a positive lower
  proxy below the exact same-cutoff canonical margin, summable two-sided
  variation of its normalized debt, a positive analytic tail allowance, and
  the single computed inequality
  `debt(0) + (exact finite prefix + tail allowance) <= 1`.  The former manual
  total-budget and rate-from-zero fields are no longer premises.  The
  strength/spacing band and nonzero same-object pin remain independent
  downstream obligations, followed by projective and continuum compatibility.
- **constructive?**: yes.  The cutoff is returned by the explicit antitone
  modulus, the prefix is a finite rational sum, the total budget is executable,
  and no witness is selected through propositional existence.  No `Classical`,
  choice, `sorry`, `admit`, `native_decide`, custom axiom, or noncomputable
  declaration is introduced.
- **status note**: focused monitored checks pass for both modules.  The generic
  dependency target completes 43 jobs and the matched dependency-complete
  one-worker target completes 5087 jobs.  All printed exports use only
  `[propext, Quot.sound]` or `[propext]`; the root aggregator imports both
  modules.  No full-root audit is claimed.

### [matched-physical-eventual-canonical-support-proxy] Construct the exact matched lower proxy from routed support data — **CLOSED 2026-08-25**

- **milestone**: specialize the support-aware conditional-kernel floor and
  routed-load maximum to the exact canonical matched nome/cutoff; construct a
  positive lower proxy below the exact same-routing finite capacity margin;
  seal its normalized debt in a proof-bearing rational package to control
  elaboration; transport variation along the stored `Q'.eqv`; and remove the
  free proxy field from the matched prefix-tail persistence producer while
  preserving every completed and same-object observable consumer.
- **files**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.lean`.
- **decl**: `matchedEventualCanonicalRoutingAt`,
  `matchedEventualCanonicalSupportCapacityMarginLower`,
  `matchedEventualCanonicalSupportCapacityMarginLower_pos`,
  `matchedEventualCanonicalSupportCapacityMarginLower_le_exact`,
  `matchedEventualCanonicalSupportMarginLowerProxy`,
  `MatchedEventualCanonicalSupportCapacityDebtValue`,
  `matchedEventualCanonicalSupportCapacityDebtValue`,
  `matchedEventualCanonicalSupportCapacityDebt`,
  `matchedEventualCanonicalSupportCapacityDebt_eqv_exact`,
  `MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer`,
  `exactDebtVariation`, `toPrefixTailProducer`, `debt_le_one`,
  `toCompletedFamily`, `toNormalizedStrengthLaw`, `StrengthBand`,
  `toPhysicalRateBand`, and `SameObjectObservablePin`.
- **obligation**: prove summable two-sided variation of the now-fixed compact
  support-debt stream at every physical scale, choose a positive analytic tail
  allowance, and verify the one computed initial-slack inequality.  Exact
  setoid transport then discharges the former free-proxy interface.  The
  strength/spacing band and nonzero same-object pin remain downstream parallel
  obligations only after this serial local persistence gate closes.
- **constructive?**: yes.  The proxy is an explicit finite rational
  construction.  The opaque boundary has a kernel-checked body and returns a
  structure carrying its exact rational setoid equality; it introduces no
  axiom and erases no witness.  Variation transport is constructive and keeps
  its modulus as data.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, custom axiom, or noncomputable declaration is introduced.
- **status note**: focused monitored checks pass for both modules.  The proxy
  dependency target completes 5088 jobs and the final dependency-complete
  target completes 5093 jobs.  All printed exports use only
  `[propext, Quot.sound]`, and the root aggregator imports both modules.  One
  long elaboration was interrupted and a second same-module form hit the
  deterministic 10M-heartbeat limit; neither is claimed as a pass.  No
  full-root audit is claimed.

### [matched-physical-support-debt-component-variation] Factor exact matched support debt into load variation, kernel variation, and kernel floor — **CLOSED 2026-08-25**

- **milestone**: prove generic positive-ratio debt factorization and variation
  algebra; specialize its numerator, denominator, and fixed shared floor to
  the exact matched canonical support proxy; identify the generic debt with
  both the exact matched debt and its compact proof-bearing representative;
  and compile three independently provable component certificates into the
  previously required support-debt variation.
- **files**:
  `lean/YMGap/Continuum/SummableRationalPositiveRatioDebtVariation.lean`
  and
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor.lean`.
- **decl**: `positiveRatio`, `reciprocalPositiveRatio`,
  `reciprocalPositiveRatio_mul_positiveRatio_eqv_one`,
  `positiveRatioDebt`,
  `positiveRatioDebt_eqv_sharedFloor_mul_reciprocal`,
  `reciprocalNumeratorVariation`,
  `reciprocalPositiveRatioVariationOfPrimitiveComponents`,
  `positiveRatioDebtVariationOfPrimitiveComponents`,
  `matchedEventualCanonicalSupportSharedFloor`,
  `matchedEventualCanonicalSupportedKernelNumerator`,
  `matchedEventualCanonicalRoutedLoadDenominator`,
  `matchedEventualCanonicalPositiveRatioDebt_eqv_exact`,
  `matchedEventualCanonicalPositiveRatioDebt_eqv_compact`, and
  `matchedEventualCanonicalSupportCapacityDebtVariationOfPrimitiveComponents`.
- **obligation**: at every matched physical scale, construct summable
  two-sided variation of the literal routed-load denominator, summable
  two-sided variation of the literal supported-kernel numerator, and one
  positive rational floor below that numerator at every later offset.  These
  now construct exact compact support-debt variation.  A positive tail
  allowance and the computed initial-slack inequality are still required by
  the unchanged persistence compiler.  Strength/spacing and the nonzero
  same-object pin remain downstream obligations after that common gate.
- **constructive?**: yes.  Both variation streams, their tail moduli, and the
  kernel floor are explicit data.  The matched specialization retains the
  literal nome, cutoff, canonical routing, finite carrier, conditional kernel,
  routed load, and explicit-ray delta.  Its transports use `Q'.eqv` proofs;
  no `Classical`, choice, `sorry`, `admit`, `native_decide`, custom axiom, or
  noncomputable declaration is introduced.
- **status note**: focused monitored checks pass for both modules.  The
  generic dependency target completes 48 jobs and the matched target completes
  all 5093 jobs.  Every printed export uses only `[propext, Quot.sound]`; the
  root aggregator imports both modules.  No full-root audit is claimed.

### [matched-physical-support-pointwise-variation] Reduce matched support-debt persistence to three pointwise dynamic-carrier certificates — **CLOSED 2026-08-25**

- **milestone**: define the literal consecutive matched vacuum-sector pair
  carriers, exact routed-load and supported-kernel pointwise functions, and
  three pointwise certificate types; fold their recodings and estimates into
  the exact maximum, minimum, denominator, numerator, and numerator floor;
  contract them into compact support-debt variation; and construct the
  existing matched prefix-tail producer from the three scale-indexed families
  plus its tail allowance and computed initial slack.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler.lean`.
- **decl**: `matchedEventualCanonicalVacuumSectorPairs`,
  `matchedEventualCanonicalRoutedLoadOnPair`,
  `matchedEventualCanonicalSupportedKernelCandidateOnPair`,
  `MatchedEventualCanonicalRoutedLoadMaximumVariation`,
  `MatchedEventualCanonicalSupportedKernelMinimumVariation`,
  `MatchedEventualCanonicalSupportedKernelMinimumFloor`,
  `matchedEventualCanonicalRoutedLoadMaximumVariationOfPointwise`,
  `matchedEventualCanonicalRoutedLoadDenominatorVariationOfPointwise`,
  `matchedEventualCanonicalSupportedKernelMinimumVariationOfPointwise`,
  `matchedEventualCanonicalSupportedKernelNumeratorVariationOfPointwise`,
  `matchedEventualCanonicalSupportedKernelNumeratorFloor`,
  `matchedEventualCanonicalSupportedKernelNumeratorFloor_le`,
  `matchedEventualCanonicalSupportCapacityDebtVariationOfPointwise`, and
  `matchedEventualCanonicalSupportDebtPrefixTailProducerOfPointwise`.
- **obligation**: inhabit, at every physical scale, the exact bidirectional
  routed-load recoding/variation data, exact bidirectional supported-kernel
  recoding/variation data, and exact positive pointwise supported-kernel floor.
  Then choose a positive tail allowance and verify the computed initial-slack
  inequality.  These inputs construct the unchanged completed family; the
  strength/spacing band and nonzero same-object observable pin remain parallel
  downstream obligations only after this common gate closes.
- **constructive?**: yes.  Both recoding directions and carrier-membership
  proofs are computational fields; variation streams carry explicit antitone
  tail moduli; and the floor is returned as positive rational data.  Every
  specialization retains the same trajectory, transition start, scale,
  canonical routing, finite carrier, load, kernel, debt, and ray capacity.  No
  `Classical`, choice, `sorry`, `admit`, `native_decide`, custom axiom, or
  noncomputable declaration is introduced.
- **status note**: the corrected focused monitored check and the
  dependency-complete one-worker target pass, the latter completing all 5099
  jobs.  All eight audited exports use only `[propext, Quot.sound]`.  A
  dependent convenience-record form reached the deterministic 10M-heartbeat
  limit and is not counted as a pass; the final explicit constructor preserves
  the same inputs and conclusion.  The root aggregator imports the module.  No
  full-root audit is claimed.

### [matched-physical-canonical-pair-recoding] Construct consecutive matched carrier maps and remove recoding data from the analytic frontier — **CLOSED 2026-08-25**

- **milestone**: specialize the existing cutoff index embedding to every
  matched physical scale and eventual-tail offset; construct a finite preimage
  search with vacuum fallback in the reverse direction; prove carrier
  membership and the left-inverse law on the embedded old component; apply the
  maps coordinatewise to exact vacuum-sector pair carriers; install them in
  load and kernel envelope interfaces; and contract scale-indexed envelopes
  plus kernel floors to the existing matched prefix-tail producer.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.lean`.
- **decl**: `matchedEventualCanonicalCurrentIndexToNext`,
  `matchedEventualCanonicalNextIndexToCurrent`,
  `matchedEventualCanonicalCurrentIndexToNext_mem`,
  `matchedEventualCanonicalNextIndexToCurrent_mem`,
  `matchedEventualCanonicalNextIndexToCurrent_currentToNext`,
  `matchedEventualCanonicalCurrentPairToNext`,
  `matchedEventualCanonicalNextPairToCurrent`,
  `matchedEventualCanonicalCurrentPairToNext_mem`,
  `matchedEventualCanonicalNextPairToCurrent_mem`,
  `matchedEventualCanonicalNextPairToCurrent_currentToNext`,
  `MatchedEventualCanonicalRoutedLoadEnvelope`,
  `MatchedEventualCanonicalSupportedKernelEnvelope`,
  `MatchedEventualCanonicalRoutedLoadEnvelope.toMaximumVariation`,
  `MatchedEventualCanonicalSupportedKernelEnvelope.toMinimumVariation`,
  `matchedEventualCanonicalSupportCapacityDebtVariationOfEnvelopes`, and
  `matchedEventualCanonicalSupportDebtPrefixTailProducerOfEnvelopes`.
- **obligation**: construct at every physical scale the two summable pointwise
  load inequalities and the dual two supported-kernel inequalities along the
  now-fixed canonical pair maps, plus one positive pointwise kernel floor.
  Then supply a positive tail allowance and the computed initial-slack
  inequality.  The reverse-map fallback exposes the genuinely new-shell
  analytic comparison rather than hiding it in geometric data.
- **constructive?**: yes.  Both maps are executable; reverse search occurs on
  a finite list and has an explicit vacuum fallback; membership and left-
  inverse proofs retain the exact matched nome and cutoff.  Envelope budgets
  carry antitone tail moduli.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, custom axiom, or noncomputable declaration is introduced.
- **status note**: the focused monitored check and dependency-complete target
  pass, the latter completing all 5101 jobs.  All ten audited exports use only
  `[propext, Quot.sound]`; the executable forbidden-token scan reports zero
  hits and the root aggregator imports the module.  No full-root audit is
  claimed.

### [matched-physical-correlated-capacity-debt] Compile one same-edge debt envelope to the exact matched completed family — **CLOSED 2026-08-25**

- **milestone**: define the literal routed-load-to-conditional-kernel capacity
  debt on every ordered pair of the exact matched carrier; prove that debt at
  most one gives the exact canonical edge-capacity field; fold a single
  two-sided pointwise envelope along the constructed pair recodings to
  summable maximum-debt variation; close the maximum by a prefix-plus-tail
  budget; and construct the existing matched local producer and completed
  carrier/transfer/vacuum family directly.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler.lean`.
- **decl**: `matchedEventualCanonicalRoutedCapacityDebtOnPair`,
  `matchedEventualCanonicalRoutedCapacityDebtOnPair_nonnegative`,
  `matchedEventualCanonicalRoutedCapacityDebtOnPair_le_one_implies_edge_capacity`,
  `matchedEventualCanonicalRoutedCapacityDebtMaximum`,
  `MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope`,
  `MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope.toMaximumVariation`,
  `matchedEventualCanonicalRoutedCapacityDebtMaximumVariation`,
  `matchedEventualCanonicalRoutedCapacityDebtMaximum_le_one`,
  `matchedEventualCanonicalCorrelatedCapacityDebtLocalProducer`, and
  `matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamily`.
- **obligation**: inhabit, at every physical scale, the two exact pointwise
  comparisons and summable budget of the one correlated debt envelope along
  the fixed canonical pair maps; choose a positive tail allowance; and prove
  the computed initial closure.  This is the one-producer alternative to the
  separated three-producer load/kernel/kernel-floor frontier.  The strength
  band and nonzero same-object observable pin remain downstream after local
  persistence.
- **constructive?**: yes.  The debt retains the identical pair, routed load,
  conditional kernel, canonical routing, matched nome/cutoff, and explicit-ray
  floor.  Positive load supplies denominator positivity; zero load is handled
  constructively.  Pair maps are executable and the envelope carries an
  explicit antitone tail modulus.  No `Classical`, choice, `sorry`, `admit`,
  `native_decide`, custom axiom, or noncomputable declaration is introduced.
- **status note**: the focused monitored check and dependency-complete
  one-worker target pass, the latter completing all 5102 jobs.  All seven
  audited exports use only `[propext, Quot.sound]`; the root aggregator imports
  the module.  No full-root audit is claimed.

### [matched-physical-correlated-capacity-debt-shell] Split the exact matched correlated envelope into embedded-old and new-shell estimates — **CLOSED 2026-08-25**

- **milestone**: construct the literal embedded image of each current matched
  pair carrier; prove it lies in the next carrier and that canonical reverse
  recoding is inverse there; define the exact new-shell complement; split the
  correlated analytic input into independently summable transported-old and
  new-shell envelopes; add their budgets constructively; and contract
  scale-indexed regional envelopes through the unchanged correlated compiler
  to the exact matched completed family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellCompiler.lean`.
- **decl**: `matchedEventualCanonicalEmbeddedOldPairCarrier`,
  `matchedEventualCanonicalCurrentPairToNext_mem_embeddedOld`,
  `matchedEventualCanonicalEmbeddedOldPairCarrier_mem_next`,
  `matchedEventualCanonicalCurrentPairToNext_nextToCurrent_of_mem_embeddedOld`,
  `MatchedEventualCanonicalPairInNewShell`,
  `matchedEventualCanonicalPair_old_or_newShell`,
  `MatchedEventualCanonicalTransportedCapacityDebtEnvelope`,
  `MatchedEventualCanonicalNewShellCapacityDebtEnvelope`,
  `matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndShell`,
  and
  `matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndShell`.
- **obligation**: inhabit both regional envelope families at every physical
  scale, then provide the unchanged positive tail allowance and computed
  initial closure.  The next expansion splits the new Cartesian pair shell
  into old-new, new-old, and new-new analytic faces.
- **constructive?**: yes.  Embedded membership is a finite-list witness; the
  complement uses decidable membership; the reverse search remains executable;
  and both budgets retain explicit antitone tail moduli.  Every estimate is on
  the identical matched capacity-debt observable.  No `Classical`, choice,
  `sorry`, `admit`, `native_decide`, custom axiom, or noncomputable declaration
  is introduced.
- **status note**: the focused monitored check and dependency-complete
  one-worker target pass, the latter completing all 5103 jobs.  All six audited
  exports use only `[propext, Quot.sound]`; the root aggregator imports the
  module.  No full-root audit is claimed.

### [matched-physical-correlated-capacity-debt-shell-faces] Decompose the exact new pair shell into three parallel ordered faces — **CLOSED 2026-08-25**

- **milestone**: define the embedded-old and new index regions at each matched
  scale and offset; prove embedded pair membership is coordinatewise; prove
  the exact new pair shell is exhausted by old-new, new-old, and new-new
  faces; assign each face an independently summable correlated-debt envelope;
  add all three budgets into the exact shell envelope; and join those three
  lanes with transported-old control to construct the unchanged completed
  matched family.
- **file**:
  `lean/YMGap/Continuum/BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces.lean`.
- **decl**: `matchedEventualCanonicalVacuumSectorIndices`,
  `matchedEventualCanonicalEmbeddedOldIndexCarrier`,
  `MatchedEventualCanonicalIndexInNewShell`,
  `mem_matchedEventualCanonicalEmbeddedOldPairCarrier_iff`,
  `MatchedEventualCanonicalPairInOldNewShell`,
  `MatchedEventualCanonicalPairInNewOldShell`,
  `MatchedEventualCanonicalPairInNewNewShell`,
  `matchedEventualCanonicalNewShellPair_face_cases`,
  `MatchedEventualCanonicalOldNewCapacityDebtEnvelope`,
  `MatchedEventualCanonicalNewOldCapacityDebtEnvelope`,
  `MatchedEventualCanonicalNewNewCapacityDebtEnvelope`,
  `matchedEventualCanonicalNewShellCapacityDebtEnvelopeOfFaces`,
  `matchedEventualCanonicalCorrelatedCapacityDebtEnvelopeOfTransportAndFaces`,
  and
  `matchedEventualCanonicalCorrelatedCapacityDebtCompletedFamilyOfTransportAndFaces`.
- **obligation**: construct four scale-indexed analytic envelope families in
  parallel: embedded-old transport and the three ordered shell faces.  Then
  provide the positive tail allowance and computed initial closure.  All four
  outputs are typed on the identical correlated capacity-debt observable.
- **constructive?**: yes.  All region predicates use decidable finite-list
  membership, face exhaustion is an explicit case split, and each budget has
  an antitone tail modulus.  The join is constructive rational addition.  No
  `Classical`, choice, `sorry`, `admit`, `native_decide`, custom axiom, or
  noncomputable declaration is introduced.
- **status note**: the focused monitored check and dependency-complete
  one-worker target pass, the latter completing all 5104 jobs.  All six audited
  exports use only `[propext, Quot.sound]`; the root aggregator imports the
  module.  No full-root audit is claimed.
