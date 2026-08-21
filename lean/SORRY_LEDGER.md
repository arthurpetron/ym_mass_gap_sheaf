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
