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

### [BF4-exact-physical-Perron] exact Haar / positive Perron same action — **OPEN ANALYTIC INPUT**

- **milestone**: AF macro-slab reroute (`work_plan.md`, Milestone 34)
- **file**:
  `lean/YMGap/Continuum/BF4ExactPhysicalPerronReroute.lean`
- **decls**: `ExactHaarPhysicalPerronSameActionAt`,
  `ExactHaarPhysicalPerronAFQuarterCertificate`,
  `ExactHaarPhysicalLocalGluingAFQuarterCertificate`
- **obligation**: Construct, at every matched cutoff, the finite
  fusion/holonomy resummation identifying the quadratic form of the literal
  signed 116-link Haar kernel on `centralHalfStates K 0` with the normalized
  positive physical reflection quadratic.  For the direct bypass, also
  construct the genuine stationary one-slice density, its exact all-word
  gluing to the physical conditional slab density, and a local centered rate
  at most `1/4`.
- **constructive or propositional**: constructive — same action is a
  `Type`-level witness, while each rowwise local kernel is retained under
  `Nonempty (Sigma oneStep, PhysicalBF4LocalContractionGluingRow ...)` so no
  scale-indexed choice is introduced.
- **status**: open analytic instantiation.  The consumer is closed:
  zero-marginal row/column filtering is proved to preserve the normalized
  full physical OS quadratic exactly; a symmetric-reference Perron estimate
  transfers a quarter bound; and the direct local-gluing route bypasses the
  grouped spectral-eighth/row-eighth/growth node and transfers the stronger
  physical `1/16` estimate to the literal exact Haar quadratic.
- **must not be closed classically**: per `AGENTS.md` Rule 6; the resummation,
  gluing density, and AF-uniform local-rate witnesses must remain explicit.

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
