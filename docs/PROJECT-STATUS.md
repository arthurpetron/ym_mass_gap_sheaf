# Canonical one-page project status

Chart schema: **1**. Snapshot: **46**, 2026-09-24 UTC. Source checkpoint:
the exact lag-two Wilson-to-OS relative-loss bridge consumer, alongside the
checked fixed-parameter complex relative-loss consumer and the explicit
width-degeneration obstruction for the original response witness
committed with this snapshot;
verification is recorded in
`audits/AUDIT-WILSON-COMPLEX-RELATIVE-LOSS-2026-09-24.md` and
`audits/AUDIT-WILSON-RESPONSE-WIDTH-OBSTRUCTION-2026-09-24.md`.
This is the single source for user-facing ASCII progress charts.
The baseline preserves the last displayed chart's wording, layout and
symbols; subsequent updates are maintenance, not redesigns.

## Fixed interpretation

- `[x]`: the EXACT displayed claim is proved and Lean-kernel-checked within
  its recorded scope. "Checked" is evidence for "proved," not a separate
  completion status. A typechecked interface, numerical test, conditional
  theorem or proved sublemma does not close a broader obligation.
- `[ ]`: the displayed obligation is open. Proving a sublemma does not
  change this marker until the whole displayed claim is established.
- `[OPEN]`: the whole-goal header/footer spelling of `[ ]`.
- `<-- CURRENT FRONTIER`: primary active work, independently of proof status.
  Parallel activity is recorded by permanent node ID below.
- Arrows: required dependency flow, NOT a claim that open joins are proved.
  The AND-join requires all its inputs on the SAME resulting theory.
- The checked "Conditional survival theorem" is the implication ONLY;
  its missing input and unproved survival conclusion remain separate nodes.

## Chart

```text
WHOLE-PROJECT GOAL                                      [OPEN]
Constructive Lean Yang-Mills on R^4, EVERY compact simple group:
nontrivial SAME theory, full QFT axioms, isolated vacuum,
and a finite positive physical mass gap: 0 < Delta < infinity.

[x] Checked within stated scope     [ ] Still open

EXPANSION: work backward from the goal into necessary inputs.
CONTRACTION: work forward, joining only proved SAME-object facts.

              ORIGINAL SU(2) LATTICE THEORY [x]
                            |
             +--------------+---------------+
             |                              |
             v                              v
     NONTRIVIALITY BRANCH               GAP BRANCH
     ONE excitation                    EVERY centered state
             |                              |
 [x] Exact plaquette heat images   [x] SAME reflected completion
 [x] Signed energy: 4E+D=2J        [x] Transfer + vacuum sector
             |                              |
             v                              v
 [ ] Complete signed cost versus   [x] Strict completed T^2 bound
     SAME interacting variance        at FIXED coupling/width
     on a justified scaling family          |
             |  <-- CURRENT FRONTIER        v
             v                         [ ] Spatial and spacing
 [x] Conditional survival theorem           control of the rate
     (requires the missing input)           |
             |                              v
             v                         [ ] EVERY-state decay
 [ ] ONE nonzero excitation survives        survives scaling
             |                              |
             +--------------+---------------+
                            |
                            v
 +------------------ REQUIRED AND-JOIN ----------------------+
 | [ ] SAME thermodynamic + continuum limits, explicit moduli |
 | [ ] Full Hilbert/OS/QFT structure and YM fields/UV behavior |
 | [ ] Physical time, Hamiltonian, and mass calibration       |
 | [ ] Construction for EVERY compact simple gauge group     |
 |     All branches must describe the SAME resulting theory. |
 +--------------------------+--------------------------------+
                            |
                            v
                 WHOLE-PROJECT GOAL [OPEN]
```

## Permanent node registry and scope

IDs are never recycled. They identify the fixed labels above without widening
the diagram. This is presentation bookkeeping, not a new Lean frontier bundle.

| ID | Fixed label | Scope / evidence |
|---|---|---|
| G00 | WHOLE-PROJECT GOAL | Unchanged target in the opening of `work_plan.md`. OPEN. |
| F00 | ORIGINAL SU(2) LATTICE THEORY | Finite original action, heat factors and observables underlying the consumers below; NOT continuum Yang--Mills. |
| A01 | Exact plaquette heat images | `BF4ExactSlabFixedSpatialPlaquetteSquare.plaquette_fullRange` and `.plaquetteSquare_fullRange`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSquare.lean:139`, `:165`; actual bare product heat, supported-Haar equivalence, explicit cutoff guards. |
| A02 | Signed energy: 4E+D=2J | `BF4ExactSlabFixedSpatialSourceYoungExplicit.padded_terminal_plaquette_young_channels`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungExplicit.lean:115`; original complete projected source and correction. |
| A03 | Complete signed cost versus SAME interacting variance on a justified scaling family | OPEN original-source estimate for ONE family, or direct response alternative. |
| A04 | Conditional survival theorem (requires the missing input) | `BF4ExactSlabFixedSpatialJointEnergySurvival.response_floor_of_relative_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:112`; supplied relative energy and positive norm floor, SAME fixed-width carrier. |
| A05 | ONE nonzero excitation survives | OPEN compatible changing-scale observable and nonzero response. |
| B01 | SAME reflected completion | `BF4ExactSlabFixedSpatialJointPhysicalTime.JointCompletion`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPhysicalTime.lean:111`; fixed-width carrier. Full Hilbert/QFT packaging remains J02. |
| B02 | Transfer + vacuum sector | Original `jointCompletedTime`, `jointCompletedUnit` and orthogonality used by `completed_twoStep_form_gap` below; discrete time, not a continuum Hamiltonian. |
| B03 | Strict completed T^2 bound at FIXED coupling/width | `BF4ExactSlabFixedSpatialJointCompletedGap.completed_twoStep_form_gap`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointCompletedGap.lean:150`; EVERY vacuum-orthogonal vector, nome/width-dependent rate. Complex extension: `BF4ExactSlabFixedSpatialJointComplexGap.complex_twoStep_form_gap`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexGap.lean:117`. |
| B04 | Spatial and spacing control of the rate | OPEN; fixed-parameter strictness is not scaling control. |
| B05 | EVERY-state decay survives scaling | OPEN; one surviving excitation does not supply a universal bound. |
| J01 | SAME thermodynamic + continuum limits, explicit moduli | OPEN; cutoff/time-window limits are not the full physical limit. |
| J02 | Full Hilbert/OS/QFT structure and YM fields/UV behavior | OPEN; algebra, represented completeness and pairing inequalities are partial prerequisites. |
| J03 | Physical time, Hamiltonian, and mass calibration | OPEN; discrete transfer and scalar logarithmic rates do not identify a physical Hamiltonian or mass edge. |
| J04 | Construction for EVERY compact simple gauge group | OPEN; an SU(2) proof cannot close this node. |

Verification context: `audits/AUDIT-FOUR-LINK-SQUARE-YOUNG-2026-09-24.md`,
`audits/AUDIT-SURVIVAL-QUANTIFIERS-2026-09-24.md`, and the complex-time
checkpoint in `work_plan.md`. These record targeted checks, not a fresh
full-tree build or full axiom audit.

Additional fixed-parameter evidence, NOT a replacement of B01--B03's
recorded face-span carrier: the separate literal-width all-nome Wilson
`BF4WilsonAllNomeCompletedInner.Completion`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedInner.lean:59`) now has its
OWN directly proved strict bound,
`BF4WilsonAllNomeCompletedGap.completed_twoStep_form_gap`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:146`). It covers
every vector orthogonal to its actual unit under its actual temporal
semigroup. No identification of the two completions or transfer of the
face-span survival theorem is claimed. This is additional partial J02
evidence, not a change to the chart's fixed labels or scope registry.

Additional partial A03/J02 evidence: `BF4WilsonAllNomeCenteredVector.centeredVector`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:129`) constructs actual
centered vectors on that Wilson completion. `centered_dyadic_loss_bound` (`:194`)
retains the cubic absolute loss for its changing square family.
`BF4WilsonAllNomePlaquetteExcitation.nonzeroExcitation` and
`.positiveResponseExcitation`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteExcitation.lean:113`, `:123`)
supply a positive plaquette norm and a positive one-step response at fixed
parameters, not growing-loop/scaling survival. No change to A04's separate
face-span conditional consumer or B01--B03's recorded scope is asserted.

New fixed-parameter same-carrier response evidence:
`BF4WilsonAllNomePlaquetteTwoStepResponseCore.completed_oneStep_diagonal` and
`.plaquetteExcitation_response_square`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteTwoStepResponseCore.lean:46`,
`:52`) combine exact time balance, completed Cauchy--Schwarz, and the existing
one-step floor. `BF4WilsonAllNomePlaquetteTwoStepResponse.plaquetteExcitation_twoStep_floor`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteTwoStepResponse.lean:65`)
divides by the proved completed diagonal ceiling and returns an explicit
positive lag-two floor on the actual all-nome Wilson excitation. The padding
wrapper `.padded_plaquetteExcitation_twoStep_floor`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteTwoStepResponsePadded.lean:33`)
preserves the result under spatial-face inclusion. The nome and width remain
parameters, so B04, B05, A03 scaling, and all continuum joins remain open.
Verification is recorded in
`audits/AUDIT-WILSON-PLAQUETTE-TWO-STEP-RESPONSE-2026-09-24.md`.

New complex-carrier concrete excitation consumer:
`BF4WilsonAllNomeComplexPlaquetteExcitation.complexPlaquetteExcitation`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexPlaquetteExcitation.lean:52`)
embeds the already constructed real plaquette state into the actual
two-component complex carrier.  Its orthogonality to the complex unit,
diagonal/norm identity, positive norm floor, lag-two response floor,
fixed-parameter relative loss, and iterated even-lag correlator decay are
proved in the same module (`:58`, `:68`, `:75`, `:82`, `:91`, `:105`).  The
two-padding origin specialization is also explicit (`:118--139`).  This is a
concrete same-object complex witness, not a cross-width identification or an
OS/GNS bridge; nome, width, active-face hypotheses, spacing-uniform control,
scaling survival, physical mass, continuum, and all-group obligations remain
open.  Verification is recorded in
`audits/AUDIT-WILSON-COMPLEX-PLAQUETTE-EXCITATION-2026-09-24.md`.

New concrete physical-carrier relative-loss consumer:
`BF4PhysicalConcreteSU2RelativeLoss.sector_relative_loss_of_form_gap`
(`lean/YMGap/Continuum/BF4PhysicalConcreteSU2RelativeLoss.lean:62`) rewrites
the existing completed sector form-gap certificate as
`(1-rate) * <v,v> ≤ <v,v> - <Tv,v>` on the SAME completed vacuum complement.
`concreteSU2_relative_loss_of_marginalGap` (`:89`) specializes this to the
literal moving-centered cube autocorrelation with the inhabited finite rate
`cutoffUniformRate w`, and `concreteSU2_relative_loss_margin_positive` (`:110`)
proves its fixed-nome margin positive.  This is a direct finite physical
consumer for the relative-loss bridge; it does not provide spacing-uniformity,
an OS/GNS map, a continuum limit, physical mass, or an all-group theorem.
Verification is recorded in
`audits/AUDIT-PHYSICAL-SU2-RELATIVE-LOSS-2026-09-24.md`.

New dynamic form-level certificate:
`BF4PhysicalDynamicVacuumSectorFormGapRelativeLoss.DynamicVacuumSectorCompletedFormGapFamily`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFormGapRelativeLoss.lean:42`)
keeps the one-step form gap separate from the dynamic family's squared-norm
contraction.  The fixed-`w=1/2` geometric staging family inhabits it (`:49`),
and `channel_relative_loss_of_formGapFamily` (`:62`) transports it to the
literal same-object RC channel.  The equality-only
`channel_relative_loss_of_formGapFamily_global` consumer (`:80`) exposes the
same coefficient through the global completed Markov transfer on that
identical vector.  The moving-centered cube specialization and positive
scale-wise margin are proved at `:111` and `:130`.  This is an honest
family-level bridge input; the attached spacing still tends to zero with a
constant lattice margin, so the existing physical-rate-band obstruction,
continuum construction, physical mass, and all-group obligations remain open.
Verification is recorded in
`audits/AUDIT-DYNAMIC-FORM-GAP-RELATIVE-LOSS-2026-09-24.md`.

New dynamic form-to-operator bridge:
`BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.DynamicVacuumSectorCompletedMarkovFormCauchySchwarzFamily`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorMarkovFormCauchySchwarzBridge.lean:56`)
factors the positive completed Markov-form Cauchy--Schwarz input at each
scale.  The canonical producer (`:66`) is supplied by the existing adaptive
completed Markov-form theorem.  The consumer
`channel_completed_norm_gap_of_formGap_and_markovCS` (`:78`) composes that
input with the scale-wise form family and returns the literal completed
`<Tv,Tv> <= rate^2 <v,v>` estimate for the same channel vector; the
input-free wrapper `channel_completed_norm_gap_of_formGap` is at `:105`.
No chart-node status changes.
Verification is recorded in
`audits/AUDIT-DYNAMIC-MARKOV-FORM-CS-BRIDGE-2026-09-24.md`.

The same bridge now has an inhabited concrete specialization:
`marginalHalfGeometricCompletedFormGapFamily` (`:79`) and its rate pin (`:85`)
feed `marginalHalfGeometricMovingCube_completed_norm_gap` (`:143`), giving a
literal nonzero moving-centered cube channel estimate at every geometric
scale.  The lattice margin remains fixed while spacing vanishes; no chart-node
status changes.

New finite nontriviality input:
`BF4PhysicalDynamicVacuumSectorUniformNormFloorSpecialization.marginalHalfGeometricMovingCubeUniformRCNormFloor`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorUniformNormFloorSpecialization.lean:34`)
inhabits the scheduled channel's scale-uniform rational norm floor for the
constant-nome geometric family.  Its zero-time transport theorem (`:48`)
retains that floor on the sampled same-object autocorrelation at every scale.
The representative-level cutoff limit and spacing-uniform physical decay
remain open; no chart-node status changes.

New fixed-family normalization-debt input:
`BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt` proves that the
reciprocal-square normalization debt is constant along the inhabited
`w = 1/2` geometric staging family and constructs its zero rational
step-variation certificate for the actual rational debt stream.  The
normalized-limit consumer can now use this as its debt input, but raw
representative variation remains separate.  Raw variation, rate-power
convergence, physical scaling, and all continuum/QFT obligations remain open;
no chart-node status changes.  Verification is recorded in
`audits/AUDIT-FIXED-FAMILY-NORMALIZATION-DEBT-2026-09-24.md`.

New fixed-family normalization ceiling:
`BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizationCeiling` proves the
reciprocal normalization scale is constant and packages it as the generic
`MovingCubeNormalizationScaleCeiling`.  The resulting certificate supplies a
raw-channel uniform norm floor and a fourth-power debt bound for every
geometric cutoff.  Raw representative variation, positive-time rate-power
variation, physical scaling, and the continuum/QFT joins remain open; no
chart-node status changes.  Verification is recorded in
`audits/AUDIT-FIXED-FAMILY-NORMALIZATION-CEILING-2026-09-24.md`.

### Fixed-family rate-power sampler arithmetic (2026-09-24 UTC)

`BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic.marginalHalfGeometric_latticeSteps_eq`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic.lean:26`)
proves that the actual floor sampler for the geometric spacing is exactly
`time * 2^scale`. Together with the existing fixed-rate pin, this reduces the
positive-time sampled rate-power stream to explicit dyadic-exponent arithmetic.
The constructive antitone-tail/variation certificate is still open, as are
raw representative variation, physical-rate scaling, and all continuum/QFT
joins. Verification is recorded in
`audits/AUDIT-FIXED-FAMILY-RATE-POWER-ARITHMETIC-2026-09-24.md`.

### Generic geometric antitone tail (2026-09-24 UTC)

`GeometricAntitoneTailControl.geometricPowerTailControl`
(`lean/YMGap/Continuum/GeometricAntitoneTailControl.lean:105`) now inhabits
the order-antitone `AntitoneTailControl (fun n => r ^ n)` for every rational
`0 < r < 1`. The cutoff and bound are explicit at `:31`, `:37`, and `:52` and
use `qCeilNat` rather than representation-sensitive numerator data. This is a
generic scalar input; the fixed-family stream-specific step bounds and all raw,
physical, continuum, OS/QFT, and Clay joins remain open. Verification is
recorded in `audits/AUDIT-GEOMETRIC-ANTITONE-TAIL-2026-09-24.md`.

### Positive-time dyadic rate-power core (2026-09-25 UTC)

`BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.positiveRatePowerVariation`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.lean:60`)
constructs the complete rational step-variation datum for every exact stream
`r^(time * 2^scale)` with `0 < r < 1` and positive time. This is the scalar
certificate selected by the fixed-family rate pin and sampler arithmetic. The
equality bridge to the compiler's actual normalized stream is now discharged
for this concrete staging family by a separate specialization; all raw,
physical, continuum, OS/QFT, and Clay joins remain open. The companion
`positiveRatePowerVariation_limit_equiv_zero`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore.lean:101`)
proves that the exact positive-time geometric stream has zero completed CReal
limit, exposing that this spacing family cannot itself provide a positive mass
calibration. Verification is recorded in
`audits/AUDIT-FIXED-FAMILY-RATE-POWER-VARIATION-CORE-2026-09-25.md`.

### Positive-time-only raw variation frontier (2026-09-25 UTC)

The canonical fixed-family raw stream now factors its remaining input into
`MarginalHalfGeometricRawRepresentativeCanonicalPositiveTimeVariation`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:560`),
which asks only for summable cross-scale variation when `0 < time`.
`...PositiveTimeVariation.toAllTime` (`:567`) inserts the checked
`marginalHalfGeometricRawCanonicalZeroTimeVariation` (`:518`) and produces the
all-time object required by the normalized compiler.  This removes duplicated
zero-time obligations and leaves one precisely typed positive-time frontier;
the same-object theorem
`marginalHalfGeometricRawRepresentativeCanonical_sq_decay` (`:422`) exposes
the finite squared decay on the canonical CReal representative itself.
The conditional contraction
`marginalHalfGeometric_normalizedContinuumLimitOfPositiveTime` (`:609`),
with strict positivity (`:618`) and squared decay (`:632`), now joins this
single raw object to the already checked normalization-debt and rate-power
streams.  It remains conditional precisely on the positive-time raw variation
certificate.
the continuum, spacing-uniform mass, and Clay nodes remain open.

### Concrete normalized-stream rate input (2026-09-25 UTC)

`BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization`
(`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean`)
transports the generic certificate to the literal normalized scheduled-rate
stream of `marginalHalfGeometricCompletedFamily`. The declarations
`marginalHalfGeometric_positiveRatePowerVariation` (`:84`) and
`marginalHalfGeometric_ratePowerVariation` (`:94`) now inhabit the actual
compiler's all-time rational rate-variation input. This does not inhabit raw
connected-moment variation; the positive-time limit remains zero, so no
positive physical mass or continuum/Clay claim follows. Verification is
recorded in
`audits/AUDIT-FIXED-FAMILY-RATE-POWER-SPECIALIZATION-2026-09-25.md`.

The same specialization also converts the fixed-family pointwise-constant
normalization debt into the constructive-real debt-variation input via
`marginalHalfGeometric_normalizationNormDebtVariation` (`:75`).  Both scalar
inputs of the normalized cutoff compiler are therefore inhabited for this
family; only the raw same-object CReal representative's cross-scale variation
remains the independent missing input.  Verification is recorded in
`audits/AUDIT-FIXED-FAMILY-NORMALIZED-RATE-AND-DEBT-2026-09-25.md`.

Conditional raw nontriviality is also now composed by
`marginalHalfGeometric_rawContinuumNontriviality` (`lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:123`): once the raw representative/variation certificate is supplied, the fixed-family uniform norm floor supplies the exact continuum zero-time positivity field.  This does not construct the raw certificate itself.

The carrier/transfer side of the raw frontier is now audited explicitly:
`centralPhysicalDynamicMovingCubeRCChannel` and
`sampledConnectedAutocorrelation_eq_global` identify the same completed
moving-cube observable at the `CReal.RC` level.  The fixed-family specialization
now constructs the CReal stream itself from explicit Cauchy presentations via
`marginalHalfGeometricRawRepresentative` (`:210`) and proves its exact
`represents` equality (`:525`).  The remaining input is only the summable
cross-scale variation field; no hidden quotient choice is used.  This is
recorded in `audits/AUDIT-RAW-REPRESENTATIVE-SELECTION-2026-09-25.md`; no
chart marker changes.

The fixed-family stream is now also proof-argument-canonical via
`marginalHalfGeometricRawRepresentativeCanonical` (`:248`) and its exact
`represents` theorem (`:330`).  This removes scale-dependent nome-proof noise.
The time-zero slice is definitionally constant and its complete
`SummableCRealStepVariation` certificate is inhabited by
`marginalHalfGeometricRawCanonicalZeroTimeVariation` (`:518`); the positive-
time cross-scale field remains the active raw frontier.  No chart marker
changes.

New fixed-parameter rate calibration:
`BF4WilsonAllNomePlaquetteRateCalibration.plaquette_twoStep_floor_le_rate_mul_normCeiling`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteRateCalibration.lean:54`)
composes the actual same-carrier lag-two floor with the existing completed
strict transfer bound and the completed diagonal ceiling, yielding
`twoStepFloor ≤ twoStepRate * plaquetteNormCeiling`. This constrains the
existing rate but does not make it uniform in coupling, width, volume, or
lattice spacing. Scaling survival and all continuum joins remain open. Its
focused verification is recorded in
`audits/AUDIT-WILSON-PLAQUETTE-RATE-CALIBRATION-2026-09-24.md`.

New normalized same-carrier response evidence:
`BF4WilsonAllNomePlaquetteRelativeFloor.plaquetteExcitation_relative_floor`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteRelativeFloor.lean:70`)
divides the explicit lag-two floor by the actual completed diagonal ceiling
and bounds the resulting positive Rayleigh-style witness below the true
same-carrier lag-two pairing. `plaquette_relativeFloor_le_rate` (`:95`)
constructively cancels the supplied positive norm floor against the existing
strict transfer estimate, and `twoStepRate_positive_of_plaquette` (`:111`)
derives strict positivity of the fixed-parameter rate. Nome, width, and the
active-face premise remain explicit; scaling and continuum joins remain open.
Verification is recorded in
`audits/AUDIT-WILSON-PLAQUETTE-RELATIVE-FLOOR-2026-09-24.md`.

New computed-rate scaling obstruction:
`BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.no_width_uniform_computed_twoStepRate`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoStepRateWidthObstruction.lean:132`)
proves that for every strict nome and every rational `0 ≤ q < 1`, the existing
computed `twoStepRate = mixRate^2` exceeds `q` at an explicit positive width.
This closes no roadmap node; it records that the current fixed-width scalar
certificate cannot be promoted to B04's spacing-uniform rate.  The theorem is
about the computed comparison rate only, not the actual transfer operator or
Yang--Mills.  Verification is recorded in
`audits/AUDIT-WILSON-TWO-STEP-RATE-WIDTH-OBSTRUCTION-2026-09-24.md`.

New computed-response scaling obstruction:
`BF4ExactSlabFixedSpatialResponseWidthObstruction.detectorScale_le_margin_power`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialResponseWidthObstruction.lean:58`)
and `uniformFloor_le_margin_power_square` (`:85`) show that the explicit
original plaquette lower-witness coefficient is bounded by
`(1/32)^(width+width)`.  The explicit `responseWidthModulus`/`uniformFloor_le_epsilon`
pair (`:110`, `:113`) gives a width modulus, and
`no_width_uniform_uniformFloor` (`:127`) rules out any positive width-uniform
floor for this particular computed witness.  This is a certificate
obstruction only: it is not a statement about the actual response or transfer
operator and leaves A03, B04, B05 and all continuum joins open.  Verification:
`audits/AUDIT-WILSON-RESPONSE-WIDTH-OBSTRUCTION-2026-09-24.md`.

New fixed-parameter same-carrier relative-loss evidence:
`BF4WilsonAllNomeComplexRelativeLoss.complex_twoStep_relative_loss`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexRelativeLoss.lean:53`)
rewrites the existing strict complex Wilson two-step form bound as an explicit
deficit bound with margin `1-twoStepRate`; its positivity is proved at `:62`.
This supplies the concrete fixed-parameter shape consumed by the typed
Wilson-to-OS relative-loss bridge, but the margin remains nome/width
dependent and no bridge inhabitant or scaling survival is supplied.
Verification: `audits/AUDIT-WILSON-COMPLEX-RELATIVE-LOSS-2026-09-24.md`.

New exact lag-two bridge contraction:
`BF4WilsonOSBridgeSpec.OSRelativeLossGap` and
`BF4WilsonOSBridgeSpec.transfer_twoStep_relative_loss`
(`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:88`, `:154`) isolate and
transport the precise two-step relative-loss statement now supplied by the
complex Wilson carrier.  This removes an unnecessary all-lag interpolation
obligation from the future concrete bridge, while leaving the carrier map,
pairing identity, OS-side inhabitant, and all scaling/continuum requirements
open.  Verification is recorded in
`audits/AUDIT-WILSON-OS-BRIDGE-SPEC-2026-09-24.md`.

New fixed-parameter cutoff consumer:
`BF4WilsonAllNomeOriginComplexCutoff.origin_twoStepRate_positive`
(`lean/YMGap/Continuum/BF4WilsonAllNomeOriginComplexCutoff.lean:42`) consumes
the literal origin plaquette, its two explicit padding layers, and the existing
same-carrier rate calibration to prove strict positivity of `twoStepRate` at
`width + 2` without an extra face or activity hypothesis.  Its companion
`origin_complexRateCutoff_bound` (`:53`) feeds that positivity into the
existing `HKConvGen.powBaseCutoff` modulus for every positive rational error
target.  This is coefficient-level finite-parameter evidence only; it does
not alter the computed-rate width obstruction or close B04, A05, J01, J02,
J03, or J04.  Verification is recorded in
`audits/AUDIT-WILSON-ORIGIN-COMPLEX-CUTOFF-2026-09-24.md`.

New same-carrier relative-energy compiler:
`BF4WilsonAllNomeDyadicRelativeSurvival.dyadic_response_floor_of_relative_energy`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:124`)
consumes a relative loss bound for the actual padded dyadic-square state and
returns a positive response floor at its own discrete lag, using the existing
`starRatio` norm floor.  The companion
`dyadic_relative_energy_of_loss_budget` (`:140`) composes the existing cubic
centered loss estimate with an explicit SAME-norm budget, cancelling the
factor two constructively; `dyadic_response_floor_of_loss_budget` (`:154`)
composes both pieces.  The budget remains an explicit hypothesis and is not
proved along a changing-scale trajectory.  No chart node changes status:
spacing control, scaling survival, continuum, physical mass, and all-group
construction remain open.  Verification is recorded in
`audits/AUDIT-WILSON-DYADIC-RELATIVE-SURVIVAL-2026-09-24.md`.

New same-carrier rate-margin calibration:
`BF4WilsonAllNomeTwoStepMargin.vacuumComplement_twoStep_rate_margin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTwoStepMargin.lean:103`) proves that
any nonzero vacuum-complement state with a relative lag-two loss `delta` forces
`1 - delta ≤ twoStepRate`.  Its companion
`vacuumComplement_twoStep_margin_le_relative_energy` (`:112`) rewrites this as
the explicit necessary margin bound `1 - twoStepRate ≤ delta`.  This is a
backward calibration of the existing fixed-parameter rate, not a producer of
the relative-loss estimate and not a physical Hamiltonian or continuum gap.
No chart node changes status.  Verification is recorded in
`audits/AUDIT-WILSON-TWO-STEP-MARGIN-2026-09-24.md`.

New certificate-number obstruction:
`BF4WilsonAllNomeDyadicRationalBudgetObstruction.no_rational_loss_budget`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRationalBudgetObstruction.lean:47`)
proves that the explicit cubic formula cannot satisfy the proposed rational
survival budget whenever an abstract response floor `rho` obeys
`rho ≤ 1-w`.  The theorem intentionally does not identify `rho` with
`starRatio`; it is therefore a reusable arithmetic obstruction, not a
completed-loss lower bound.  It redirects A03's next step to a sharper
SAME-object loss comparison or a different response/scaling certificate.
`CoarseBudgetData` (`:35`) packages the proposed inputs as explicit Type-level
data, and `coarse_budget_data_empty` (`:110`) proves that package empty under
`0 < 1-w`.
No chart node changes status.  Verification is recorded in
`audits/AUDIT-WILSON-DYADIC-RATIONAL-BUDGET-OBSTRUCTION-2026-09-24.md`.

New rationalized same-carrier budget:
`BF4WilsonAllNomeDyadicRelativeSurvival.dyadic_relative_energy_of_rational_loss_budget`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRelativeSurvival.lean:156`)
reduces the completed norm-budget premise to the explicit rational inequality
`dyadicLossBound ≤ 2*delta*starRatio w`, using the existing positive norm floor
and nonnegative scalar action.  This removes a quotient-real budget from the
input interface but does not prove the rational inequality along scaling.  No
chart node changes status.  Verification is recorded in
`audits/AUDIT-WILSON-DYADIC-RELATIVE-SURVIVAL-2026-09-24.md`.

Additional partial J02 evidence: `BF4WilsonAllNomeLinear.completedAdd` and
`.completedSmul` (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:132`, `:135`)
construct actual rational operations with explicit moduli; `LinearLaws`
proves their laws. `BF4WilsonAllNomeGeometry.completedInner_posdef`
(`lean/YMGap/Continuum/BF4WilsonAllNomeGeometry.lean:71`) identifies zero norm
with the actual zero state. `BF4WilsonAllNomeBilinearTime.orbitSum_pairing`
(`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:195`) retains the full
signed double correlator on actual finite time combinations.
`BF4WilsonAllNomeTimeDifference.timeDifference_norm_lower` and
`.positiveTimeDifferenceExcitation`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDifference.lean:122`, `:192`)
supply the squared-norm lower bound `(1-q)^2*B(x,x)` for x-T(2)x and an
actual plaquette-difference state with positive floor at every positive
width. The floor depends on nome/width; this is not scaling survival, an
A03 variance comparison, or full J02 closure.

Additional partial J02 evidence: `BF4WilsonAllNomeDistance.distanceData`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDistance.lean:125`) constructs the
actual completed squared-distance data.
`BF4WilsonAllNomeCauchyRows.limit_bound` and `.limit_timeRows`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCauchyRows.lean:67`, `:119`) prove
computed represented limits and their commutation with actual discrete time.
`.limit_orthogonal` and `.orthogonalLimit` (`:158`, `:181`) retain the
existing vacuum complement. Supplied representatives and inner/outer moduli
remain data; no arbitrary quotient-row selection or full Hilbert claim.
Additional A03 geometry only: `BF4DyadicWilsonSquareUniqueEdge.paddedSquare_edges_split`
and `.selectedLink_not_mem_dyadicTail`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareUniqueEdge.lean:170`, `:182`)
expose a literal head and exclude its underlying link from the remaining
growing square word. The original arbitrary-word Haar moments and useful
scaling-variance estimate are not supplied by this geometry.

Additional partial A03 evidence: the original arbitrary-word Haar moments
are now proved in `BF4ExactSlabWilsonWordSingleLinkMoments.original_word_first_moment`
and `.original_word_second_moment`
(`lean/YMGap/Continuum/BF4ExactSlabWilsonWordSingleLinkMoments.lean:44`, `:63`).
`BF4DyadicWilsonSquareSingleLinkMoments.paddedSquare_complement_first_moment`
and `.paddedSquare_complement_second_moment`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareSingleLinkMoments.lean:69`, `:83`)
derive their premises for the actual growing square and retain the entire
selected-link complementHeat product R.
`BF4DyadicWilsonSquareShiftedMoment.paddedSquare_shifted_complement_moment`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareShiftedMoment.lean:93`)
gives H[(chi-c)^2 R]=(1+c*c)*H[R] for arbitrary rational c. R is not the full
action; its incident factors still require an interacting comparison.
Those moment lemmas alone supply no normalized full-action variance,
completed-vector scaling bound, or survival conclusion.

Additional partial A03/J02 evidence: the interacting comparison is now
proved by `BF4ExactSlabWilsonWordVariance.finiteValue_variance_floor_with_mean`
(`lean/YMGap/Continuum/BF4ExactSlabWilsonWordVariance.lean:172`), with floor
starRatio(w)*(1+mean^2) and the SAME selected-action mean and partition.
`BF4DyadicWilsonSquarePlacedGeometry.paddedSquare_placed_edges_split`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquarePlacedGeometry.lean:41`) retains
the exact moving placement. `BF4WilsonAllNomeDyadicVariance.centeredVector_norm_floor`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicVariance.lean:167`) passes the
actual chainIds-window estimate through the existing limits to the SAME
centered Wilson vector. `BF4WilsonAllNomeDyadicExcitation.nonzeroExcitation`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicExcitation.lean:84`) computes
a nonzero state for every square scale with fitting width=2^scale+1.
The floor is independent of width and square size at fixed nome, but
deteriorates with nome. No states in different completions are identified;
the cubic loss/scaling mismatch, A03 and full J02 remain open.

Additional A03 route limitation:
`BF4DyadicResetBudgetObstruction.selectedSublist_resetFloor_cubic_budget_nonpositive`
(`lean/YMGap/Continuum/BF4DyadicResetBudgetObstruction.lean:123`) proves the
proposed multi-link reset floor cannot pay the existing half-increment
budget 192*L^3*(1-w), for every actual selected sublist of square edges.
This is not an upper bound on variance or a refutation of physical survival.
No reset expansion is assumed; proving one alone would not fix this join.

Additional partial A03 evidence:
`SU2QuaternionProductHeatWilsonWord.productMap_fundamental_word`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:248`)
proves exact original product-heat transmission w^(3*perimeter), retaining
arbitrary supported tests. `BF4DyadicWilsonSquareNodup.paddedSquare_indices_nodup`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareNodup.lean:238`) derives actual
carrier-index distinctness. `BF4DyadicWilsonSquareHeatImage.paddedSquare_fringe_independent`
and `.paddedSquare_fundamental_fullRange`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareHeatImage.lean:84`, `:101`)
derive strict-padding independence and the literal square multiplier w^(12*L).
`BF4DyadicWilsonSquareSignedCost.paddedSquare_terminal_young_identity`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedCost.lean:86`) retains
the original terminal source and correction: 4E+D=2*((1-2*w^(12*L))*M+S),
where M=H[q*q*f*f] and S=H[q*q*P(f*f)]. The square image S was unresolved
at snapshot 18; the next paragraph records its producer. The useful SAME
interacting variance/scaling comparison and A03 remain open. This bare
kinetic image is not an eigenidentity for the interacting completed transfer.

Additional partial A03 evidence:
`SU2QuaternionProductHeatWilsonSpinTwo.productMap_spinTwo_word` and
`.productMap_fundamental_square`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonSpinTwo.lean:242`, `:263`)
prove the original label-two multiplier w^(8*perimeter) and full fundamental
square image 1+w^(8*perimeter)*chi_2, retaining ordered prefixes, genuine
Haar-unit certificates and every supported final test. The actual square
specialization `BF4DyadicWilsonSquareQuadraticHeat.paddedSquare_square_fullRange`
and `.paddedSquare_square_moment`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareQuadraticHeat.lean:83`, `:120`)
give b=w^(32*L) and S=b*M+(1-b)*N, N=H[q*q]. Its
`.paddedSquare_terminal_quadratic_identity` (`:178`) now proves
4E+D=2*((1-2*a+b)*M+(1-b)*N), a=w^(12*L), with the actual terminal message,
complete projected source and signed correction. No source normalization,
useful SAME centered-variance/scaling bound or interacting eigenmode is
inferred. A03 stays open; no recorded face-span or Wilson carrier is replaced.

Additional partial A03 evidence: `BF4DyadicWilsonSquarePassiveChannels.paddedSquare_energy_eq_channels`
and `.oddMass_eq_active_square_channels`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:109`, `:190`)
preserve the ORIGINAL energy and odd mass with every spectator heat factor
retained. `BF4DyadicWilsonSquareChannelCost.paddedSquare_terminal_channel_cost`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelCost.lean:135`) evaluates
4E+D_ch in the actual computed channel moments A,M. The original odd mass
is an active HEAT pairing, not A. The cap-four certificate and weighted
channel bound in `BF4DyadicWilsonSquareChannelGeometry.squareChannelMoment_le_four_mass`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:220`)
supply 4A-M>=0. `BF4DyadicWilsonSquareChannelBudget.paddedSquare_terminal_signed_geometric_budget`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelBudget.lean:98`) proves
4E+D_ch<=2*(8*(1-u)*(4A-M)+960*(1-u)^2*A), u=w^L. D_ch is retained;
neither it nor A is identified with an unchannelized predecessor. The useful
SAME interacting centered-variance/scaling comparison remains open. No
completed scaling improvement or carrier substitution is asserted.

## Activity and changes since the preceding chart

New partial J02 evidence: `BF4WilsonAllNomeComplexGap.complex_twoStep_translated`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:132`) applies the
existing strict bound to every translated complex vacuum-orthogonal state and
exposes the exact same-object correlator indices `n` and `n+2` using the
existing completed-time semigroup law.  Its focused check is within
`{propext, Quot.sound}` with no source hole, classical input, warning or
error.  This remains fixed nome/width discrete time; it supplies no spacing,
thermodynamic, continuum, physical-mass or all-group conclusion.  Evidence:
`audits/AUDIT-WILSON-COMPLEX-TRANSLATED-GAP-2026-09-24.md`.

New partial J02 evidence: `BF4WilsonAllNomeComplexGap.complex_oneStep_norm_gap`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:145`) rewrites that
same-object `n,n+2` correlator as the norm-square contraction at the
intervening slice `n+1`, using only the exact completed-time pairing identities.
The focused monitored check exits 0 and the declaration audits to
`{propext, Quot.sound}` with no `sorryAx`, classical input, warning or error.
This is still fixed nome/width discrete time; no spacing, scaling,
thermodynamic, continuum, physical-mass or all-group node closes.  Evidence:
`audits/AUDIT-WILSON-COMPLEX-ONE-STEP-NORM-GAP-2026-09-24.md`.

New partial J02 evidence: `BF4WilsonAllNomeComplexGap.complex_iterated_norm_gap`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:159`) iterates the
same completed-carrier contraction and proves geometric norm-square decay
`twoStepRate^n` for every discrete power.  The focused monitored check exits 0
and the declaration audits to `{propext, Quot.sound}` with no `sorryAx`,
classical input, warning or error.  The rate remains nome/width-dependent, so
this adds no spacing/scaling, thermodynamic, continuum, physical-mass or
all-group closure.  Evidence:
`audits/AUDIT-WILSON-COMPLEX-ITERATED-NORM-GAP-2026-09-24.md`.

New partial J02 evidence: `BF4WilsonAllNomeComplexGap.complex_even_lag_corr_decay`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:180`) converts the
iterated norm estimate into the same-object correlator bound at even lag `2*n`
using the exact completed-time pairing identity.  The focused monitored check
exits 0 and the declaration audits to `{propext, Quot.sound}` with no
`sorryAx`, classical input, warning or error.  This remains fixed nome/width
discrete time; no spacing/scaling, thermodynamic, continuum, physical-mass or
all-group node closes.  Evidence:
`audits/AUDIT-WILSON-COMPLEX-EVEN-LAG-CORRELATOR-2026-09-24.md`.

New partial J02 evidence: `BF4WilsonAllNomeComplexGap.complex_even_lag_corr_nonnegative`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:188`) proves
nonnegativity of every even-lag same-object correlator by rewriting it to the
diagonal norm.  `complexRateCutoff`/`complexRateCutoff_bound`
(`:196`, `:199`) add the explicit `HKConvGen.powBaseCutoff` modulus for the
scalar coefficient, with strict rate positivity stated as an honest premise.
The focused monitored check exits 0 and all new declarations audit to
`{propext, Quot.sound}` with no `sorryAx`, classical input, warning or error.
This is coefficient-level fixed-parameter evidence only: an absolute observable
modulus still needs a norm cap and parameter-uniform positivity/rate control.
No spacing/scaling, thermodynamic, continuum, physical-mass or all-group node
closes.  Evidence:
`audits/AUDIT-WILSON-COMPLEX-RATE-MODULUS-2026-09-24.md`.

New conditional J02 evidence: `BF4WilsonAllNomeComplexGap.complex_even_lag_response_power_floor`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:210`) composes the
same-object even-lag decay with explicit norm-cap and response-floor
hypotheses, yielding `floor ≤ twoStepRate^n*C` on the SAME complex carrier.
The focused monitored check exits 0 and the declaration audits to
`{propext, Quot.sound}` with no `sorryAx`, classical input, warning or error.
This is a conditional compiler only: cap/response production, strict rate
positivity, spacing/scaling, thermodynamic, continuum, physical-mass and
all-group obligations remain open. Evidence:
`audits/AUDIT-WILSON-COMPLEX-RESPONSE-FLOOR-2026-09-24.md`.

New partial J02 evidence: `CRealSeminormPairingCompletion.completedInner_diagonal_le_normCeiling`
(`lean/YMGap/Continuum/CRealSeminormPairingCompletion.lean:221`) transports
the computed dense-stream ceiling to the completed diagonal by an explicit
`max n normBase` reindex and the constructive one-sided limit principle.
`BF4WilsonAllNomeCenteredVector.centeredVector_norm_ceiling`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:180`) and
`BF4WilsonAllNomeDyadicExcitation.dyadicExcitation_norm_ceiling`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicExcitation.lean:52`) specialize
that cap to actual centered Wilson vectors and every padded dyadic square.
The three focused checks exit 0 within `{propext, Quot.sound}`.  The cap is
expression/width/nome dependent, not uniform, and supplies neither a response
floor nor scaling, thermodynamic, continuum, physical-mass, or all-group
closure. Evidence:
`audits/AUDIT-WILSON-COMPLETED-NORM-CEILING-2026-09-24.md`.

New partial J02 evidence: `BF4WilsonAllNomeComplexGap.complex_twoStep_form_gap`
(`lean/YMGap/Continuum/BF4WilsonAllNomeComplexGap.lean:97`) consumes the
complexification on the SAME all-nome Wilson completion.  The module also
proves `complexUnit_fixed` (`:53`),
`complexTime_preserves_orthogonal` (`:74`), and the exact complex
vacuum-orthogonality criterion (`:64`).  Its 11-declaration focused check is
within `{propext, Quot.sound}`.  This is a fixed nome/width consequence only:
the displayed strict-gap node remains scoped as recorded, and no scaling,
continuum, physical-mass or all-group conclusion is supplied.  Evidence:
`audits/AUDIT-WILSON-COMPLEX-GAP-2026-09-24.md`.

New partial J02 evidence: `BF4WilsonAllNomeComplexification` constructs a
two-component complexification of the EXISTING all-nome Wilson completion.
`valueConj_mul`, `inner_conj_symm`, `inner_posdef`, `inner_smul_right`,
`inner_smul_left`, and `inner_time_balance` retain the actual completed pairing
and original completed time, with explicit `CReal` scalar approximation data.
The 27-declaration focused check is within `{propext, Quot.sound}`.  This adds
fixed-parameter complex structure only; the drafted complex strict-gap consumer
is not yet verified, and no chart node closes.  Full reflected OS/Hilbert
reconstruction, scaling survival, A03, continuum limits, physical mass and
every-group construction remain open.

New partial J02 evidence: `BF4WilsonAllNomeCompletedRealScalar.completedRealSmul`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedRealScalar.lean:85`) constructs
real scaling on the existing Wilson completion, with explicit QCauchy scalar
data; `.completedTime_realSmul` (`:129`) preserves actual time. The scalar
algebraic laws have computed sum/product moduli. `BF4WilsonAllNomeUnitProjection.unitProjection`
(`lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:87`) computes the
actual vacuum component, and `.centeredPart_time_pairing` (`:231`) realizes
connected correlations for arbitrary completed vectors under that SAME
time map. `BF4WilsonAllNomeCenteringPin.centeredPart_embed`
(`lean/YMGap/Continuum/BF4WilsonAllNomeCenteringPin.lean:75`) identifies
this centering with the preceding dense centered vector. No modulus is
extracted from legacy CReal, no face-span carrier is replaced, and no scaling
estimate or full Hilbert/OS/QFT conclusion is supplied. J02 remains open.

New A03 route limitation: `BF4DyadicChannelFloorObstruction.coefficient_ge_nineteenTwenty`
(`lean/YMGap/Continuum/BF4DyadicChannelFloorObstruction.lean:114`) proves that
paying 960*(1-w^L)^2 through the candidate iterated endpoint floor requires
C>=1920, for 0<w<1 and L>=2. Its dyadic specialization (`:135`) includes
every side 2^(scale+1). No growing-loop partition floor or physical energy
lower bound is asserted. The useful SAME signed-aggregate/variance comparison
remains open; extending this candidate normalization alone cannot supply it.

- Primary active node: **A03**. Literal Wilson squares now have side L=2^s,
  assigned spacing 2^-s, unit geometric side and a computed spacing modulus.
  Their original increment bound now has an actual SAME centered-vector consumer:
  2*(B(v,v)-B(v,T(L)v))<=384*L^3*(1-w). The cubic cost remains. This is not useful
  relative control without the SAME centered-variance comparison and a
  justified scaling trajectory. The complete signed-source route remains
  available; the preceding coarse coefficient limitation is unchanged.
  A03 stays `[ ]`: no nonzero limiting norm or continuum premise is supplied.
  The six-face floor is now proved at most (1-w)^12, so subtracting the
  available nome-linear loss budget cannot certify a positive response.
  This limits that certificate pair, not actual variance or physical survival.
  The unique-link decomposition now supplies the premises of the proved
  original arbitrary-word and dyadic-square one-link moments. Their exact
  shifted-square identity retains the complete heat complement. The
  selected-action comparison and exact moving placement now yield a positive
  norm floor for every centered dyadic square on the SAME all-nome completion.
  The next join is a useful relative loss/variance or direct response estimate
  on a justified changing-scale family, not another fixed-nome nonzero wrapper.
  The proposed reset amplification is now ruled out as a repair of the
  unchanged cubic-loss certificate. Next analysis targets the signed word
  quadratic before finite Cauchy discards its cross terms, or a stronger
  direct-response route; no sharper estimate is yet claimed.
  The exact fundamental product-heat image is now proved for arbitrary
  distinct-link words and consumed by the original terminal signed cost
  of the growing square. Its actual square heat image is now proved and
  consumed in the complete signed formula 4E+D=2*((1-2*a+b)*M+(1-b)*N).
  The raw-source formula has now been rederived in the actual square's
  spectator channels, retaining their heat weights and original odd mass.
  A constructed cap-four certificate gives the signed geometric budget
  in A and 4A-M at u=w^L. Next: useful complete channel-budget/SAME centered-
  variance control along a justified scaling family, or direct response.
  Neither raw N nor channel A is the physical partition by substitution;
  no interacting eigenvalue or stronger completed scaling estimate is asserted.
- Parallel node: **J02**. The literal all-nome Wilson completion now has
  proved rational linear laws, bilinear pairing, linear time and positive
  definiteness. Signed finite time combinations retain every original
  cross term and preserve the vacuum complement. The positive-square
  argument supplies a concrete plaquette-difference excitation with floor
  `(1-q)^2*starRatio(w)`, positive at each fixed nome and width. It neither
  replaces B01--B03's recorded carrier nor improves the A03 scaling estimate.
  The actual squared distance now supports computed represented limits;
  discrete time commutes with them and the vacuum complement is closed
  under them. This does not select representatives of arbitrary quotient rows.
  Full Hilbert/QFT, scaling survival and the continuum join remain open.
- New checked obstruction: for every `0 ≤ q < 1`, the current computed
  `mixRate^2` exceeds `q` at an explicit positive width. This rules out only
  the computed fixed-width rate as B04's uniform certificate; it does not
  refute the actual transfer operator. The next frontier remains a genuinely
  spatially/spacing-uniform same-object estimate.
- New checked same-carrier compiler: `BF4WilsonAllNomeDyadicRelativeSurvival`
  consumes the actual padded dyadic-square centered loss and norm floor. Its
  `dyadic_response_floor_of_relative_energy` (`:124`) returns a positive
  response under an explicit relative-energy budget, while
  `dyadic_relative_energy_of_loss_budget` (`:140`) composes the existing cubic
  loss bound with an explicit SAME-norm budget and constructively cancels the
  factor two. `dyadic_response_floor_of_loss_budget` (`:154`) composes both.
  The budget is not proved along a changing-scale trajectory; no chart node
  closes.
- New checked backward calibration: `BF4WilsonAllNomeTwoStepMargin` proves
  that any nonzero vacuum-complement state with relative lag-two loss `delta`
  forces `1-delta ≤ twoStepRate`, equivalently
  `1-twoStepRate ≤ delta`. This constrains the existing fixed-parameter rate
  but supplies neither the loss estimate nor a physical mass normalization.
- New rationalized budget interface:
  `dyadic_relative_energy_of_rational_loss_budget` reduces the completed
  quotient-real budget to the explicit rational inequality
  `dyadicLossBound ≤ 2*delta*starRatio w`, using the existing SAME-state norm
  floor. The rational inequality remains open along scaling; no chart node
  closes.
- New checked certificate-number obstruction:
  `BF4WilsonAllNomeDyadicRationalBudgetObstruction.no_rational_loss_budget`
  proves that the explicit cubic formula cannot satisfy the proposed rational
  budget under any coarse defect floor `rho ≤ 1-w` and admissible
  `delta,theta`. This is not an actual-loss lower bound and does not identify
  `rho` with `starRatio`; it redirects A03 to a sharper SAME-object loss or a
  different response/scaling certificate. No chart node closes.
- The obstruction is now packaged as the explicit Type-level
  `CoarseBudgetData` bundle, with `coarse_budget_data_empty` proving that the
  proposed budget has no inhabitant under `0 < 1-w`. This is a constructive
  no-go, not an actual-loss lower bound.
- New checked bridge expansion: `BF4WilsonOSBridgeSpec.SameObjectBridge`
  (`lean/YMGap/Continuum/BF4WilsonOSBridgeSpec.lean:29`) names the exact
  carrier-map, pairing, step, vacuum, and orthogonality data needed to identify
  the literal all-nome Wilson completion with the separate strict OS carrier.
  `OSFormGap` (`:48`) keeps the OS-side two-step inequality as an explicit
  input, and `transfer_twoStep_form_gap` (`:102`) transports it constructively
  to the Wilson side. `OSFormFamily` (`:62`) and
  `transfer_form_family` (`:121`) now expose the corresponding arbitrary-lag
  consumer needed for same-object correlator decay. The new
  `OSRelativeLossFamily` (`:76`) and `transfer_relative_loss_family` (`:138`)
  expose the relative-energy defect needed by the survival compiler. All
  focused consumers report empty axiom sets. No bridge inhabitant is supplied,
  so J02, B04/B05, the continuum joins, physical mass, and the Clay target
  remain open.
- Goal-node status changes: **NONE**.
- Displayed wording/layout/symbol changes: **NONE**. The chart block is
  unchanged; this snapshot records a new typed bridge expansion only.

## Maintenance contract

1. Read this file before every chart. Copy its chart block; do not regenerate
   the arrangement or paraphrase labels. Always show the whole-project goal.
2. Change a proof marker only with evidence covering the EXACT node's
   carrier, action, quantifiers, parameters and limits. Record the old marker,
   new marker, declaration, verification scope and reason here.
3. Record partial proofs and conditional compilers as evidence/activity;
   do not rename or silently shrink their parent goal node.
4. Keep activity separate from proof status. Record movements of the primary
   frontier by old/new ID; list parallel work separately.
5. Necessary wording, geometry or semantic corrections require a new schema
   version, explicit old-to-new ID/label mapping, and a user-facing explanation.
   Preserve superseded versions in Git; never recycle IDs or silently add glyphs.
6. Every delivered update states what mathematically changed since the last
   snapshot. Say "no status change" when appropriate. Formatting is not progress.
7. Refuted shortcuts go in the evidence/change record; they do not replace
   original goal nodes. This contract does not freeze an erroneous mathematics
   claim: correct it explicitly, with evidence and migration history.

## Snapshot history

| Schema / snapshot | Date (UTC) | Change |
|---|---|---|
| 1 / 1 | 2026-09-24 | Freeze last displayed chart; add permanent IDs, fixed meanings and evidence rules. No goal-node status change. |
| 1 / 2 | 2026-09-24 | Sharp complex Cauchy--Schwarz and explicit matrix-coefficient consumer on the SAME completion. Partial J02 evidence only; no chart-block or goal-node status change. |
| 1 / 3 | 2026-09-24 | Quantitative original-source geometric energy budget with signed correction retained. Partial A03 evidence only; SAME variance/scaling comparison open. No chart-block or goal-node status change. |
| 1 / 4 | 2026-09-24 | Spectator-retaining geometric budget, coefficient-one contraction, and SAME moments with exactly four active heat blocks. Partial A03 evidence only; channel-aggregated SAME variance/scaling comparison open. No chart-block or goal-node status change. |
| 1 / 5 | 2026-09-24 | Complete original-source local angular bound and explicit one-link harmonic-tail modulus at fixed nome. Partial A03 evidence only; conditional spectator quadratic and SAME variance/scaling comparison open. No chart-block or goal-node status change. |
| 1 / 6 | 2026-09-24 | Conditional original-kernel mixed positivity and computed harmonic tails in the SAME actual spectator-channel quadratic. Partial A03 evidence only; joint four-link heat and SAME variance/scaling comparisons open. No chart-block or goal-node status change. |
| 1 / 7 | 2026-09-24 | Computed positive floor comparing the SAME original channel norm with the ORIGINAL partition, and its direct original-energy consumer, independent of width/depth/late cutoff at fixed nome. Partial A03 evidence only; SAME centered-variance/scaling comparisons open. No chart-block or goal-node status change. |
| 1 / 8 | 2026-09-24 | The computed normalized coefficient is at least 32; this limits that certificate, not actual energy. ORIGINAL transfer positivity sharpens E<=norm and the existing centered approximation retains the same epsilon in energy. Partial A03 evidence only. No chart-block or goal-node status change. |
| 1 / 9 | 2026-09-24 | Literal dyadic Wilson squares, fixed-width all-nome reflected form, exact two-time moment pin and SAME-form cubic-cost loss bound. Partial A03/J02 evidence only; no completion substitution or scaling-survival conclusion. No chart-block or goal-node status change. |
| 1 / 10 | 2026-09-24 | Literal all-nome represented completion and pairing, actual positive contractive time semigroup, fixed unit, invariant orthogonal sector and SAME-operator loop moments/loss. Partial J02 evidence only; strict same-carrier gap, centered scaling survival and full Hilbert/QFT remain open. No chart-block or goal-node status change. |
| 1 / 11 | 2026-09-24 | Original arbitrary-Wilson covariance, rational-centered dyadic cap removal and strict two-step bound on EVERY unit-orthogonal state of the SAME all-nome completion. Nome/width dependence remains; partial J02 evidence only. No face-span carrier identification, chart-block or goal-node status change. |
| 1 / 12 | 2026-09-24 | Actual centered Wilson vectors, positive plaquette norm/one-step response, and SAME centered square loss. The coarse six-face-floor/nome-linear-loss certificate pair cannot certify positive response. Partial A03/J02 evidence only; no carrier substitution, scaling-survival conclusion, chart-block or goal-node status change. |
| 1 / 13 | 2026-09-24 | SAME rational completion algebra, bilinear/linear time, definite pairing and exact signed finite-orbit correlators. A positive-square bound supplies a quantitatively nonzero plaquette time difference at fixed nome/width. Partial J02 only; no A03 improvement, carrier substitution, scaling-survival conclusion, chart-block or goal-node status change. |
| 1 / 14 | 2026-09-24 | SAME squared distance and computed represented limits; actual time commutes with limits and the vacuum complement is closed under them. Literal selected-link head-tail geometry supplies an A03 precursor, not arbitrary-word Haar moments or scaling variance. Partial J02/A03 only; no carrier substitution, chart-block or goal-node status change. |
| 1 / 15 | 2026-09-24 | Original arbitrary-word and literal dyadic-square first/second Haar moments, retaining the full selected-link heat complement. Exact rationally shifted square equals (1+c*c) times its unchanged spectator integral. Partial A03 only; full-action variance/scaling comparison remains open. No carrier substitution, chart-block or goal-node status change. |
| 1 / 16 | 2026-09-24 | Original selected-action variance with actual mean/partition, exact moving placement, and positive norm floor/nonzero dyadic-square states on the SAME all-nome completion. Partial A03/J02 only; changing-scale survival and cubic-loss control remain open. No carrier substitution, chart-block or goal-node status change. |
| 1 / 17 | 2026-09-24 | The proposed multi-link reset floor cannot pay the existing cubic response-loss budget, even for every actual selected sublist of square edges. Certificate obstruction only; next A03 analysis repointed to signed relative loss or direct response. No actual-variance upper bound, carrier substitution, chart-block or goal-node status change. |
| 1 / 18 | 2026-09-24 | Exact fundamental product-heat image for arbitrary distinct-link words, actual growing-square distinctness/fringe independence, and original terminal signed-cost consumer. The square heat image and useful SAME variance/scaling comparison remain open. Partial A03 only; no interacting eigenvalue, carrier substitution, chart-block or goal-node status change. |
| 1 / 19 | 2026-09-24 | Exact label-two and full fundamental-square product-heat images for arbitrary distinct-link words, specialized to the actual growing square and consumed in its complete signed terminal-energy formula. Useful SAME interacting centered-variance/scaling comparison remains open. Partial A03 only; no interacting eigenvalue, carrier substitution, chart-block or goal-node status change. |
| 1 / 20 | 2026-09-24 | Actual growing-square spectator channels preserve original energy and odd mass. The constructed cap four supplies a signed geometric budget at u=w^L with all spectator heat retained. SAME original-normalization/centered-variance scaling comparison remains open. Partial A03 only; no completed scaling improvement, carrier substitution, chart-block or goal-node status change. |
| 1 / 21 | 2026-09-24 | The candidate iterated endpoint floor forces a coefficient of at least 1920 even for the quadratic channel-budget remainder. Numerical normalization obstruction only; no growing-square partition comparison or actual energy lower bound. A03 remains open; no chart-block, scope or goal-node status change. |
| 1 / 22 | 2026-09-24 | Actual explicit-modulus real scaling, algebraic laws, computed vacuum projection and same-operator connected correlations on the existing Wilson completion. Exact equality with the preceding dense centered state is proved. Partial J02 only; no new scaling estimate, carrier substitution, full Hilbert/QFT closure, chart-block or goal-node status change. |
| 1 / 23 | 2026-09-24 | Two-component complexification of the SAME all-nome Wilson completion, with explicit constructive-real scalar data, Hermitian positive-definite pairing, and original-time balance. Focused check passed 27 declarations within the permitted axiom gate. Partial J02 only; the complex consumer, A03 scaling estimate, continuum/QFT closure and all goal markers remain open. |
| 1 / 24 | 2026-09-24 | The SAME complex Wilson carrier now consumes the existing unit and transfer: unit fixation, vacuum-sector preservation and an 11-declaration fixed-parameter strict two-step bound are kernel-checked within the permitted axiom gate. No scaling, continuum, physical-mass, all-group or chart-node closure. |
| 1 / 25 | 2026-09-24 | The SAME complex Wilson gap is now exposed as an exact translated discrete correlator bound at indices n and n+2 for every translated vacuum-orthogonal state. Partial J02 only; no spacing/scaling, continuum, physical-mass, all-group or chart-node closure. |
| 1 / 26 | 2026-09-24 | The translated complex correlator is rewritten as a same-carrier norm-square contraction at the intervening time slice. Focused check passed within the permitted axiom gate. Partial J02 only; no spacing/scaling, continuum, physical-mass, all-group or chart-node closure. |
| 1 / 27 | 2026-09-24 | The same-carrier norm contraction is iterated constructively, giving `twoStepRate^n` decay for every discrete power at fixed nome/width. Focused check passed within the permitted axiom gate. Partial J02 only; no spacing/scaling, continuum, physical-mass, all-group or chart-node closure. |
| 1 / 28 | 2026-09-24 | The iterated same-carrier norm estimate is converted into an even-lag same-object correlator bound at lag `2*n`. Focused check passed within the permitted axiom gate. Partial J02 only; no spacing/scaling, continuum, physical-mass, all-group or chart-node closure. |
| 1 / 29 | 2026-09-24 | Even-lag same-object correlators are proved nonnegative, and the scalar `twoStepRate^n` coefficient receives an explicit cutoff under an honest strict-positivity premise. Focused check passed within the permitted axiom gate. Partial J02 only; no spacing/scaling, continuum, physical-mass, all-group or chart-node closure. |
| 1 / 30 | 2026-09-24 | The same complex carrier now has a conditional response-floor compiler: an explicit norm cap plus response floor implies `floor ≤ twoStepRate^n*C`. Focused check passed within the permitted axiom gate. No chart-block or goal-node status change; cap/response production and all scaling/continuum obligations remain open. |
| 1 / 31 | 2026-09-24 | The computed per-stream norm ceiling now reaches the completed diagonal and specializes to actual centered Wilson and padded dyadic-square states. Focused checks passed within the permitted axiom gate. The cap is not scale/width uniform and does not produce a response floor or close any chart node. |
| 1 / 32 | 2026-09-24 | Same-carrier plaquette response squared into a positive lag-two floor, with spatial padding. Fixed nome/width only; no chart-block or goal-node status change. |
| 1 / 33 | 2026-09-24 | Same-carrier plaquette floor calibrated against `twoStepRate * plaquetteNormCeiling`. Fixed nome/width only; no chart-block or goal-node status change. |
| 1 / 34 | 2026-09-24 | Same-carrier normalized plaquette response floor and fixed-parameter rate positivity. Scaling and continuum joins remain open; no chart-block or goal-node status change. |
| 1 / 35 | 2026-09-24 | Honest obstruction: the computed `twoStepRate = mixRate^2` has no positive width-uniform bound below one. This redirects B04 to a new analytic rate or genuine spatial/spacing control; no chart-block or goal-node status change. |
| 1 / 36 | 2026-09-24 | The literal origin plaquette now discharges fixed-parameter `twoStepRate > 0` after two padding layers, and the existing complex-rate cutoff is instantiated without a positivity premise. This is coefficient-level finite-parameter evidence only; no chart-block or goal-node status change. |
| 1 / 40 | 2026-09-24 | The explicit cubic dyadic loss formula is arithmetically incompatible with the proposed rational budget under any abstract coarse defect floor `rho ≤ 1-w`; certificate obstruction only, with no actual-loss lower bound or chart-block/goal-node status change. |
| 1 / 41 | 2026-09-24 | The coarse rational budget is packaged as Type-level `CoarseBudgetData`, and `coarse_budget_data_empty` proves its constructive emptiness under `0 < 1-w`; no chart-block or goal-node status change. |
| 1 / 42 | 2026-09-24 | Minimal typed Wilson-to-OS bridge interface and constructive two-step form-bound consumer checked with an empty axiom set. No bridge inhabitant or chart-node status change. |
| 1 / 43 | 2026-09-24 | Added the lag-indexed OS form-family interface and its equality-only Wilson transport consumer; both are axiom-free. No bridge inhabitant or chart-node status change. |
| 1 / 44 | 2026-09-24 | Added the lag-indexed OS relative-loss family and equality-only Wilson transport consumer; the focused check is axiom-free. No bridge inhabitant or chart-node status change. |
| 1 / 45 | 2026-09-24 | Proved a fixed-parameter complex Wilson relative-loss inequality and an explicit width modulus showing the computed original-response witness has no positive width-uniform floor. Both focused checks stay within `{propext, Quot.sound}`; no chart-node status change. |
| 1 / 46 | 2026-09-24 | Added the exact lag-two relative-loss bridge interface and equality-only transport consumer; the focused check is axiom-free. No bridge inhabitant or chart-node status change. |
| 1 / 47 | 2026-09-24 | Embedded the actual plaquette excitation into the complex Wilson carrier and proved its orthogonality, norm/response floors, relative loss, and even-lag decay. Fixed-parameter same-object evidence only; no chart-node status change. |
| 1 / 48 | 2026-09-24 | Rewrote the existing finite physical SU(2) form gap as relative loss on the literal moving-centered cube same-object autocorrelation, with explicit `cutoffUniformRate w` margin positivity. No chart-node status change. |
| 1 / 49 | 2026-09-24 | Added a separate dynamic family form-gap certificate and inhabited it for the fixed-`w=1/2` geometric staging family; the moving-cube RC channel now has scale-wise relative loss. No chart-node status change. |
| 1 / 50 | 2026-09-24 | Exposed the dynamic form-gap relative-loss coefficient through the global completed Markov transfer on the identical embedded vector by equality transport. No chart-node status change. |
| 1 / 51 | 2026-09-24 | Factored the scale-indexed completed Markov-form Cauchy--Schwarz input and composed it with the form gap into the literal same-object squared-norm estimate. The CS family remains open; no chart-node status change. |
| 1 / 52 | 2026-09-24 | Inhabited the dynamic Markov-form Cauchy--Schwarz family from the existing adaptive producer and added an input-free same-object squared-norm consumer. No chart-node status change. |
| 1 / 53 | 2026-09-24 | Added the inhabited `w = 1/2` geometric form-gap family, explicit rate pin, and non-vacuous moving-cube same-object squared-norm estimate at every geometric scale. No chart-node status change. |
| 1 / 54 | 2026-09-24 | Inhabited the fixed-family scale-uniform moving-cube norm floor and transported it to every scheduled zero-time same-object autocorrelation. The cutoff limit and scaling nodes remain open. |
| 1 / 55 | 2026-09-24 | Proved the reciprocal-square normalization debt is constant in the fixed `w = 1/2` geometric family and constructed its zero rational variation. The normalized-limit consumer's debt input is now inhabited; raw representative variation remains open. No chart-node status change. |
| 1 / 56 | 2026-09-24 | Proved the fixed-family reciprocal normalization scale is constant, inhabited the generic global ceiling, and derived the shared raw norm-floor/fourth-power debt consequences. Raw and positive-time rate variation remain open. No chart-node status change. |
| 1 / 57 | 2026-09-24 | Proved the exact fixed-family geometric floor sampler is `time * 2^scale`, reducing the positive-time stream to explicit dyadic-exponent arithmetic. The antitone-tail variation, scaling, and continuum joins remain open. No chart-node status change. |
| 1 / 58 | 2026-09-24 | Added and checked an order-antitone geometric tail certificate for every rational base in `(0,1)`, using `qCeilNat`; fixed-family stream-specific step bounds remain open. No chart-node status change. |
| 1 / 59 | 2026-09-25 | Constructed and checked the full positive-time rational variation certificate for the exact stream `r^(time * 2^scale)`; equality transport to the large normalized compiler remains open. No chart-node status change. |
| 1 / 60 | 2026-09-25 | Proved constructively that the completed CReal limit of the exact positive-time geometric stream `r^(time * 2^scale)` is zero. This rules out positive physical-mass calibration by this spacing family; the compiler bridge and a replacement physical-rate family remain open. No chart-node status change. |
| 1 / 61 | 2026-09-25 | Transported the fixed-family variation certificate to the literal normalized scheduled-rate stream and inhabited its all-time rational variation input. Raw connected-moment variation remains open; no chart-node status change. |
| 1 / 62 | 2026-09-25 | Converted the fixed-family pointwise-constant normalization debt into the constructive-real debt-variation input alongside the inhabited normalized scheduled-rate input. Raw same-object CReal variation remains open; no chart-node status change. |
