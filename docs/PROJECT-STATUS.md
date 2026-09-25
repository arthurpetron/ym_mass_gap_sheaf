# Canonical one-page project status

Chart schema: **1**. Snapshot: **36**, 2026-09-24 UTC. Source checkpoint:
the SAME all-nome Wilson origin-plaquette complex-rate cutoff milestone
committed with this snapshot;
verification is recorded in
`audits/AUDIT-WILSON-ORIGIN-COMPLEX-CUTOFF-2026-09-24.md`.
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
- Goal-node status changes: **NONE**.
- Displayed wording/layout/symbol changes: **NONE**. The chart block is
  unchanged from snapshots 1--35; this snapshot records only new proof evidence.

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
