# Forward-backward audit: actual constructions and the Clay endpoint

Date: 2026-10-11 Pacific; source inspection continued on 2026-10-12 UTC.
Baseline: `9503edc0`, with the current uncommitted local coefficient work.
This is a source/planning audit, independently reviewed in both directions,
not a repository-wide build or a new continuum proof.

WHOLE-PROJECT GOAL: constructive nontrivial continuum quantum Yang-Mills on
R^4 for every compact simple gauge group, with the required same-theory QFT
axioms, unique vacuum and finite positive physical Hamiltonian mass gap.
The whole-project goal remains OPEN.

## 1. Backward branching: what an actual final witness must supply

Jaffe-Witten sections 3-4 require the indicated axiomatic strength, spacetime
symmetry, positive energy and vacuum, local gauge-invariant curvature fields,
the required short-distance identification, and a positive finite mass for
each compact simple group. A fixed lattice model or scalar rate is not that
theory. Confinement, a particular cluster expansion, and a common numerical
gap for all groups are not required proof methods. Source:
[official problem description, pp. 5-6](https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf).

Within the repository's constructive method, branch backward into:

1. A realized group G and a SAME-theory continuum observable functional, with
   actual local-field/Yang-Mills identification. An arithmetic Lie-type code
   is not the group or its interacting theory.
2. The physical reflected carrier of that functional, complex quantum-field
   structure, supported local observables, spacetime covariance/locality,
   vacuum and actual physical dynamics. An ordinary Euclidean GNS norm is
   not automatically the reflected physical norm.
3. A positive gap for EVERY state orthogonal to the vacuum, on those dynamics.
   A single surviving excitation supplies a different requirement: excluding
   a trivial limit and, with the spectral identification, an infinite mass.
4. Explicit witnesses and quantitative approximation/modulus data for the
   chosen constructive realization. This is the repository's method
   constraint, not a claim that Clay mandates this specific lattice route.

The selected sufficient lattice branch expands item 1 into original-action
stage observables, controlled heat-label removal, thermodynamic/spacing
limits, renormalized field approximations and their provenance. These are
route obligations, not an assertion that every possible solution must use
heat kernels, H1, a particular RG recursion or a sigma-additive measure.

Existing useful specifications are
`lean/YMGap/Continuum/CanonicalOSRoot.lean:84`, `ReferenceWeightStageFamily`;
`:121`, `CanonicalSchwingerLimit`; and `:268`, `PositiveTimeOSRoot`.
`approximationConverges:147` demands separate volume/spacing moduli.
`physicalHilbert:513` constructs completion only AFTER the reflected root
is supplied. These are genuine handoffs, not original-Yang-Mills inhabitants.

## 2. Forward branching: what the current source actually provides

Short paths in the following table are under `lean/YMGap/Continuum/`, except
where an explicit full path is supplied.

| Forward branch | Source-backed result | Boundary that must remain visible |
|---|---|---|
| Original finite source -> actual completed response/cost | `BF4WilsonAllNomeOriginalRayleighLimit.lean:96`, `originalOwnBlockVariance_pin`; `:104`, `originalOwnBlockCost_pin`; convergence `:130`, `:143` | SAME OLD center and distinct chronological masses; fixed width/nome/expression. No uniform changing-family relative estimate. |
| Original signed family -> initial nonzero state | `BF4WilsonAllNomePlaquetteFamilyVariance.lean:151`, `familyExcitation_norm_floor`; `BF4WilsonAllNomeShiftedPaddedNondegenerate.lean:191`, `pathShiftedNondegenerate_of_padded` | Actual positive per-member floors. They can become tiny; they do not prove late continuum survival. |
| Original completion -> every-state strict T^2 bound -> decay | `BF4WilsonAllNomeCompletedGap.lean:147`, `completed_twoStep_form_gap`; `:214`, `completed_iterated_norm_gap`; `:234`, `completed_even_lag_corr_decay` | Fixed nome/width. The rate is not a uniform physical scaling rate. |
| Strong-coupling branch -> spatially uniform rate | `BF4WilsonAllNomeStrongCouplingUniformRate.lean:443`, `allNome_strongCoupling_vacuumSq_all_widths`; `:453`, explicit pilot | Real all-width result in its three small-nome guards, not an AF near-one result. |
| Original physical bond sector -> continuous numerical time and logarithm | `BF4WilsonAllNomeBondOSRealization.lean:74`, `image_pairing`; `BF4WilsonAllNomeBondOSRealTime.lean:63`, `action`; `:71`, `action_value`; `BF4WilsonAllNomeBondOSLogarithm.lean:48`, `transfer`; `:112`, `domain_logarithm_tail_bound`; `:136`, `representedLogarithmCertificate` | These operators exist; do not rebuild them. Their continuum physical-clock and full local-QFT identification remain separate. |
| Original bulk correlations -> small-nome spatial limit | `BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:85`, `jointLimits_spatial_converge`; `BF4WilsonOriginalBulkComparison.lean:588`, `bulkConnected_spatial_close`; `:628`, `bulkConnected_included_spatial_close` | SAME-action scalar bulk comparison, including larger ambient widths, in the guarded regime. Not a near-one changing-family limit. |
| Coupling variation -> original normalized comparison | `BF4WilsonAllNomeTimeCoupling.lean:158`, `joint_coupling_tolerance_bound` | Absolute finite-chain budget; it does not pay the relative late response or eliminate its width/face-count dependence. |
| Constructive compact-group foundations | `lean/YMGap/RepTheory/RationalQuaternionCauchyGroup.lean:389`, `completedGroup`; `lean/YMGap/RepTheory/RationalQuaternionCompletedMatrix.lean:189`, `representation_injective`; `QuaternionRepresentedHaar.lean:308`, `integral_translate` | Actual quaternion group/Haar/representation work, not the other groups' interacting continuum constructions. |

The local Cayley density attempt failed three narrow checks and is parked in
`audits/drafts/BF4ExactSlabCayleyGaugeDensity.lean.txt`, outside the Lean library.
It is NOT checked or registered. The already checked source expansion
`BF4ExactSlabPlaquetteCayleyExpansion.lean:529`,
`original_plaquette_cayley_cleared`, remains a local source identity, not a
Gaussian measure comparison or uniform remainder.

## 3. Where the branches meet, conditionally meet, or fail to meet

| Backward demand | Exact forward-to-backward connection | Status of the meeting |
|---|---|---|
| Actual original fixed-carrier dynamics | `BF4WilsonAllNomeBondOSRealization.image_pairing:74` and `BF4WilsonAllNomeBondOSRealTime.action_value:71` preserve the original pairing/time action; logarithm uses the same time-one operator | Actual fixed-carrier meeting. Physical spacing/continuum passage is not part of it. |
| ONE normalized positive-time excitation | `BF4WilsonAllNomeShiftedH1Anchor.lean:581`, `path_normalized_anchor_shifted`, with the produced padded floor via `BF4WilsonAllNomeShiftedPaddedNondegenerate.lean:225`, `path_normalized_anchor_shifted_padded` | Conditional meeting. Missing PRIMARY is exactly the positive-scale endpoints at `ShiftedH1Anchor:718`, `pathShiftedEpsBound_iff_positiveScales`. |
| Dense relative-energy producer -> SAME completed H1 -> positive BOX | `BF4WilsonAllNomeOriginalRayleighLimit` pins the literal finite cost/variance; `BF4WilsonAllNomePositiveOrbitResponseOrder.lean:624`, `positiveOrbit_response_retention`, transfers raw retention to positive smoothing | Existing sufficient route. Missing analytic producer, not missing smoothing/completion machinery. Raw control is optional; direct BOX control remains eligible. |
| EVERY-state physical decay | `BF4WilsonAllNomeWilsonMixRateDeadEnd.lean:132`, `WilsonAFPaddedGapInput`; `:144`, `wilsonGapBranch_afPadded_generic` | Conditional only. Actual scale-sized all-vector rate input is not constructed. H1 does not fill it. |
| Same continuum functional -> reflected physical Hilbert space | `CanonicalOSRoot.CanonicalSchwingerLimit:121` -> `PositiveTimeOSRoot:268` -> `physicalHilbert:513`; `MeasureLinkedOSReconstruction.lean:54`, `ProjectiveOSFunctionalIdentification`, retains provenance | Required original stage/limit, support and reflected-form inputs remain unsupplied on the physical changing family. |
| Finite positive physical mass | `BF4WilsonSpatialUnionPhysicalCalibration.lean:75`, `currentPhysicalRate`, dimensionalizes supplied spacing; `:240`, `fixedMass_no_finite_physical_ceiling`, rejects a fixed mass divided by vanishing spacing | Conversion is proved; actual scale-setting and changing-rate identification are not. The fixed-carrier shortcut is refuted. |
| Local curvature fields and UV behavior on THAT functional | `LocalCurvatureFields.lean:165`, `LocalCurvatureFields`; `:320`, `LocalOperatorContent` | No adequate meeting: the present legacy fields do not pin their own functional to the supplied continuum theory or bound actual OPE errors. |
| Every compact simple group | `lean/YMGap/Rubric/ClayResolutionRoot.lean:38`, `PinnedSimpleLieType`; `lean/YMGap/MassGap/SimpleGroup.lean:627`, `GroupBoundGap` | Classification is not realization. `GroupBoundGap.row_eq_su2:635` explicitly confines that provenance to SU(2). |

Full paths in the first six rows are under `lean/YMGap/Continuum/`.
Several branches already join at fixed parameters. None of these source
connections yields the entire continuum endpoint without the indicated
producer estimates and identifications.

For a sheaf/descent interpretation, the overlap data must be actual
observable/functional maps, null-equivalence compatibility, quantitative
errors and dynamics intertwining. Names or scalar-floor equalities do not
glue measures or Hamiltonians. Exact bare cross-spacing projective consistency
is not assumed by `CanonicalOSRoot.ReferenceWeightStageFamily:84`.

In particular `BF4WilsonAllNomeWidthInclusionObstruction.lean:232`,
`no_completed_literal_inclusion`, refutes full literal completed-width descent.
Use controlled bulk/renormalized observable comparisons, not that full map.
The fixed-carrier presheaf arrows recorded in `docs/PROJECT-STATUS.md` remain
useful fixed-carrier arrows, not a proved continuum sheaf-descent theorem.

## 4. Target-specification traps that change the execution strategy

Preserve existing declaration fields; do not optimize toward an inadequate
bundle or silently alter it.

- `lean/YMGap/Rubric/FrontierDAG.lean:101`, `FrontierDAG`, stores a selected
  fusion/KP/associator/bounded-H route, not all of the actual endpoint content.
  Its header's claim that an inhabitant closes the problem is not justified
  by those fields. `Continuum/Tier0Scorecard.lean:293` already distinguishes
  its historical inventory from an exact census of Clay requirements.
- `lean/YMGap/Continuum/FunctionalContinuumTarget.lean:115` itself warns that
  its Euclidean slot is too weak; its freely supplied GNS data do not create
  the SAME reflected continuum reconstruction.
- `lean/YMGap/Continuum/LocalCurvatureFields.lean:165` chooses an unrelated
  algebra/functional. `StressTensor:213` contains one-point conservation;
  `OPE:242` lacks an operator-product-error inequality. The trivial instances
  `localCurvatureFields_triv:186` and `ope_triv:260` therefore do not pay the
  intended physical obligations.
- `lean/YMGap/Continuum/FourDExistence.lean:487`, `ContinuumYMWithGap`, already
  stores a gap. `ym_mass_gap_of_existence:521` projects it; that theorem does
  not derive a physical gap from mere continuum existence.
- `lean/YMGap/MassGap/SimpleGroup.lean:615`, `SU2WilsonOrigin`, forces the
  SU(2) row. Group-indexed scalar arithmetic or caller-supplied reconstruction
  cannot be counted as every-group interacting construction.

These findings constrain claims and work selection now. Correcting full
formal endpoint statements requires a separate reviewed specification
change, not manufacturing additional inhabited surrogate certificates.

## 5. Efficient execution order and effort estimates

1. Finish or park the already bounded local-identity cleanup. It has no
   authority to expand into another completion/gauge interface. It is not
   the critical analytic path.
2. PRIMARY: prove the SAME ORIGINAL endpoint estimate on a justified changing
   family, or its optional direct original-energy sufficient producer.
   Keep the direct BOX route available if the raw sufficient estimate proves
   too strong. No new cost/normalization/smoothing adapter is selected.
3. Independently seek ORIGINAL-action scale-setting and controlled
   cross-scale/local-field convergence. A numerical AF schedule remains a
   candidate until those physical joins exist.
4. Keep EVERY-state scale-sized decay as a separate analytic branch; survival
   cannot supply its lower physical mass floor. Reuse the fixed-carrier
   dynamics/logarithm rather than reconstructing them again.
5. Advance local-field/QFT and group foundations in parallel only when a
   concrete available input produces a real missing object or estimate.
   Freeze purely assumptive interface expansion. A bounded independent
   reviewer checks SAME-object joins; root alone runs narrow Lean checks.

| Remaining work | Effort/time assessment |
|---|---|
| This source audit, plan checkpoint and dispatch | One working session; planning budget 2-6 focused agent-hours, not a mathematical completion estimate. |
| A finite identity after the mathematical proof is known | Typically hours to a few focused days of proof engineering; dependent on the exact reduction/certificate cost. |
| Selected next analytic-producer probe | Allocate 1-2 focused research days before a continue/revise/prune decision. This is a probe budget, NOT a promise to prove its uniform estimate. |
| Changing-family estimates and scale-setting | Major unsolved analytic research; no defensible completion deadline from the present source. |
| Same-theory continuum/local QFT and every-group construction | Multiple major unsupplied constructions. Even after analytic inputs, substantial proof engineering remains; total time cannot honestly be bounded now. |

These are planning judgments, not source-derived facts or a percentage of
Clay completion. Parallel work removes independent engineering delay; it
does not make the missing analytic inputs logically independent or solved.

## 6. Next task begun

The next bounded mathematical task is the viability/quantitative screen of
the OPTIONAL original-energy producer on the literal radius-zero family,
with s=2t, the actual warmed source and the OLD center:

    Z0 * energy(A,phi_k) <= (c_E/s) * Z1 * B.

Its existing finite-cost/limit/positive-BOX consumers must retain both
chronological masses. The aim is a cancellation-preserving simplification
or actual estimate, not another theorem which assumes this bound. Degree
and terminal-depth choices remain explicit per member. A fixed-nome bound
or a Gaussian coefficient with no ORIGINAL-measure relative remainder
does not pay it. The parameter trajectory is not relabeled physically
justified by this task.

A bounded independent mathematical review has completed this first screen.
The existing consumers are
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:264`,
`blockConditionalRatio_energy_error_relative_tolerance`, and
`BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:158`,
`blockConditionalRatio_boundaryDrift_tolerance`, followed by the raw limit
and positive-BOX maps above. Tolerances 1/s produce c0=c_E+2, with no positive
source-norm or inverse-norm premise. Existing positivity/drift instead gives
only `0 <= Z0*E <= (1+comparisonEta)*Z1*B`; the constant-scale bound is unpaid
at the required 1/s scale.

The exact residue is

    E(A,phi_k)=ell_V[A*(T A)*phi_k^2]
               -ell_V[(A*phi_k)*T(A*phi_k)].

Here energy is the literal diagonal-minus-mixed definition
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:63`, `energy`.

The mixed term must cancel nearly all the diagonal; it must not be dropped.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPredictionEnergyNormalized.lean:133`,
`lastStepNoise_prediction_energy_cleared`, pays
outgoing noise by INCOMING energy, not a bound on the latter; its projected
consumer `lastStepNoise_projected_prediction_energy_cleared:208` additionally
retains spatialCeiling. No independent cheaper
producer was found in this screen. This is source/PAPER analysis, not new Lean.

The ensuing calculation directly tests the COMPLETE OLD-centered response.
For `P_e=e^4*(P4+e*P5+e^2*P6+...)`, explicitly assuming
`P4(s)>0` and `P4(s+1)>0`, let
`r0=P4(s+1)/P4(s)`, `u=P5/P4`, `v=P6/P4`, and let Delta denote the value
at s minus that at s+1. Formal finite ratio algebra gives

    s*(1-P_e(s+1)/P_e(s))
      =s*(1-r0)+e*s*r0*Delta u
        +e^2*s*r0*(Delta v-u(s)*Delta u)+higher terms.

P5 must not be silently set to zero for a separately supplied OLD center.
When P5=0, this reduces to the signed P6/P4 difference, not an absolute P6
bound. This ROOT-derived finite coefficient calculation is PAPER and still
needs ORIGINAL density/terminal matching and a denominator-relative
nonperturbative remainder; it does not prove H1. The existing coefficient
groupings in `AUDIT-ADAPTIVE-CONDITIONAL-SCORE-2026-10-07.md` are diagnostics.
No canonical displayed claim changes, no new sorry/axiom or frontier-field
change, and no chart reprint.

ROOT inspected the decisive source definitions and reviewed both independent
audits. Independent complete report/opening-plan/instruction-11 review PASS;
the ratio expansion's positive denominator guards are explicitly retained.
No fresh full-tree verification or new Lean proof is claimed.
