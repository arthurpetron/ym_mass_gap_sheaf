# Parallel frontier review: nonconstant excitation

Date: 2026-09-16. Read-only source review of the Lean tree; no Lean files,
proofs, frontier fields, or build configuration changed and no compiler run.
This report distinguishes already implemented declarations from open consumers.

## Result

**A nonzero, unit-orthogonal excitation on the SAME spatial union carrier is
already constructed. It is not an outstanding prerequisite of the current
strict-bound work.** `BF4SpatialUnionExcitation.excitation` is a concrete
`UnionCompletion` vector, `excitation_orthogonal` proves its actual unit pairing
vanishes, and `excitation_norm_floor` / `excitation_ne_zero` prove a positive
rational squared-norm floor and nonzeroness. These are respectively
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:57`,
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:60`,
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:92`, and
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:110`.

The universal strict bound is also already stated for every vector of this
completed unit complement, not merely for the excitation:
`BF4SpatialUnionCompletedGap.completed_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4SpatialUnionCompletedGap.lean:153`, and
`BF4SpatialUnionUnitComplement.unitComplement_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4SpatialUnionUnitComplement.lean:67`.
The latter's actual transfer is `twoStepTransfer`,
`lean/YMGap/Continuum/BF4SpatialUnionUnitComplement.lean:64`.

## Same-object chain

| Link | Source declaration | What is supplied |
| --- | --- | --- |
| Original observable | `BF4ExactSlabFixedSpatialFaceCharacter.faceCharacter`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceCharacter.lean:52`; `faceSpan`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceCharacter.lean:70` | Fundamental character of the literal plaquette polynomial; a physical radius-zero presentation. |
| Same finite law | `BF4ExactSlabFixedSpatialLocalVariance.chart_variance_floor`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalVariance.lean:61` | First and second moments use the same original selected-chain action and partition. |
| Positive floor | `BF4ExactSlabLocalStarComparison.starRatio`, `lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:46`; `starRatio_positive`, `lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:65` | Exact rational `lowerFactor(w)/upperFactor(w)`, positive for `0<w<1`; not beta/spacing-independent. |
| Joint limiting variance | `BF4ExactSlabFixedSpatialLocalVariance.face_joint_variance_floor`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalVariance.lean:111` | The same floor after heat-cutoff/time-boundary removal. |
| Spatial limiting variance | `BF4ExactSlabFixedSpatialSpatialDenseGap.spatialCenteredFace_floor`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:170` | The same floor after the recentered spatial limit. |
| Actual centered vector | `BF4ExactSlabFixedSpatialSpatialCentralExcitation.centralExcitation`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCentralExcitation.lean:55`; `centralExcitation_norm_pin`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCentralExcitation.lean:65` | Explicit centering stream in the fixed-base reflected completion, with self-pairing pinned to the above scalar variance. |
| Map into union | `BF4SpatialUnionFixedBase.completionMap`, `lean/YMGap/Continuum/BF4SpatialUnionFixedBase.lean:79`; `completedInner_map`, `lean/YMGap/Continuum/BF4SpatialUnionFixedBase.lean:112`; `completionMap_time`, `lean/YMGap/Continuum/BF4SpatialUnionFixedBase.lean:118`; `completionMap_unit`, `lean/YMGap/Continuum/BF4SpatialUnionFixedBase.lean:125` | Quotient descent preserving the mixed pairing, physical discrete time, and unit. No common support base is selected for arbitrary union vectors. |
| Same connected correlator | `BF4SpatialUnionExcitation.excitation_correlator_pin`, `lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:69` | `B(v,T_n v)` equals the union centered moment of the original plaquette at every natural-number lag. |
| Quantitative nonzero vector | `BF4SpatialUnionExcitation.excitation_norm_floor`, `lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:92`; `excitationNormCauchy`, `lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:83` | Positive rational squared-norm floor and explicit Cauchy data for its actual scalar representative. |
| Closed instance | `BF4SpatialUnionSmallNome.excitation`, `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:52`; `excitation_norm_floor`, `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:60`; `twoStep_gap`, `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:66` | All guards supplied at the existing nome `1/1024`; an inhabited actual sector and its universal strict bound. The nome is defined by `BF4ExactSlabPlaquetteSmallNomeCertificate.nome`, `lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`. |

The crucial distinction from a merely positive functional variance is the
implemented `centralExcitation_norm_pin` followed by `completedInner_map`.
The report does not infer reflected nonzeroness from an unrelated ordinary
state-GNS norm.

## Open next excitation-related consumers

1. **Positive response at a nonzero physical time: NOT FOUND on this carrier.**
   Searches of `BF4SpatialUnion*.lean` and
   `BF4ExactSlabFixedSpatialSpatial*.lean` found the zero-time norm floor above,
   nonnegative even-time moments, and strict upper bounds, but not a positive
   rational lower bound on `B(v,T_2 v)` for the actual excitation. The existing
   `BF4SpatialUnionCompletedGap.completed_even_nonnegative`,
   `lean/YMGap/Continuum/BF4SpatialUnionCompletedGap.lean:163`, states
   nonnegativity, not strict positivity. A concrete existing downstream demand
   for a strictly positive response is `CanonicalOSRoot.PositiveTimeOSRoot`
   (`rayleighLowerPositive`, `probeRayleighLower` fields),
   `lean/YMGap/Continuum/CanonicalOSRoot.lean:268`. That canonical interface also
   requires a normalized probe and rational-valued `GNSData`; no union-to-this-
   interface identification is asserted here. This is a distinct useful
   parallel analytic question, not another proof of zero-time nonzeroness.
2. **Continuum nontriviality of this union excitation: NOT FOUND.** Searches in
   `BF4SpatialUnion*.lean`, `BF4ExactSlabFixedSpatialSpatial*.lean`,
   `CanonicalOSRoot.lean`, and the moving-cube continuum-nontriviality modules
   found no spacing-indexed limit/pin for this vector. The current union vector
   depends on the small-nome guards. `BF4SmallNomeAFGuardObstruction.no_fine_guard_on_chart`
   and `no_blocked_guard_on_chart`,
   `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` and
   `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:133`, rule out
   reusing that guard throughout the supplied AF chart.
3. **Existing conditional limit compiler, not a union inhabitant.**
   `MovingCubeRawContinuumNontriviality.ofUniformNormFloor`,
   `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.lean:180`,
   consumes a `DynamicVacuumSectorUniformRCNormFloor` on its exact moving-cube
   channel and a supplied raw scheduled representative variation. Its result
   is `MovingCubeRawContinuumNontriviality`,
   `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler.lean:60`.
   These parameters are not `BF4SpatialUnionSeminorm.UnionCompletion`; no
   equality bridge is supplied by the above excitation declarations.

## Parallel-work disposition

No new wrapper module was added: it would duplicate an already constructed
fixed-spacing witness. The independent actionable residue is the positive
nonzero-time response and the spacing-compatible, same-observable limit with a
surviving quantitative norm floor. The current source already separates the
zero-time floor (`excitation_norm_floor`) from the actual time correlator
(`excitation_correlator_pin`) and makes both available while the parent work
constructs limits and continuity consequences on this carrier.

## Bounded next-step investigation: nonzero-time response

The minimal scalar target is a witnessed rational `c > 0` with
`ofQ' c <= centeredMoment ... 2 centralStage centralStage`. Its exact completed
consumer is the existing `BF4SpatialUnionExcitation.excitation_correlator_pin`
at `n=2`, `lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:69`.
The union's actual self-adjoint balance is
`BF4SpatialUnionGeometry.completedInner_time_balance`,
`lean/YMGap/Continuum/BF4SpatialUnionGeometry.lean:98`, and its semigroup law is
`BF4SpatialUnionSeminorm.completedTime_add`,
`lean/YMGap/Continuum/BF4SpatialUnionSeminorm.lean:137`.
Thus the same response is the squared norm of the actual one-step translate;
it is not the excitation's already positive zero-time squared norm.

There are two precise proof-search targets; neither is currently supplied:

- **Original selected-chain estimate.** Supply a positive rational lower
  bound on the finite `connectedScalar` along the `n=2`, `base=1` recentered
  diagonal, with both arguments the original face and its literal two-step
  translate and with one common chart (for example `H=2`).
  `BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.connectedScalar`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.lean:71`,
  defines this quantity from exactly three moments of one selected action.
  `BF4ExactSlabFixedSpatialSpatialCenteredForm.originalConnected_diagonal_converges`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredForm.lean:127`,
  is the existing limit consumer. The previously listed local-star result
  `chart_variance_floor` has zero lag and identical face insertions, so it does
  not supply this missing two-time estimate.
- **Reuse an already positive original response only after a scalar pin.**
  `BF4ExactSlabOriginalResponseNumeratorFloor.original_numerator_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabOriginalResponseNumeratorFloor.lean:43`,
  proves a full-slab numerator floor for the older shifted plaquette probe.
  The explicit constant is `responseFloor = (1/16)*(1/1024)^36`,
  `lean/YMGap/Continuum/BF4ExactSlabOriginalResponseNumeratorFloor.lean:37`.
  `BF4ExactSlabThermodynamicPositiveResponse.original_response_floor`,
  `lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveResponse.lean:50`,
  transports it to that older thermodynamic response. **Correction from the
  subsequent geometry review:** the old response has endpoint separation
  THREE, not two: `BF4ExactSlabShiftedProbeTubeGeometry.endpoint_separation`,
  `lean/YMGap/Continuum/BF4ExactSlabShiftedProbeTubeGeometry.lean:77`.
  Its bond-reflected norm already includes a one-link separation. A possible
  comparison must therefore target union lag THREE, followed by a separate
  actual-contraction inequality to reach lag two. An equality with the union's
  lag-two scalar must not be assumed. A full isomorphism of completions is not
  needed for this scalar consumer. **A corresponding lag-three scalar pin is NOT FOUND** in
  `BF4SpatialUnion*.lean`, `BF4ExactSlabFixedSpatial*.lean`,
  `BF4ExactSlabThermodynamicProbeResponse.lean`, or
  `BF4ExactSlabThermodynamicPositiveResponse.lean`. The original numerator theorem
  names `slabPhysicalFaceEdges`; the union diagonal names the selected chain.
  Treating the two as definitionally the same action would skip the missing
  comparison. The bounded constructive comparison plan, with explicit aligned
  extents and probe coordinates, is recorded separately in
  `audits/AUDIT-UNION-POSITIVE-RESPONSE-FRONTIER.md`.

The finite crossing-coercivity estimate is not a ready uniform substitute:
`BF4ExactSlabSelectedInterfaceCoercivity.selected_lower`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedInterfaceCoercivity.lean:70`,
has a floor whose exponent depends on its computed selected cutoff and
the extent's face count (`selectedFloor_exponent`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedInterfaceCoercivity.lean:64`). It proves
independence of later crossing cutoffs with the bulk cutoff/extent fixed, not
survival of a positive floor in the union's joint regulator limit.

## Independent source review of the new completion work

The six modules below were read in full. No hidden representative choice,
assumed completeness, or carrier replacement was found. This is a source
review, not a fresh compiler or axiom audit.

| Module/declarations | Review result |
| --- | --- |
| `CRealSeminormCompletedApproximation.DistanceData`, `lean/YMGap/Continuum/CRealSeminormCompletedApproximation.lean:30` | Fields are actual distance laws and a representative-distance limit; there is no completeness field. Dense approximants sample the supplied Cauchy stream and modulus. |
| `CRealSeminormCauchyRows.CauchyRows`, `lean/YMGap/Continuum/CRealSeminormCauchyRows.lean:50` | Rows are supplied as `Nat -> D.Cauchy`, not selected from an arbitrary `Nat -> D.Completion`. Diagonal and outer rates remain functions in `Type`. |
| `BF4SpatialUnionCompletedDistance.distanceData`, `lean/YMGap/Continuum/BF4SpatialUnionCompletedDistance.lean:151` | All fields are supplied on the actual union by `B(x-y,x-y)` and its proved termwise distance pin. |
| `BF4SpatialUnionRelaxation.relaxationCertificate`, `lean/YMGap/Continuum/BF4SpatialUnionRelaxation.lean:128` | Computed modulus uses the actual coupling-dependent `q` and a norm ceiling computed from the supplied representative. No nome-uniform bound or quotient representative choice. |
| `BF4ExactSlabThermodynamicGenericRowsPin.rowLimit_pin`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicGenericRowsPin.lean:75` | Regression equality preserves the old carrier, rows and rates. It does not identify the old completion with the union. |
| `BF4SpatialUnionCauchyRows.rowLimit_time`, `lean/YMGap/Continuum/BF4SpatialUnionCauchyRows.lean:69`; `rowLimit_center`, `lean/YMGap/Continuum/BF4SpatialUnionCauchyRows.lean:93`; `rowLimit_orthogonal`, `lean/YMGap/Continuum/BF4SpatialUnionCauchyRows.lean:102`; `relaxationRows_limit`, `lean/YMGap/Continuum/BF4SpatialUnionCauchyRows.lean:132` | Actual representative maps retain the outer modulus. Limit uniqueness plus the actual nonexpansive estimates proves commutation. Orthogonality uses the already proved centering fixed-point criterion. The orbit's computed diagonal limit is the existing projection of the same input, not a newly selected stationary state. |

The `ConvergesTo`/eventual-order propositional witnesses used internally are
eliminated inside proofs only. The executable approximation points, Cauchy
rows, diagonal sampling rates and relaxation thresholds are supplied or
constructed independently as data.

This review does not claim a continuum particle, interaction, full Hilbert/OS
structure, a calibrated physical mass, or the Clay target. No new kernel
verification was performed. Prior focused-check evidence for the existing
excitation modules is recorded in `audits/AUDIT-SPATIAL-UNION-SECTOR.md`.
