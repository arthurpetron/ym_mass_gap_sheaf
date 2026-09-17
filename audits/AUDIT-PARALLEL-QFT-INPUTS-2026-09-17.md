# Backward QFT requirements and forward Wilson-carrier inputs

Source review: 2026-09-17, starting from `843ac19`. This report distinguishes
known interface types from constructed physical inputs. No canonical frontier
statement is changed. The new equal-time commutation module below passed its
parent-controlled focused verification, with seven printed axiom gates inside
{propext, Quot.sound}; no compiler was run by its parallel author. The final
log hash is recorded in `AUDIT-BIDIRECTIONAL-FRONTIERS-2026-09-17.md`.

## Whole-project goal

For every compact simple gauge group, construct a nontrivial continuum
Yang--Mills theory on R^4 with the required same-theory QFT axioms, isolated
vacuum and finite positive physical Hamiltonian mass gap, within the
constructive Mathlib-free MLTT/HoTT gate. **The goal remains OPEN.**

## Answer: which inputs are already known?

Several forward inputs are constructed on the current Wilson spatial union.
They support independent mathematical work now. The full continuum QFT inputs
are not all constructed, and some older interface statements are weaker than
their advertised physical interpretation. Backward work therefore has two
distinct outputs: real consequences of existing inputs, and precise producer
obligations for the missing same-theory joins. Neither is a license to supply
an unrelated model for a missing physical object.

All paths in the following tables are relative to `lean/YMGap/Continuum/`.

| Constructed forward input | Source declaration | Exact scope |
| --- | --- | --- |
| Original finite-base Wilson-expression union | `BF4WilsonSpatialUnion.lean:37`, `Stage`; `BF4WilsonSpatialUnionSeminorm.lean:139`, `UnionCompletion` | One Cauchy quotient of original Wilson stages with possibly growing supports. Not a continuum scaling limit. |
| Actual constructive-real reflected pairing | `BF4WilsonSpatialUnionPairingData.lean:132`, `completedInner`; `BF4WilsonSpatialUnionPosdef.lean:93`, `completedInner_posdef` | RC-valued pairing on that same quotient, with positive definiteness. |
| Constructive real scalar action | `BF4WilsonSpatialUnionCompletedRealScalar.lean:74`, `completedRealSmul`; `:84`, `completedInner_realSmul_left` | Takes a supplied `CReal` and its `QCauchy` datum; no selection of a representative from a scalar quotient. |
| Represented-row completion | `CRealSeminormCauchyRows.lean:50`, `CauchyRows`; `:103`, `rowLimit`; `:109`, `rowLimit_bound`; `BF4WilsonSpatialUnionCauchyRows.lean:65`, `rowLimit_time` | Actual inner representative rows and outer moduli are inputs. Not a theorem selecting representatives of arbitrary quotient-valued sequences. |
| Physical discrete time and its original-form pin | `BF4WilsonSpatialUnionSeminorm.lean:143`, `completedTime`; `:151`, `completedTime_add`; `BF4WilsonSpatialUnionTimeForm.lean:137`, `completedTime_correlator` | Natural-number time. The same action, carrier and reflected form are retained. |
| Time symmetry, even positivity and contractivity | `BF4WilsonSpatialUnionTimeForm.lean:92`, `completedInner_time_balance`; `:119`, `completedInner_even_nonnegative`; `:107`, `completedInner_time_contraction` | Even-time positivity does not assert one-step positivity or a continuous-time generator. |
| Actual time-zero Wilson observables | `BF4WilsonSpatialUnionTimeZeroMultiplier.lean:140`, `completedMultiply`; `BF4WilsonSpatialUnionTimeZeroOperator.lean:89`, `completedInner_multiplier_balance`; `:119`, `completedMultiply_realSmul`; `:129`, `completedInner_multiplier_bound` | Bounded symmetric real-linear multipliers on the same completed space. |
| Actual finite Wilson-program realization and approximation | `BF4WilsonWindowRealization.lean:76`, `compileWindow_pin`; `:122`, `approximationCertificate` | Exact finite syntax and approximation from supplied Cauchy representatives. Not all gauge-invariant continuum fields or exact observable representatives of every completed state. |
| Fixed-spacing strict bound | `BF4WilsonSpatialUnionCompletedGap.lean:153`, `completed_twoStep_form_gap` | All completed vectors orthogonal to the same unit, under the original small-nome guards. |

## Backward dependency map

The right column gives the smallest unresolved join identified by this source
review; it does not introduce a new Lean structure or claim its proof.

| Required endpoint | Existing destination or obstruction | Missing same-theory producer / status |
| --- | --- | --- |
| Same limiting observable algebra and functional | `CanonicalOSRoot.lean:121`, `CanonicalSchwingerLimit`; `:145`, `thermodynamicModulus`; `:146`, `continuumModulus`; `:147`, `approximationConverges` | A changing-spacing family and its actual observable discretizations, expectation/norm approximation and two independent limit moduli. A current Wilson-union inhabitant is **NOT FOUND** in the search scope below. |
| Scalar-compatible OS root | `CanonicalOSRoot.lean:272`, `PositiveTimeOSRoot.positive`; `GNSQuotient.lean:102`, `GNSData.B`; `ObservableMeasure.lean:82`, `ProbFunctional.E` | Both destination forms are Q'-valued; the actual current completed pairing is RC-valued. No rationalization theorem is supplied. A reviewed same-theory scalar-interface correction and its proof bridge are needed before claiming this particular canonical root is filled. |
| Certified positive-time observable realization | `CanonicalOSRoot.lean:290`, `representativeSupported`; `:296`, `stateEssentiallySurjective`; `:298`, `reflectedForm`; `:302`, `transferRepresentative` | Pins to the SAME limiting algebra, half-space certificates, reflected form and ambient time. The surjectivity field concerns the dense `positive.V`, not all completed vectors. Finite Wilson-program realization does not supply the missing limiting-algebra/functional pins. |
| Full Hilbert structure appropriate to QFT | `CRealSeminormCauchyRows.lean:50`, `CauchyRows`; `BF4WilsonSpatialUnionCompletedRealScalar.lean:74`, `completedRealSmul` | The supplied-row completion is built. A full complex Hilbert/QFT reconstruction on current `UnionCompletion` is **NOT FOUND**; no inference from the word `Completion` to arbitrary quotient-level completeness is made. |
| Continuum regularity / test-field continuity | `OSAxioms.lean:238`, `IsOS0` | The existing predicate is only `wilsonCharExp(t,0) <= 1`, independent of its continuum-measure argument. A regularity theorem for actual limiting smeared fields, with its specified test-function domain and constructive bounds, is **NOT FOUND** in the current Wilson branch. |
| Full Euclidean covariance | `FourDExistence.lean:173`, `O4RestorationContent`; `OSAxioms.lean:250`, `IsOS1HypercubicTranslation`; `:259`, `IsOS1HypercubicH4` | These signatures allow a freely supplied self-map and functional; they are not an action of the entire Euclidean group on the current limiting theory. A full spatial/continuum group action, laws and continuity on current Wilson union are **NOT FOUND**. |
| Limiting reflection positivity | `BF4ExactSlabFixedSpatialWilsonIntrinsicForm.lean:152`, `intrinsicForm_nonnegative`; `CanonicalOSRoot.lean:298`, `reflectedForm` | Positivity is already supplied for the current fixed-spacing limiting Wilson form. The changing-spacing reflected-functional pin and controlled limit are still missing; no need to repropose the existing positivity theorem as a new hypothesis. |
| Observable algebra and locality | `BF4WilsonSpatialUnionTimeZeroOperator.lean:89`, `completedInner_multiplier_balance`; new `BF4WilsonSpatialUnionTimeZeroCommutation.lean:160`, `completedMultiply_comm` | Equal-time multiplier commutation can be proved from existing inputs independently of the improved mass estimate. Continuum spacelike locality of local fields is **NOT FOUND** and is not concluded by this equal-time law. |
| Full continuous-time semigroup and physical generator | `SelfAdjointHamiltonian.lean:437`, `BoundedFunctionalCalculusResidual` | This field bundle carries an everywhere-defined additive symmetric map and a scalar gap witness, but no equation linking that map to the exponential of the actual transfer. A dense generator domain, actual semigroup/generator relation and same-Wilson-carrier realization are **NOT FOUND**. |
| Yang--Mills local-field / short-distance identification | `LocalCurvatureFields.lean:165`, `LocalCurvatureFields`; `:242`, `OPE`; `FourDExistence.lean:158`, `UVAsymptoticFreedomContent` | `LocalCurvatureFields` freely supplies an algebra/functional; `OPE` has no field-product remainder identity; the UV predicate is a scalar one-loop growth statement. Actual scaled Wilson/curvature field limits and their common-theory short-distance laws are **NOT FOUND**. |

The type mismatch is not an instruction to modify a frontier field. This
report leaves all existing fields intact for reviewed statement repair.

## Two carrier distinctions that block accidental reuse

1. `BF4SpatialUnionDiagonalTranslation.completedInner_translate`,
   `lean/YMGap/Continuum/BF4SpatialUnionDiagonalTranslation.lean:268`, is a
   genuine positive diagonal-translation law, but its `UnionCompletion`
   comes from `BF4SpatialUnionSeminorm`, not `BF4WilsonSpatialUnionSeminorm`.
   The opened namespaces and `PhysicalSpan` in that file at lines 22--26
   identify the old plaquette carrier. It is not the current Wilson-union
   spatial action. A current-carrier bridge was **NOT FOUND** in the searched
   Wilson-union/translation modules.
2. `BF4ExactSlabThermodynamicPositiveRealSemigroup.realTimeAction_addTime`,
   `lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveRealSemigroup.lean:61`,
   uses `BF4ExactSlabThermodynamicSeminormCompletion.Completion`, opened at
   line 27, not the current Wilson union. Its positive-time semigroup is not
   a current-carrier continuous-time construction or a generator pin merely
   because both routes use constructive reals.

The older `OSReconstruction` interface is also not a substitute:
`HilbertSpace`, `VectorIn`, `SelfAdjointOp` and `ContractionSemigroup` at
`lean/YMGap/Continuum/OSReconstruction.lean:101`, `:113`, `:125`, `:140`
contain Unit witnesses and free law propositions; `OSReconstruction` at
`:206` does not use its measure argument to pin these objects. Its source
docstrings do not upgrade those declared field types.

## Independent implementation selected from known inputs

New file: `lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeZeroCommutation.lean`.

| Declaration | Line | Actual consumer |
| --- | --- | --- |
| `form_multiplier_comm` | 63 | Original reflected finite-window limit, with full action and partition retained. |
| `intrinsicForm_multiplier_comm` | 90 | The same multiplier identity at the common reflection center. |
| `pairing_multiplier_comm` | 112 | One common finite support base for both arbitrary loops and both stages. |
| `representativeInner_multiplier_comm` | 143 | Actual computed pairing limits of arbitrary supplied Cauchy streams. |
| `completedInner_multiplier_comm` | 151 | Original RC-valued completed pairing. |
| `completedMultiply_comm` | 160 | Equality of the two composed existing multiplier maps on every completed vector. |
| `completedInner_multiplier_product_balance` | 171 | Symmetry of their product, using the new commutation law and the existing symmetry of each factor. |

The proof uses scalar polynomial commutativity, not commutativity of SU(2)
holonomies. No representation-theoretic noncommutativity is erased: the
multiplied objects are already gauge-invariant scalar loop characters. The
proof never assigns multiplication to arbitrary completed vectors or asserts
that arbitrary OS-null representatives may be multiplied.

All original nome guards are retained. No new analytic input, canonical field,
carrier, `sorry` or axiom is introduced. The parent inspected the complete
source and checked this module with one worker and an explicit 20 GiB cap.
The parallel author did not run Lean, change CI, or scan literature; neither
the source review nor the focused check is a full-tree audit.

## Search scope and source-review boundary

Read: current `work_plan.md` opening and direction decisions;
`AUDIT-PARALLEL-FRONTIERS-2026-09-16.md`,
`AUDIT-ORIGINAL-SPATIAL-WILSON-REALIZATION.md`,
`AUDIT-ORIGINAL-OS-RECONSTRUCTION.md`, and
`AUDIT-UNION-SPATIAL-TRANSLATION-FRONTIER.md`; the destination structures
and current-carrier definitions cited above were checked against live source.

Searched `lean/YMGap/Continuum/BF4Wilson*.lean`,
`BF4SpatialUnion*.lean`, `CRealSeminorm*.lean`, `CanonicalOSRoot.lean`,
`GNSQuotient.lean`, `ObservableMeasure.lean`, `OSAxioms.lean`,
`OSReconstruction.lean`, `SelfAdjointHamiltonian.lean`,
`LocalCurvatureFields.lean`, `FourDExistence.lean`, and
`BF4ExactSlabThermodynamicPositiveRealSemigroup.lean` for the same-object
joins named above. **NOT FOUND** is scoped to that inspection; it does not
assert mathematical impossibility or authorize filling a missing join with
a weaker unrelated structure.
