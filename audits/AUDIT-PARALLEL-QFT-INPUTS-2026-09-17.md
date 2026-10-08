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

## 2026-10-08 UTC: bounded SAME-slab spatial-swap input

This independent finite geometry/word increment supplies no analytic
hypothesis and does not modify the historical or canonical QFT fields.
The primary signed scaling frontier is unchanged. The user's lattice-mass
note remains reconciled in `RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`;
no measured mass, Sobolev regularity or Kogut--Susskind identity is assumed.

All paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | Source | Checked mathematical content |
| --- | --- | --- |
| `swapVertex`, `swapDir`, `swapPlane`, `swapLink`, `swapPlaquette` | `BF4ExactSlabSpatialAxisSwapGeometry.lean:31`, `:34`, `:40`, `:48`, `:50` | Concrete x1/x2 exchange, with x0 and physical time x3 fixed. |
| `swapLink_involutive`, `swapPlaquette_involutive`, `swapVertex_addE` | `BF4ExactSlabSpatialAxisSwapGeometry.lean:66`, `:71`, `:77` | Actual involutions and compatible edge endpoints. |
| `swap_edgesOf_perm` | `BF4ExactSlabSpatialAxisSwapGeometry.lean:83` | Complete positive-link incidence; not oriented-word equality. |
| `swap_completeSlabPlaquettes_perm`, `swap_completeSlabLinks_perm` | `BF4ExactSlabSpatialAxisSwapGeometry.lean:130`, `:154` | Every original boundary-complete face and link retained, including fringe. |
| `swap_spatialFaces_perm`, `swap_temporalFaces_perm`, `swap_baseLinks_perm` | `BF4ExactSlabSpatialAxisSwapGeometry.lean:191`, `:196`, `:214` | Both original action families and the inclusive width-only slice carrier retained. |
| `swapLink_timeReflect_commute`, `swapPlaquette_timeReflect_commute` | `BF4ExactSlabSpatialAxisSwapGeometry.lean:224`, `:229` | Literal SAME-extent temporal reflection commutes. |
| `swapLink_timeShift_commute`, `swapPlaquette_timeShift_commute` | `BF4ExactSlabSpatialAxisSwapGeometry.lean:235`, `:240` | Temporal placement commutes at every time. |
| `reverse_word_conjugate`, `reverse_word_scalar` | `BF4ExactSlabSpatialAxisSwapWord.lean:43`, `:61` | d c bar(b) bar(a) is the conjugate of a b bar(c) bar(d), by anti-homomorphism and associativity only; their scalars agree. |
| `swappedFaceWord_scalar`, `swappedFaceWord_character` | `BF4ExactSlabSpatialAxisSwapWord.lean:77`, `:86` | Only p12 reverses canonical direction order; every spin character is coefficientwise invariant for arbitrary link assignments. |
| `correctedSlab_swappedWord_character` | `BF4ExactSlabSpatialAxisSwapWord.lean:93` | Target pinned to the literal corrected-slab plaquette with its initial-unit fold retained. Source still names the swapped physical links. |

Sol authored the 274-line geometry leaf; root authored the 110-line word
leaf. Root read both complete sources. An independent reviewer checked
orientation, full boundary/fringe retention, time convention and source pins.
The initially missing word namespace opens were repaired before its passing
check. No `sorry`, new axiom, classical/native decision, new analytic premise,
or option-limit increase was introduced.

Root alone ran serialized focused checks, with one worker, hard 20 GiB
worker ceiling and 12 GiB OS reserve. Each fresh preflight found no competing
compiler/runner, 88% system memory free and zero swap. Geometry's 27 and
word's five printed gates all stay within {propext, Quot.sound}; several
geometry identities are axiom-free. Exact passing logs:

- `/private/tmp/ym-spatial-axis-swap-20261008a.log`, SHA256
  `28528573d45a06c56f9f53c0eefaccfe476336d72928141d0a6de656c425e171`.
- `/private/tmp/ym-spatial-axis-swap-word-20261008b.log`, SHA256
  `1181b347422d70ab153ae0a32aba4fa9f951eac28405bc5f77397764748f8263`.

Imports are registered in `lean/YMGap.lean`; the root/full tree was NOT built
or audited. Actual next consumer: full link-coordinate reindex, transport
of each original `BF4ExactSlabAllExtentObservableHaarForm.faceHeatPolynomial`,
and the complete original face permutation using
`BF4ExactSlabAllExtentWeightedFactorization.polynomialProduct_perm`.
Then retain the SAME partition and Wilson source to prove finite
original-window scalar invariance and eventually SAME reflected-form isometry.
Those joins remain OPEN. These leaves do not establish a width-changing
isometry, continuous rotations, continuum Euclidean covariance, physical
mass calibration, a uniform scaling estimate or any Clay conclusion.
No displayed chart claim changed; no chart reprint.

### Subsequent 2026-10-08 UTC: actual coordinates and ORIGINAL action

The previous finite geometry/word checkpoint's open Haar/action join is now
proved, not assumed. Normalized Wilson-window source transport, SAME
reflected-form isometry and full continuum covariance are still OPEN.

| Declaration | Source, relative to `lean/YMGap/Continuum/` | Exact checked scope |
| --- | --- | --- |
| `swapBlock`, `swapBlock_physical`, `linkAt_swapBlock`, `swapBlock_involutive` | `BF4ExactSlabSpatialAxisSwapHaar.lean:47`, `:51`, `:57`, `:64` | Actual idxOf of the swapped complete-slab link; bounds/involution proved using the literal list, not an abstract supplied permutation. |
| `swapQuaternionBlockInvolution`, `swapPolynomial_haar` | `BF4ExactSlabSpatialAxisSwapHaar.lean:73`, `:102` | Produced full coordinate involution and original Haar invariance for explicitly supported polynomials. |
| `link_swap_prefix`, `link_swap` | `BF4ExactSlabSpatialAxisSwapHaar.lean:121`, `:144` | All four original coordinates, all link directions including x3, with no signs. Off-list identity fallback is also preserved. |
| `plaquette_scalar_swap`, `plaquette_character_swap` | `BF4ExactSlabSpatialAxisSwapHaar.lean:174`, `:193` | Actual reindexed plaquette scalar and EVERY spin character, using the conjugate p12 word and explicit common padding. |
| `swap_originalChainFaces_perm` | `BF4ExactSlabSpatialAxisSwapAction.lean:69` | Every original selected face, including the terminal spatial slice, on a contained chronological window. |
| `heatAtFace`, `heatAtFace_support`, `heatAtFace_swap` | `BF4ExactSlabSpatialAxisSwapAction.lean:79`, `:96`, `:108` | Recoding of actual faceHeatPolynomial to raw faces retains literal coeffAt(heatKernelPacket K w) and full range(K+1); support and swap pin are produced. |
| `originalChainAction_support`, `originalChainAction_swap` | `BF4ExactSlabSpatialAxisSwapAction.lean:144`, `:151` | SAME originalChainAction, arbitrary rational w/K, with width<=extent+1 and start+steps<=extent; every factor and endpoint unchanged. |
| `originalChainAction_weighted_haar_swap` | `BF4ExactSlabSpatialAxisSwapAction.lean:169` | H[action*swap(p)]~=H[action*p] for every supported insertion. SAME action/partition, no positivity premise; image/action support is produced before common padding is removed. |

Sol authored the initial Haar leaf; root repaired namespace opens and made
the quaternion-scalar/common-padding conversion explicit. This eliminated
the deterministic reduction timeout without increasing any proof option.
Root authored the action leaf, read both final complete sources and alone
performed their serialized narrow checks. Independent initial and final
complete-source reviews pass, including all coefficients, inverse flags,
time links, support premises and terminal-slice retention. No `sorry`, axiom,
classical/native decision, new analytic premise or canonical field change.

Passing focused logs: Haar has 13 and action seven printed gates, all exactly
{propext, Quot.sound}. One worker, hard 20 GiB ceiling, 12 GiB reserve; each
fresh preflight found no competing compiler/runner, 88% system-wide free
memory and zero swap. No full-tree/root build or audit:

- `/private/tmp/ym-spatial-axis-swap-haar-20261008d.log`, SHA256
  `19be6ae7875687f257882c433b00e1fe302d54ebfe0ddbe845962f6763949b4d`.
- `/private/tmp/ym-spatial-axis-swap-action-20261008c.log`, SHA256
  `cae7124daabb7529b870f6ce19af84ca8cfab3813565e05f2e99ea11de93f57c`.

NEXT actual ordered SourceLoop transport and the original WindowExpression
source/placement pin. Keep every reverse flag and word order (unlike the
canonical face comparison, an arbitrary mapped loop is not reordered), then
retain the SAME finite normalization before passing to the actual reflected
form. No completion wrapper or freely supplied isometry is a substitute.
Signed scaling and every displayed physical/Clay claim remain OPEN; no chart
claim changed or was reprinted.

### Subsequent 2026-10-08 UTC: original Wilson windows and reflected forms

The actual source/normalization and dense reflected-form joins above are
now proved. All source paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | Source | Exact checked scope |
| --- | --- | --- |
| `swapEntry`, `pathFinish_swap`, `compatible_swap`, `swapSourceLoop` | `BF4ExactSlabSpatialAxisSwapWilsonLoop.lean:40`, `:61`, `:69`, `:78` | Actual endpoint-compatible closed source loop on SAME baseLinks; preserves edge order and every inverse flag. |
| `swapEntry_shift_commute`, `word_swap`, `character_swap` | `BF4ExactSlabSpatialAxisSwapWilsonLoop.lean:93`, `:117`, `:140` | Literal time placement commutes; arbitrary ordered original words and EVERY spin transport with common padding. No face-only substitution or reordered path. |
| `swapExpression`, `within_swap`, `swap_mirror`, `placedPolynomial_swap` | `BF4ExactSlabSpatialAxisSwapWilsonWindow.lean:46`, `:53`, `:78`, `:88` | Every offset/spin/signed operation retained; same window guard, temporal mirror and actual placed insertion. |
| `original_window_numerator_swap`, `originalWindowScalar_swap` | `BF4ExactSlabSpatialAxisSwapWilsonWindow.lean:119`, `:145` | SAME full chronological action-weighted numerator and literal finite normalization; original reciprocal unchanged. Both supports are produced before padded Haar removal. |
| `originalJointLimit_swap` | `BF4WilsonAllNomeSpatialAxisSwapForm.lean:36` | SAME existing joint heat/time diagonal and constructive limit, with explicit Within and produced transported Within. |
| `swapIntrinsic`, `swap_chart`, `swap_advance` | `BF4WilsonAllNomeSpatialAxisSwapForm.lean:49`, `:62`, `:66` | Retains witnessed radius; exact temporal-chart and advance commutation, no width map. |
| `commonForm_swap`, `intrinsicForm_swap`, `swap_crossOdd`, `bondForm_swap` | `BF4WilsonAllNomeSpatialAxisSwapForm.lean:70`, `:81`, `:95`, `:109` | Existing all-nome site and actual odd bond forms preserved at SAME width/nome. Odd source retains R+1 charts, one-sided advance and L=2R+1. |

The finite originalWindowScalar identity does not require Within: the
original off-list identity fallback is itself preserved. Physical-window
and limit interpretations DO require the existing guard; the checked joint
consumer retains it. Quotient.sound is used only to transport the existing
CReal equivalence into the existing bondForm real quotient.

Sol authored the loop leaf; root authored its signed-window/normalization
consumer; the parallel reviewer authored the joint/reflected-form consumer.
Root read all complete final sources. Independent complete-source reviews
checked order/inverse flags, support removal, original action/reciprocal,
explicit limit guards and odd-source geometry. No sorry, new axiom,
classical/native decision, analytic premise, proof-limit increase or
canonical field weakening. No canonical frontier atom is closed.

Root alone checked the three leaves serially, each launch after fresh process/
memory/swap preflight: no competing compiler/runner, 87--88% system-wide
memory free and zero swap. One worker, hard 20 GiB ceiling, 12 GiB reserve.
All 28 printed gates stay within {propext, Quot.sound}; two loop identities
are axiom-free. Exact passing logs:

- `/private/tmp/ym-spatial-swap-wilson-loop-20261008a.log`, SHA256
  `e2487a5858219b188e5cb7e4f84bd2d317a47e13f5b3afc0cf39d98bae886a53`.
- `/private/tmp/ym-spatial-swap-wilson-window-20261008c.log`, SHA256
  `c87e6a56931be1ef160fe6edbdfa6e47ca1efe0ac32415693286ec146528cce7`.
- `/private/tmp/ym-spatial-swap-reflected-form-20261008b.log`, SHA256
  `3ca48cb77e1ef0dc74e5b49852834be8fda03fe2b5c16ba93eca2f3876ebeac4`.

Imports are registered, but root/full tree was NOT built or audited.
NEXT actual source involution and signed-difference laws, then distance
preservation/nonexpansiveness consumed by
`CRealSeminormCompletion.lean:323`, `Nonexpansive.completionMap`, on the
already chosen carrier. Completed spatial operator, physical bond/time-sector
join, continuous rotations, continuum covariance and changing-family
survival remain OPEN. The primary coupled signed interaction estimate is
still OPEN; the independent harmonic-response screen is recorded in the
adaptive audit and supplies no replacement estimate. No displayed physical/
Clay chart claim changed; no chart reprint.
