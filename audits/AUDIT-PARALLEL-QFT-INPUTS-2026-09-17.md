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

## Selected literal Wilson vertex-gauge input (2026-10-08 UTC)

The supplied lattice-measurement attachment is already reconciled in
`RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`; it adds no new estimate.
Independent source review instead identified one missing physical-source
property with an existing finite consumer: the literal closed Wilson word
and its guarded signed window must satisfy the existing
`BF4ExactSlabVertexGaugeAction.Invariant` for every common auxiliary tag map.
Plaquette invariance and the narrower temporal ledger do not alone assert
this property for arbitrary closed words.

Selected argument: `BF4ExactSlabAuxiliaryVertexGauge.slabGauge_link`
(`lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:93`) pins each
actual physical link's ledger image; ordered endpoint compatibility and
`SU2QuaternionHaarGaugeWord.closed_character`
(`lean/YMGap/Continuum/SU2QuaternionHaarGaugeWord.lean:104`) cancel the
unit auxiliary gauges in the sphere/Haar ideal. Retain inverse orientations,
repeated occurrences, the three auxiliary blocks, supported spectators and
both placement guards. Then instantiate the existing same-carrier
`BF4ExactSlabGaugeRepresentedCompletion.ofPolynomial`
(`lean/YMGap/Continuum/BF4ExactSlabGaugeRepresentedCompletion.lean:52`)
on the literal placed window, with the unchanged
`fullData` hypothesis `headCutoff w <= K`. This is an explicit represented
dense point, not a new completion or a supplied gauge-invariance premise.

Scope: tags take values in three SHARED auxiliary quaternions or identity;
no independently realized gauge at every vertex, infinitesimal Gauss
generator, rowwise SO4 Ward cancellation, OS/scaling identification or
continuum QFT closure is selected. Stop if the join requires any new
analytic premise, inverse, representative selection or changed action.
One Sol-authored source leaf, an independent complete-source review and
root-owned serialized capped verification are selected. At selection the
227-line draft had passed mathematical review but was not yet compiled;
the final checked source and its concrete consumer are recorded below.
Main DIRECT macroscopic retention / JOINT signed relative cost stays OPEN.

### Observed literal source and SAME-completion consumer

Both complete FINAL sources pass independent semantic review and root-owned
focused Lean verification. Paths below are relative to `lean/YMGap/Continuum/`.

| Produced result | Exact declaration and checked scope |
| --- | --- |
| Physical closed word satisfies the existing auxiliary vertex invariant | `BF4ExactSlabVertexGaugeWilsonWord.lean:174`, `closedWord_invariant`; actual ledger substitution, compatible ordered path, physical membership and closed terminal are used. |
| Literal placed SourceLoop and signed window inherit that property | Same module `:210`, `placedSourceLoop_invariant`; `:219`, `placedWindow_invariant`; both room guards, every spin, offset, inverse and repeated occurrence remain. |
| Original supported dense polynomial and produced gauge predicate | `BF4ExactSlabGaugeWilsonCompletion.lean:39`, `windowPolynomial`; `:42`, `windowPolynomial_val`; `:46`, `window_gaugePolynomial`; no invariance premise. |
| Explicit represented point and actual block-projection image | Same module `:54`, `windowRepresentative`; `:62`, `blockWindowRepresentative`; Type-valued representatives/moduli in the EXISTING `fullData` completion, strict nome and unchanged `headCutoff w <= K`. |

Sol authored the source cancellation leaf; root repaired namespace/typed
coefficient-relation/Within elaboration and authored the concrete completion
consumer. Root read both full final sources. Independent full-source review
passes ordered/reversed endpoints, physical placement, support/padding,
arbitrary supported spectators, literal insertion and represented projection.
No new sorry/axiom, classical/native shortcut, new analytic premise,
noncomputable extraction, field weakening or resource-limit increase.

All eight printed gates are exactly {propext, Quot.sound}; accepted logs
contain no error or warning. Checks were serialized through the safe launcher,
one 20-GiB worker, 12-GiB OS reserve. Each launch's fresh preflight found no
competing compiler/runner, 86--87% system-wide free memory and zero swap.
The first two source checks had elaboration errors, not mathematical evidence;
only the final checked source is accepted.

| Leaf | Final source SHA256 | Accepted focused log and SHA256 |
| --- | --- | --- |
| Vertex word | `34e800bee3134d69453658ec423818ac0dcaa5b57dc946a5e9b9f622fa955d34` | `/private/tmp/ym-vertex-gauge-wilson-word-20261008-c.log`; `085e0ce259c5a9b192d5ea39a0b2093ed112142482e08c80c59b54bfc3bc2177` |
| Completion consumer | `01a8c06b710c111e400638bd65bb9539d175773eebac819ed5241e04f7d666bf` | `/private/tmp/ym-gauge-wilson-completion-20261008-a.log`; `eb6c18e5d9fc72465532592d5b84730b2239bd5923d3919c5f426f974f8c3784` |

Root imports registered only: no root/full-tree build, audit, guard or metric.
Stop this independent increment at the actual finite weighted completion
consumer. All-nome OS/scaling identification, infinitesimal Gauss law,
joint signed cost/variance control, continuum survival/physical calibration,
full QFT and every-group/Clay remain OPEN. Three shared auxiliary tags are
not arbitrary independently realized vertex gauges. The rowwise kinetic
SO4 Ward generator is different; this source property does not erase its
interaction response. No displayed canonical chart claim changed.

## Original bond derivative and ordinary transfer logarithm (2026-10-08 UTC)

Selected independent QFT input: identify the EXISTING bond derivative output
with the ordinary positive-logarithm series (-log P) of that SAME bond space's
original numerical time-one action. Inputs already produced: `BondOSLinear` operations,
`BondOSRealTime.action_value`, `PositiveRealSemigroup.realTimeAction_original`,
`BondOSDerivative` input/output pins, and `DomainLogarithm` graph tail bound
and represented output-range modulus. Consumer: the existing physical bond
derivative graph now has its own literal transfer-logarithm identification,
not just the ambient sector identification. No additional analytic premise.

One bounded Sol-authored leaf, independent complete-source review, and
root-only serialized focused verification were selected. Stop if the join
requires quotient representative selection, an inverse, a substituted carrier,
or deletion of the ambient boundary kernel. Fixed nome and width only; no
physical time calibration or full QFT/continuum closure is selected.

### Observed kernel-checked SAME-bond identification

Complete final 157-line source review and focused Lean check PASS.

| Produced result | Exact declaration |
| --- | --- |
| Existing numerical time-one action equals original completed time one | `lean/YMGap/Continuum/BF4WilsonAllNomeBondOSLogarithm.lean:49`, `transfer`; `:53`, `bondValue_transfer` |
| SAME-bond D=I-P and literal D^n, including D^0=I | Same module `:60`, `defect`; `:63`, `bondValue_defect`; `:70`, `defectPower`; `:74`, `bondValue_defectPower` |
| Exactly m ordinary-log terms D^(j+1)/(j+1), in original addition order | Same module `:85`, `logPartial`; `:91`, `bondValue_logPartial` |
| Tail bound for EVERY existing quotient-domain class | Same module `:112`, `domain_logarithm_tail_bound` |
| Exact represented derivative output and its original explicit modulus | Same module `:124`, `represented_logarithm_bound`; `:136`, `representedLogarithmCertificate` |

The tail bound is `bondDist(L_m(input d),output d) <=
bondInner(D^m(output d),D^m(output d))`. Quotient elimination is into Prop.
The Type-level convergence certificate consumes a SUPPLIED original
`SectorDerivative.DomainPoint`; its modulus is exactly `domainLogModulus p`,
computed from that point's output-range witness. No rate/witness extraction
from arbitrary quotient Domain is asserted. This does not alter the old
Wilson-UNION QFT audit's scope or discharge its continuum obligations.

All 11 printed gates are exactly {propext, Quot.sound}; no warning, sorryAx,
new hole/axiom, classical/native shortcut or option increase. Fresh preflight:
88% memory free, zero swap, no competing compiler/runner. One 20-GiB worker,
12-GiB OS reserve, safe-build focused check with explicit olean output.
Root import registered only; no root/tree build, audit, guard or metric.

```text
Accepted log: /private/tmp/ym-bond-os-logarithm-20261008-a.log
SHA256 83933412920c9764993bf6d9d9aee23d3174e504a049afb01bf7c6dcf22570b0
Checked source SHA256
f6a051873dcfaf099b362b533ef03ceaa8a58601e4bd00b7dbc56d1d8eebd8f1
```

Decision: retain this actual fixed-parameter SAME-object join. Main DIRECT
macro-retention or sufficient JOINT signed-window estimate on a justified
changing family remains OPEN, as do survival, physical Hamiltonian mass,
full SAME limiting QFT and every compact simple group. No exact canonical
displayed claim changed; no ASCII chart reprint.

## Selected spatial sign-reflection boundary test (2026-10-08 UTC)

Previous goal turn: PROGRESS, pushed `b24bc74b`. The primary JOINT signed
filtered-cost input remains unpaid. Parallel source review tests the next
finite symmetry generator before attempting its Haar/action/completion lift.

Proposition: geometric x0 reflection about width/2 does NOT close the literal
`spatialFaces width` or `temporalFaces width` lists at any positive width.
The origin transverse p12 face maps to base x0=width, excluded by the strict
base cutoff, although every reflected spatial edge remains in `baseLinks`.
The analogous temporal p13/p23 faces are also excluded. Available inputs:
`BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff` and
`temporalFaces_mem_iff`, `SliceCarrier.baseLinks_mem_iff`, and
`TwoLayerBoundary.SliceLink`. Consumer: the prospective face-permutation step
for a SAME-action finite signed-cubic generator; no existing declaration
supplies that new generator. Predicted decision: PRUNE its naive exact lift;
keep continuum covariance and boundary comparison OPEN, without changing the
action, carrier or any canonical field. A face-list obstruction alone is not
a theorem about inequality of limiting reflected functionals.

Decisive tests: every width>=1, transverse versus incident reflection planes,
and inclusive retained coordinates versus absent action factors. Budget: one
bounded Sol geometry leaf, independent complete-source review, root-only
serialized focused 20-GiB check/12-GiB reserve after fresh capacity preflight.
Stop rather than assume an invariant cell selection or change the law.
Selection is not yet a new kernel-checked result.

### Observed boundary certificate and route decision

Final focused check PASS; root inspected the complete final source and
independent complete-source mathematical review PASS. Every positive width
is covered. This certifies ONLY geometry/list nonclosure, not inequality of
action values or reflected functionals, impossibility of completed parity,
or failure of continuum Euclidean covariance.

| Checked claim | Exact source |
| --- | --- |
| Explicit geometric positive-face reflection, physical x3 time fixed | `lean/YMGap/Continuum/BF4ExactSlabSpatialSignReflectionObstruction.lean:31`, `reflectPositiveFace` |
| Original origin p12/p13 membership, reflected face absence | Same module `:50`, `origin12_spatial`; `:56`, `reflected_origin12_not_spatial`; `:75`, `origin13_temporal`; `:81`, `reflected_origin13_not_temporal` |
| All four reflected p12 edges are SAME retained coordinates | Same module `:64`, `reflected_origin12_edges_in_baseLinks` |
| Transverse p12 reflection remains included EXACTLY for a>0; incident origins survive | Same module `:89`, `transverse12_reflected_mem_iff`; `:102`, `incident_origin01_reflected_spatial`; `:108`, `incident_origin02_reflected_spatial` |
| Neither actual face list is permuted at any width>=1 | Same module `:123`, `spatialFaces_no_perm`; `:130`, `temporalFaces_no_perm` |

The two final finite-direction tests explicitly reduce to x1!=x3/x2!=x3
before kernel `decide`. The earlier failed elaboration log and its generated
sorryAx are NOT proof evidence. Final 17 printed gates: three axiom-free,
two {propext}, twelve {propext, Quot.sound}. No warning, sorryAx, new hole,
axiom, classical/native shortcut, option increase or canonical field change.
Each launch had a fresh no-competing-process preflight, 88% pressure-free
memory, zero swap, one 20-GiB worker and 12-GiB OS reserve. Root import
registered only; no root/full-tree build, audit, guard or metric run.

Accepted log SHA-256:

```text
/private/tmp/ym-spatial-sign-boundary-20261008b.log
  2ac3893af862444dd6506a9b95f22704c3ba9dabe902694c1d286e684d514552
```

Checked source SHA-256:

```text
34321c2c5b37639180c3dcd07c803fe6afa9053c8ff98caa7667ffc089a466fb
```

SOURCE-LEVEL product screen, NOT a new checked action/Haar pin: for a
contained chain of m steps, write the common face product C and the two
transverse sheets B0,Bw. The original/reflected products have the shape
C*B0 and C*Bw. p12 sheets occur on ALL m+1 spatial slices, including the
terminal slice; p13/p23 sheets occur on ALL m temporal layers. Keep these
factors rather than discard retained Haar coordinates. Inputs:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFacePlacement.lean:97`,
`spatialFaces_mem_iff`, and `:105`, `temporalFaces_mem_iff`;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:70`, `spatialWeight`.
No global reflected-link bijection, oriented-word transport or normalized
boundary estimate is supplied by this product screen.

Decision: PRUNE the naive exact face-permutation lift, without changing
the original action or canonical obligations. Future SAME-theory parity
needs a normalized lateral-boundary comparison (or another valid argument),
not just the existing temporal Perron/terminal-depth control. This is an
additional boundary requirement to coordinate with the main interacting
scaling lane, not a proved reduction of that requirement to its signed cost.
Full QFT covariance and the whole Clay target remain OPEN. No canonical
displayed claim changed; no chart reprint.

## Selected completed spatial coherence increment (2026-10-08 UTC)

Proposition: extend the produced x0/x1 source isometry to the EXISTING
original Wilson completion, then lift the actual ordered-source braid to
U01*U12*U01 = U12*U01*U12 on that SAME completion. The two involutions then
give (U01*U12)^3=I. Consumer: coherent finite spatial permutation covariance,
an independent input to the QFT lane; not the signed scaling estimate.

Available inputs: `BF4WilsonAllNomeSpatialHeadSwapForm.intrinsicForm_swap`,
the existing `Nonexpansive.completionMap`, the first completed generator in
`BF4WilsonAllNomeSpatialAxisSwapCompletion`, and
`BF4ExactSlabSpatialHeadSwapGeometry.swapVertex_braid` / `swapLink_braid`.
The source loop start, ordered edges, reverse flags, spin, offsets and signed
expression syntax must satisfy the braid before quotient descent. No
canonical plaquette reordering or quaternion-factor commutation is permitted.

Predicted output: actual involutive pairing/distance-preserving operator,
with unchanged supplied Cauchy modulus, unit and completed-time commutation;
then actual completed braid/cycle identities. Degenerate/null states and
arbitrary temporal-radius tags remain covered. Stop if a new carrier, form,
analytic estimate or assumed symmetry is required. No signed reflection,
continuous rotation, continuum covariance or scaling closure is asserted.
Verification budget: Sol implements the single completed-generator leaf;
root supplies/reviews the coherence proof, with independent source review
and serialized focused 20-GiB checks, 12-GiB reserve, fresh capacity preflight.
Observed results will be recorded separately after checking.

### Observed completed-generator and braid evidence

Both leaves pass root-controlled focused kernel checks and independent
complete-source semantic review. The second generator preserves the SAME
original intrinsic pairing, completed distance, unit, vacuum complement and
completed x3 time. Both actual adjacent swaps retain their supplied Cauchy
moduli. Ordered source loops satisfy the braid before quotient descent;
no generic assumed group action is used. The cycle has order DIVIDING three;
faithfulness and inequality of the quotient operators are not claimed.

| Produced result | Exact declaration |
| --- | --- |
| Actual second completed operator, original embed, unchanged Cauchy modulus | `lean/YMGap/Continuum/BF4WilsonAllNomeSpatialHeadSwapCompletion.lean:155`, `completedSwap`; `:159`, `completedSwap_embed`; `:163`, `swap_cauchy_modulus` |
| Involution, actual time and original unit | Same module `:166`, `completedSwap_involutive`; `:176`, `completedSwap_time`; `:213`, `completedSwap_unit` |
| SAME pairing/distance and vacuum complement | Same module `:231`, `completedInner_swap`; `:241`, `completedDist_swap`; `:246`, `completedSwap_preserves_vacuumComplement` |
| Literal ordered edges/loops, signed expression and intrinsic braid | `lean/YMGap/Continuum/BF4WilsonAllNomeSpatialSwapBraid.lean:43`, `swapEntry_braid`; `:66`, `swapSourceLoop_braid`; `:75`, `swapExpression_braid`; `:103`, `swapIntrinsic_braid` |
| Actual completed U01 U12 U01 = U12 U01 U12; (U01 U12)^3=I | Same module `:116`, `completedSwap_braid`; `:128`, `completedCycle_cube` |

Verification: two serialized one-worker focused checks at 20 GiB, with
12-GiB OS reserve and fresh dynamic-capacity/process preflight before each.
Both preflights report 88% system-wide memory free and zero swap use; no
competing compiler or runner. All 25+6=31 printed gates are empty or within
{propext, Quot.sound}; the edge braid is axiom-free. No sorryAx, new
hole/axiom, classical/native shortcut, limit increase or canonical field
change. Root imports registered only; no root/full-tree audit or guard.

Successful logs and SHA-256:

```text
/private/tmp/ym-headswap-completion-20261008.log
  844b98c4dabcf029b1f759158b56f301e51f958e869eb28c9bca26375ce25b47
/private/tmp/ym-spatial-swap-braid-20261008.log
  b0c9861073a10bc91ab594cfff0d151c41df407684c055c201bd14d023aacf9f
```

Checked source SHA-256, same completed-generator/braid order:

```text
1f94570673f491b497e8a7989865c359b377e78013c02ed5f8d8a95fbdbff801
3b7bb5dbf244b1c1fb133264ee01bc5516a6e32a9a48dbbd670419946e364895
```

Decision: the available finite QFT input is produced. Full signed-cubic,
continuous/continuum covariance, the second generator's witnessed time-sector
and bond-image joins, useful joint signed scaling estimates and all physical
Clay obligations remain OPEN. No canonical chart claim closes or chart is
reprinted. Return the main lane to an actual interacting producer; the separate
curvature/variational screens in the adaptive audit add no analytic estimate.

## Second spatial generator: selected Wilson/reflected-form join (2026-10-08 UTC)

Proposition: transport arbitrary ordered SourceLoop/WindowExpression data by
the produced literal x0/x1 swap, then prove invariance of the SAME original
normalized window, existing joint limit and common/intrinsic/odd bond forms.
Consumer: the fixed-width reflected/completed spatial-symmetry route; not the
primary signed scaling estimate or continuum Euclidean covariance.

Inputs already produced: `BF4ExactSlabSpatialHeadSwapGeometry`,
`BF4ExactSlabSpatialHeadSwapHaar.link_swap` and
`BF4ExactSlabSpatialHeadSwapAction.originalChainAction_weighted_haar_swap`,
plus the existing original Wilson-window and diagonal-limit APIs. Predicted
output is an unconditional actual-source/form pin, not a supplied isometry.
Decisive tests: x3 remains physical time; p01 canonical order reverses but
ordered source words keep their traversal order and reverse flags; the SAME
chronological partition/terminal slice, radius and odd one-sided time advance
must remain. Abandon if an analytic premise or surrogate pairing is required.
Budget: bounded Sol implementation, independent complete-source review,
root-only serialized focused checks at 20 GiB with 12-GiB OS reserve and fresh
dynamic-capacity preflight. No completion/operator, full cubic/continuous
covariance or scaling closure is asserted by this selected increment.
Observed verification is recorded separately below.

### Observed second-generator source/form proof evidence

All three new leaves pass focused kernel checks; root and independent
complete-source reviews pass. Arbitrary source paths retain their order and
reverse flags, not a canonically reordered p01 loop. Original action factors
use the existing conjugate-character pin for canonical p01 reversal. The
original normalized window and diagonal limit keep the SAME action and
reciprocal. Intrinsic CReal and odd bond RC pairings remain distinct.

| Produced result | Exact source |
| --- | --- |
| Ordered edge/start/finish/path transport and actual physical closed SourceLoop | `lean/YMGap/Continuum/BF4ExactSlabSpatialHeadSwapWilsonLoop.lean:40`, `swapEntry`; `:51`, `swapEntry_start`; `:56`, `swapEntry_finish`; `:78`, `swapSourceLoop` |
| Literal original ordered word and every spin, including inverse flags and empty loop | `lean/YMGap/Continuum/BF4ExactSlabSpatialHeadSwapWilsonLoop.lean:117`, `word_swap`; `:140`, `character_swap` |
| SAME placed Wilson expression, temporal offsets and mirror | `lean/YMGap/Continuum/BF4ExactSlabSpatialHeadSwapWilsonWindow.lean:46`, `swapExpression`; `:62`, `swap_mapOffsets`; `:88`, `placedPolynomial_swap` |
| Complete original chronological action numerator and unchanged normalized window | `lean/YMGap/Continuum/BF4ExactSlabSpatialHeadSwapWilsonWindow.lean:119`, `original_window_numerator_swap`; `:145`, `originalWindowScalar_swap` |
| Existing original joint limit with actual Within witness | `lean/YMGap/Continuum/BF4WilsonAllNomeSpatialHeadSwapForm.lean:36`, `originalJointLimit_swap` |
| SAME common/intrinsic reflected form, preserving radius/chart/time | `lean/YMGap/Continuum/BF4WilsonAllNomeSpatialHeadSwapForm.lean:70`, `commonForm_swap`; `:81`, `intrinsicForm_swap`; `:66`, `swap_advance` |
| SAME odd source and bond pairing, retaining advance 1 y and 2R+1 window | `lean/YMGap/Continuum/BF4WilsonAllNomeSpatialHeadSwapForm.lean:95`, `swap_crossOdd`; `:109`, `bondForm_swap` |

Verification: three serialized focused 20-GiB one-worker checks with 12-GiB
OS reserve and fresh capacity preflight before each. All 13+7+10=30 printed
gates are empty or within {propext, Quot.sound}; no sorryAx. The loop check
reports two unused simp-argument warnings only. Swap use was zero in all
preflights. Root imports registered only; no root/full-tree audit. No new
hole/axiom, classical/native shortcut, option increase, canonical field or
displayed-claim/chart change.

Successful logs and SHA-256:

```text
/private/tmp/ym-headswap-wilson-loop-20261008.log
  3bf82fa8e196ac8d163e614ae60e0c981f09d20058a18dcc0ecd55a0ddd7d8fd
/private/tmp/ym-headswap-wilson-window-20261008.log
  464469088ed8c394f8bdf656b8a78bfd9ddea97eaef04625c7234ac78e459319
/private/tmp/ym-headswap-reflected-form-20261008.log
  f0f719733fcc34361f51e7fe2845456b5fec92141687189e5a7fede8b198ef4d
```

Checked source SHA-256, in the same loop/window/form order:

```text
521d4f68971335bb7f2cbf11ed48af7f393a6dc03048de5a711becbecadf3bad
539ffed4e3e96ed1e17377b3d1853e8c68ca2a9030e9bd63bca676dbe49ae2ab
4e48b377ee438e5241625a8213baf72afda9cc7d157609faefb480abab1e5f58
```

Decision at this source/form checkpoint: the independent finite QFT input
was produced, while the second completed operator and completed permutation
coherence were still OPEN. Their subsequent checked proofs are recorded above.
Full signed-cubic and continuous/continuum covariance, signed scaling control
and every physical/Clay obligation remain OPEN. No state-family survival follows.

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

Selected next finite input, 2026-10-08 UTC: construct the SECOND spatial
transposition x0/x1, alongside the existing x1/x2 map, and prove literal
complete-slab Haar/ORIGINAL-action invariance. Physical time x3 and all
chronological endpoint factors stay fixed; p01 reverses its canonical word.
Inputs are the existing finite face/link membership, quaternion reversal,
coordinate reindex and action-product APIs. Consumer: the missing generator
of a full finite spatial permutation action, before any continuum-covariance
claim. Geometry must also prove the braid relation with the existing swap.
Budget: bounded Sol geometry/word implementation; root actual Haar/action
joins; independent complete-source review; root sole focused checks, one
20-GiB worker/12-GiB reserve with fresh capacity preflight. Stop if a current
second-generator realization already exists or a supplied symmetry/norm
hypothesis is needed. No new conditional symmetry interface, full-tree build,
analytic premise or closure of the continuum QFT/covariance box is selected.
The analytic signed-cost lane remains active; this is independent work from
the backward QFT requirement with available forward inputs. Results below
must distinguish this selection from subsequent checked evidence.

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

### Subsequent 2026-10-08 UTC: SAME completed operator and witnessed time sector

The previous source-form checkpoint's operator/range/dense-image joins are
now constructed. All source paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | Source | Exact checked scope |
| --- | --- | --- |
| `swapSourceLoop_involutive`, `swapExpression_involutive`, `swapIntrinsic_involutive` | `BF4WilsonAllNomeSpatialAxisSwapAlgebra.lean:42`, `:50`, `:78` | Actual entry/vertex involutions and list-map identity; no supplied inverse or form hypothesis. |
| `swapIntrinsic_sum`, `swapIntrinsic_difference`, `swapIntrinsic_smul`, `distSq_swap`, `swapNonexpansive` | `BF4WilsonAllNomeSpatialAxisSwapAlgebra.lean:88`, `:99`, `:111`, `:118`, `:127` | Literal common-radius signed operations; SAME original all-nome reflected distance supplies the existing nonexpansive input. |
| `completedSwap`, `swap_cauchy_modulus`, `completedSwap_involutive`, `completedSwap_time` | `BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:50`, `:58`, `:61`, `:70` | Existing completionMap/null quotient, original Cauchy modulus unchanged, involutive map commuting with actual integer time. |
| `completedSwap_add`, `completedSwap_smul`, `completedSwap_sub`, `completedSwap_unit` | `BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:80`, `:91`, `:102`, `:107` | Actual signed linear operations and original unit preserved; no new pairing or ground-state claim. |
| `representativeInner_swap`, `completedInner_swap`, `completedDist_swap`, `completedSwap_preserves_vacuumComplement` | `BF4WilsonAllNomeSpatialAxisSwapCompletion.lean:117`, `:125`, `:136`, `:142` | Existing pairSequence limits/quotient pairing and subtraction distance preserved; orthogonality means ONLY orthogonality to the existing unit. |
| `completedSwap_actionFrom`, `completedSwap_finiteRoot`, `completedSwap_root` | `BF4WilsonAllNomeSpatialAxisSwapTimeSector.lean:79`, `:96`, `:104` | Every finite signed polynomial in I-T and every supplied fixed-depth original root commute. Old-source limitRate supplies a valid transported convergence rate; mapped root-row modulus equality is NOT assumed. |
| `swapRange`, `swapRange_modulus`, `swapState` | `BF4WilsonAllNomeSpatialAxisSwapTimeSector.lean:123`, `:132`, `:136` | Actual supplied original preimages mapped by mapCauchy; supplied outer modulus retained verbatim; State keeps its produced Type-valued range witness. |
| `swapState_distance`, `swapState_inner`, `swapState_involutive_val`, `image_swap_pin` | `BF4WilsonAllNomeSpatialAxisSwapTimeSector.lean:143`, `:147`, `:153`, `:170` | Actual range-state pairing/distance and underlying-vector involution. Dense physical bond image remains the literal root(1) of the original swapped source embedding. |

The operator preserves one fixed-width/nome spatial permutation, not a
width-changing map or continuum Euclidean covariance. Root commutation is
for every supplied finite depth but claims no uniform-depth modulus. State
involution compares underlying vectors (the existing stateSetoid relation),
not equality of arbitrary Type-valued range-certificate data. No quotient
representative or preimage is selected by choice. No new analytic premise,
assumed isometry, replacement action/carrier/norm or canonical field closure.

Sol authored the source algebra; root authored the completed operator;
the independent reviewer authored the root/range/dense-image consumer. Root
read all final complete sources, and independent complete-source mathematical
reviews passed. The algebra's initial map-id simplifier mismatch and the
operator's local-notation/named-argument collision were fixed without any
proof-limit increase. No sorry, new axiom, classical/native decision or
noncomputable extraction was introduced.

Three final leaves pass focused serialized checks, with all 41 printed
gates exactly {propext, Quot.sound}. Root alone compiled: one worker, hard
20 GiB ceiling, 12 GiB reserve. Every launch had a fresh process/memory/swap
preflight: no competing compiler/runner, 87--88% system-wide free and zero
swap. No full-root/tree build, audit, guard or baseline refresh.

- `/private/tmp/ym-spatial-swap-algebra-20261008b.log`, SHA256
  `6b14fccde0acccbcd95e1a808dcac275b347c45ae13f3bbdf31739453c146d4c`.
- `/private/tmp/ym-spatial-swap-completion-20261008b.log`, SHA256
  `845e832b16b17f4d0eaab2915dba73da884c8c347903f974358127a8ab377000`.
- `/private/tmp/ym-spatial-swap-time-sector-20261008a.log`, SHA256
  `1fc44d2f3feb112b1d8ef457aa16c432219fe0373ed29a588b7a59a48b03349a`.

Imports are registered only. This bounded lane has now reached an actual
completed operator and existing physical dense-image consumer, rather than
another conditional completion wrapper. Full cubic action, represented
bond-completion map, spatial/spacing control, continuous rotations and
continuum covariance remain OPEN. Primary coupled signed response/scaling,
independent survival, physical calibration, full QFT and every-group/Clay
obligations remain OPEN. No displayed chart claim changed; no chart reprint.

### Subsequent 2026-10-08 UTC: second spatial generator and literal braid

The bounded selection above now has checked evidence: x0/x1 joins the
existing x1/x2 generator on the SAME finite slab. This is not yet a completed
S3 representation, a full cubic action or continuum covariance. Paths below
are relative to `lean/YMGap/Continuum/`.

| Declaration | Source | Exact checked scope |
| --- | --- | --- |
| `swapVertex`, `swapDir`, `swapPlane`, `swapLink`, `swapPlaquette` | `BF4ExactSlabSpatialHeadSwapGeometry.lean:32`, `:35`, `:41`, `:49`, `:51` | Literal x0/x1 exchange, with x2 and physical time x3 fixed; p01 is unoriented-fixed and p02/p12, p03/p13 exchanged. |
| `swap_edgesOf_perm`, `swap_boxLinks_perm`, `swap_completeSlabLinks_perm` | `BF4ExactSlabSpatialHeadSwapGeometry.lean:80`, `:134`, `:176` | Actual boundary occurrences retain multiplicities; the literal deduplicated complete carrier is also permuted. |
| `swapVertex_braid`, `swapDir_braid`, `swapPlane_braid`, `swapLink_braid`, `swapPlaquette_braid` | `BF4ExactSlabSpatialHeadSwapGeometry.lean:271`, `:278`, `:284`, `:290`, `:297` | Both concrete adjacent spatial swaps satisfy sts=tst on the actual vertices, directions, unoriented planes, links and faces. These are not yet completed-operator identities. |
| `swappedFaceWord_scalar`, `swappedFaceWord_character`, `correctedSlab_swappedWord_character` | `BF4ExactSlabSpatialHeadSwapWord.lean:45`, `:54`, `:61` | Only p01 reverses: mapped A,B,C,D are target D,C,B,A. Existing quaternion anti-homomorphism proves scalar invariance, without commuting factors or assuming unit norm. Every spin and original corrected-slab target remain. |
| `swapBlock`, `swapBlock_involutive`, `swapPolynomial_haar`, `link_swap_prefix`, `plaquette_character_swap` | `BF4ExactSlabSpatialHeadSwapHaar.lean:47`, `:64`, `:102`, `:121`, `:193` | Actual slab idxOf involution, supported original Haar pin, all four link coordinates including spatially moved x3 links, off-list identity fallback, and every plaquette spin. |
| `swap_originalChainFaces_perm`, `originalChainAction_swap`, `originalChainAction_weighted_haar_swap` | `BF4ExactSlabSpatialHeadSwapAction.lean:69`, `:151`, `:169` | SAME finite action/partition at arbitrary rational nome and cutoff, with width<=extent+1 and start+steps<=extent. Full spin prefix, all temporal factors and final spatial slice retained; supported insertion is explicit. |

Sol authored geometry/word; root authored the actual Haar/action consumers,
read all four complete sources and alone ran the checks. Independent final
complete-source mathematical review passed orientation, carrier/index,
braid, support, coefficient and endpoint checks. No sorry, new axiom,
classical/native decision, noncomputable extraction, proof-limit increase,
supplied symmetry, analytic premise or canonical field weakening.

All four focused checks passed on their first runs, with 39+5+13+7 printed
gates empty or within {propext, Quot.sound}. The five braid proofs are
axiom-free. Verification was serialized under the monitored lock: one
compiler, hard 20 GiB cap, 12 GiB OS reserve. Each fresh preflight found no
competing compiler/runner, 87--88% system-wide memory free and zero swap.
No root/full-tree build, audit, guard or baseline refresh was run.

| Leaf | Source SHA256 | Passing focused log and SHA256 |
| --- | --- | --- |
| Geometry | `16ef102dcd6dd296421dc88f5e6ff012de936c5e79aae38042eb249bb1722ea3` | `/private/tmp/ym-head-swap-geometry-20261008a.log`; `4450bef7eb4aa254ec64f44836217feae8dce4e4a4cd5a27dd4a9e99557c85ca` |
| Word | `44b96c90041d5abf14ac65a2dce0c94faec169209ddc11d47b6db91f50d7efe4` | `/private/tmp/ym-head-swap-word-20261008a.log`; `0d52210c82f31f9c585994f0ee4cfe802434c687d58565a61a995351de236136` |
| Haar | `2096cbd4589e77e6ce15e686f9d8830fa147fcb194db54846a96694403864202` | `/private/tmp/ym-head-swap-haar-20261008a.log`; `ff8aced5bb34f817f2559534ef75399906b76331b0213df694df6d0d9910da0a` |
| Action | `c81fe4b993f44a367c727b5623c8e8ea285425b0c45999eaf40c0df662acd6f5` | `/private/tmp/ym-head-swap-action-20261008a.log`; `04341f55e899cc7e095fa6882c282cc39a0d937dbcb9acd09447ef981d392e67` |

Imports are registered only. The actual second-generator Wilson-source,
normalized-window/reflected-form and completed-operator joins remain OPEN;
do not infer them from the geometry braid or first-generator proof alone.
Decision: stop this bounded increment at the actual finite Haar/action
consumer. Continue the joint signed interacting estimate; finite symmetry
does not supply its slow-rate, variance-survival or scaling input. Full QFT,
physical calibration, every group and the whole Clay target remain OPEN.
No displayed chart claim changed, so no chart reprint.
