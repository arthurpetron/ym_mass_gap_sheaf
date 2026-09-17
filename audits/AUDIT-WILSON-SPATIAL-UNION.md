# Coherent original Wilson spatial union and its nonvacuous strict bound

Date: 2026-09-17 UTC. This checkpoint follows pushed `2dc4201` and is
**PROGRESS**, not completion of the whole-project goal.

WHOLE-PROJECT GOAL: construct nontrivial continuum Yang--Mills on R^4,
with the required QFT axioms, isolated vacuum and strictly positive finite
physical Hamiltonian mass gap, for EVERY compact simple gauge group,
within the constructive axiom gate. **The Clay target remains OPEN.**

## Every original Wilson window has a finite operator program

2026-09-17 UTC, after pushed `de89e75`: **PROGRESS**. Every signed expression
in the existing finite Wilson-window syntax now has exact operator code on
the SAME completion. A supplied Cauchy representative's original modulus
also computes a finite program within any supplied positive squared-distance
tolerance. These are actual realization results, not new analytic premises.

### Short mathematical argument

Distribute the signed expression into scalar-character words. Sort the
offsets in each word in descending order; commutativity of the scalar
polynomial factors preserves the source polynomial. No internal edge order
of a nonabelian loop is changed. For a head at offset t in horizon H,
recursively realize the tail at horizon t, multiply by that character on
the current reflection plane, then advance by H-t. The proved descending
and within-window bounds give t+(H-t)=H, so truncated subtraction does not
change the time geometry. Exact original source-to-state descent removes
the sorting and expansion. Addition and rational scaling assemble all signed
terms, yielding equality with the original embedded window.

All paths below are under `lean/YMGap/Continuum/`.

| Checked edge | Declaration and path:line |
| --- | --- |
| Original loop/spin/offset data -> finite timed word with explicit horizon | `TimedLoop`, `BF4WilsonTimedWord.lean:21`; `WordWithin`, :30; `wordExpression_within`, :49 |
| Finite word -> descending word retaining source polynomial and time bounds | `orderWord_descending`, `BF4WilsonTimedWordOrder.lean:68`; `orderWord_within`, :74; `orderWord_source`, :111 |
| EVERY original expression -> signed words with the SAME source polynomial | `expand`, `BF4WilsonExpressionExpansion.lean:36`; `expand_source`, :143; `expand_within`, :178 |
| Existing embedded windows -> original vacuum, sum and scalar operations | `embedWindow_one`, `BF4WilsonWindowOperatorPins.lean:78`; `completedAdd_embedWindow`, :88; `completedSmul_embedWindow`, :105; `embedWindow_zero`, :110 |
| Actual bounded multiplier -> character at current reflection plane | `completedMultiply_embedWindow`, `BF4WilsonWindowOperatorPins.lean:116` |
| Actual time map -> advanced horizon, UNCHANGED original source expression | `completedTime_embedWindow`, `BF4WilsonWindowOperatorPins.lean:130` |
| Descending word -> literal program of SAME completed operations | `Program`, `BF4WilsonChronologicalProgram.lean:42`; `evaluate`, :65; `orderedProgram_pin`, :76 |
| Source identity -> unordered word realized by its chronological program | `wordProgram_pin`, `BF4WilsonChronologicalProgram.lean:94` |
| Signed expansion + exact original descent -> EVERY bounded window realized | `compileWindow`, `BF4WilsonWindowRealization.lean:49`; `compileWindow_pin`, :76; `windowCertificate`, :88 |
| Arbitrary dense union stage -> finite code and exact state equality | `stageProgram_pin`, `BF4WilsonWindowRealization.lean:97`; `stageCertificate`, :103 |
| SUPPLIED Cauchy representative + original modulus -> finite-program approximation in actual squared distance | `approximationProgram_bound`, `BF4WilsonWindowRealization.lean:112`; `approximationCertificate`, :122 |

`approximationCertificate` returns Type-level data: the base of the actual
sample `X.seq (X.modulus epsilon)`, its finite program, and the bound by
epsilon in `completedDist`. It applies the existing
`constantApproximation_bound`, `CRealSeminormCompletedApproximation.lean:84`, after the
exact stage pin. No quotient representative is chosen; no uniform support
bound for the Cauchy stream is assumed. The finite compiler itself is axiom-free.

### Remaining consumer and boundary

This closes operator realization for the ENTIRE existing Wilson-window syntax
and quantitative generation for supplied representatives of its completion.
It does not prove that this syntax contains every gauge observable or inhabit
`PositiveTimeOSRoot`, `CanonicalOSRoot.lean:268`. The limiting ambient algebra,
essentially-surjective canonical realization (:296) and scalar interface
remain unsupplied; the original CReal form has not been replaced by a rational
one. No canonical field is weakened. Full Hilbert/OS/QFT, continuous time and
its generator, spatial symmetry, changing-scale original-action control,
finite positive physical mass, continuum survival and every compact simple
group remain open. The existing fixed-spacing small-nome strict bound remains
proved; finite-program generation is not another mass estimate.

### Focused verification

Six final monitored serial one-worker/20 GiB checks passed all 46 public
gates within `{propext, Quot.sound}`, with no final warning/error. Main read
every module and alone compiled. Parallel work supplied word ordering and
signed expansion. Independent source reviews checked the chronological
geometry, original-operation evaluation, coefficient descent and final
approximation certificate; neither found a mathematical mismatch.

The operation-pin proof initially failed on dependent same-base rewriting;
the final proof uses explicit original common-base identities and the
existing null-distance consumer. The chronological evaluator initially
repeated captured section parameters in recursive calls; this was corrected.
Those failed recovery logs are not verification evidence. The final logs
below checked the finished sources, including the approximation endpoint.

No source sorry, axiom, analytic guard, canonical frontier field or resource
limit changed. Fresh preflights found no competing compiler/test/runner;
swap did not grow (6813.19 to 6797.19 MiB). Root imports added; root/full-tree/
full audit/guard unrun; CI remains manual. Final logs and SHA-256:

- `/tmp/ym-wilson-timed-word-20260917.log`:
  `9fc403b05084e863eb0e5b1a3cbdba7fbdcebbbc70a86c70ac7761d6e68606a8`
- `/tmp/ym-wilson-timed-word-order-20260917.log`:
  `07c129d8dee57d9e9ba75f6372c120a643c92d26419f0f88d55820b626477da6`
- `/tmp/ym-wilson-expression-expansion-20260917.log`:
  `28eafb171e03373e42f8ba647794470481d34e4cbe4edad58c2c624c40969a7d`
- `/tmp/ym-wilson-window-operator-pins-20260917-checked.log`:
  `029891e0fd309733ad60fabfb147d899aaefaf987b5278e3a08efde2c32f3ccf`
- `/tmp/ym-wilson-chronological-program-20260917-final.log`:
  `8e4e0db3f7729ecaed573edca4431f4c487b4c0614a49ae2968e4021c24f571d`
- `/tmp/ym-wilson-window-realization-20260917-final.log`:
  `d97a38c98187572306de2ef2b07d2901751a95e9da6677edd7357f121fa9252f`

Earlier sections retain their then-open boundaries; the finite-window
realization and supplied-representative approximation above supersede those
specific earlier open consumers, not the full canonical or continuum joins.

## Symmetric linear observables and the SAME vacuum correlations

2026-09-17 UTC, after pushed `169a236`: **PROGRESS**. The previously
constructed multiplier is now a bounded symmetric linear observable map
on the SAME completion. Its vacuum-created state and time correlations
are pinned to the original Wilson states and scalars, not an auxiliary model.

### Short mathematical argument

Reflection fixes the loop at the common center. Commutation and associativity
of the scalar character polynomials therefore move this multiplier between
the two slots of the actual reflected form. The original common-base and
pairing-limit theorems preserve that identity. Because the completed pairing
already separates vectors, symmetry and bilinearity imply zero preservation,
additivity and scalar linearity. The prior distance bound, evaluated against
the actual zero, becomes the actual squared-norm bound.

All paths below are under `lean/YMGap/Continuum/`.

| Checked edge | Declaration and path:line |
| --- | --- |
| Fixed-center reflection + coefficient algebra -> original window balance | `form_timeZero_multiplier_balance`, `BF4WilsonTimeZeroIntrinsicSymmetry.lean:46` |
| One common time horizon -> original intrinsic balance | `intrinsicForm_multiplier_balance`, `BF4WilsonTimeZeroIntrinsicSymmetry.lean:74` |
| One common spatial base -> original dense union balance | `pairing_multiplier_balance`, `BF4WilsonSpatialUnionTimeZeroOperator.lean:63` |
| Original pairing convergence -> completed multiplier symmetry | `representativeInner_multiplier_balance`, `BF4WilsonSpatialUnionTimeZeroOperator.lean:79`; `completedInner_multiplier_balance`, :89 |
| Separating original form -> zero, addition, rational and witnessed-real linearity | `completedMultiply_zero`, `BF4WilsonSpatialUnionTimeZeroOperator.lean:95`; `completedMultiply_add`, :101; `completedMultiply_smul`, :109; `completedMultiply_realSmul`, :119 |
| Existing zero + proved distance cap -> actual squared-norm cap | `completedInner_multiplier_bound`, `BF4WilsonSpatialUnionTimeZeroOperator.lean:129` |
| Symmetry -> square observable has norm-square pairing and is nonnegative | `completedInner_multiplier_square`, `BF4WilsonSpatialUnionTimeZeroOperator.lean:138`; `completedInner_multiplier_square_nonnegative`, :142 |
| Literal loop at radius zero -> original staged/embedded loop state | `loopExpression`, `BF4WilsonTimeZeroVacuum.lean:45`; `loopStage`, :49; `loopState`, :71 |
| Polynomial a*1=a + original null descent -> multiplier creates THAT state | `completedMultiply_unit`, `BF4WilsonTimeZeroVacuum.lean:90` |
| Original time map -> existing radius-advanced loop state | `completedTime_multiply_unit`, `BF4WilsonTimeZeroVacuum.lean:112` |
| Symmetry + vacuum-state pin -> actual operator correlation equals original dense pairing | `vacuumCorrelation_original`, `BF4WilsonTimeZeroCorrelations.lean:78` |
| Same vacuum means -> original connected Wilson scalar | `vacuumConnected_original`, `BF4WilsonTimeZeroCorrelations.lean:90` |
| Existing connected decay -> actual observable vacuum correlation decay | `vacuumConnected_sq_decay`, `BF4WilsonTimeZeroCorrelations.lean:102` |

`vacuumCorrelation`, `BF4WilsonTimeZeroCorrelations.lean:52`, is literally
`B U (M_L (T_n (M_K U)))`; `vacuumConnected`, :56, subtracts the two actual
vacuum expectations. The right-hand original scalar retains the existing
explicit Cauchy data `centeredMomentCauchy`,
`BF4WilsonSpatialUnionCenteredForm.lean:49`. The inherited bound concerns
the SQUARED connected correlator, with rate `twoStepRate w hd` to power n
and the actual two centered norm prefactors. It neither proves one-step
positivity nor introduces a new coupling-uniform estimate.

### Remaining consumer and boundary

The next constructive realization problem is the general ordered multi-time
Wilson expression, using these actual multipliers and the original time
maps. This would address more than the single-loop vacuum state; full
gauge-observable coverage remains a separate requirement. The canonical
`PositiveTimeOSRoot`, `CanonicalOSRoot.lean:268`, still requires its limiting
ambient algebra, positive-time support and essentially-surjective state
realization (:296), in addition to its rational-GNSData interface. This
increment neither inhabits that root nor rationalizes the actual CReal form.
No canonical field was changed. Full Hilbert/OS/QFT, continuous time and its
generator, spatial symmetry, changing-scale original-action estimates,
finite positive physical mass, continuum survival and every compact simple
group remain open. The fixed-spacing small-nome strict bound remains a
separate already proved input, not a new conclusion of symmetry.

### Focused verification

Four final monitored serial one-worker/20 GiB checks passed all 24 public
gates within `{propext, Quot.sound}`, with no final warning/error. The
vacuum proof needed an explicit same-base loop-inclusion equality; its
recovery log is not verification. Source review also identified namespace
qualification and a needed specialization of the expectation-factor rewrite,
both resolved before the relevant successful check. Main read every module
and alone compiled. Parallel work supplied the intrinsic symmetry and
vacuum identification; an independent bounded review found no mathematical
action, pairing, modulus or decay-application mismatch.

No source sorry, axiom, analytic guard, canonical frontier field or resource
limit changed. Fresh preflights found no competing compiler/test/runner;
swap remained 6813.19 MiB. Root imports added; root/full-tree/full audit/
guard unrun; CI remains manual. Final logs and SHA-256:

- `/tmp/ym-wilson-timezero-intrinsic-symmetry-20260917.log`:
  `11345d4ff4d89180f235b30741b0dc022736a41a6a3768245efb20e252320c37`
- `/tmp/ym-wilson-timezero-completed-operator-20260917.log`:
  `793f68b8591d6a8573576fa9013e9621dd92673816724275d2b9705b5884d1eb`
- `/tmp/ym-wilson-timezero-vacuum-20260917-final.log`:
  `5cf9dc2bf8fc07708645d01ab1888334938665dd132ff7a9fc852d54d363e211`
- `/tmp/ym-wilson-timezero-correlations-20260917.log`:
  `47ef40e9032c7f69f3e754038a3241a67ee647a8edb9042af81a2c2b94a770fe`

Earlier sections below retain their then-open boundaries; the operator
laws and single-loop vacuum/correlation joins above supersede those specific
earlier open consumers.

## Bounded time-zero Wilson multiplication on the SAME completion

2026-09-17 UTC, after pushed `b429d2a`: **PROGRESS**. A supplied finite
spatial loop and spin now define multiplication on the existing Wilson
union completion. Its actual squared distance is bounded by
`characterBound spin` times the original squared distance. This is an
observable bound, not a new strict transfer or physical mass estimate.

### Causal mathematical argument

The multiplier lies on the reflection-fixed slice. The certificate for
`c-a*a` is multiplied by the RETAINED fixed heat weight; conditional
reflection positivity applies to the lower-action-dressed original probe.
This gives nonnegative full-action reflected weight for `c-a*a`, hence
the multiplier estimate. It does not infer an OS bound from ordinary L2.

All paths below are under `lean/YMGap/Continuum/`.

| Checked edge | Declaration and path:line |
| --- | --- |
| Fixed-local certificate + actual action dressing -> nonnegative reflected weight | `selectedAction_fixed_weight_nonnegative`, `BF4ExactSlabSiteMultiplierBound.lean:76` |
| Certificate for c-a*a -> full-action multiplier estimate | `selectedAction_multiplier_bound`, `BF4ExactSlabSiteMultiplierBound.lean:119` |
| Literal source placement -> original fixed slice | `chartInsertion_loop`, `BF4WilsonTimeZeroChart.lean:89`; `chart_fixed_local`, :96 |
| Actual Haar-unit word + character recurrence -> spin cap certificate | `chart_squareBound`, `BF4WilsonTimeZeroChart.lean:102` |
| Same positive reciprocal partition -> normalized finite estimate | `chartScalar_timeZero_multiplier_bound`, `BF4WilsonTimeZeroMultiplierBound.lean:99` |
| Original diagonal convergence -> original limiting OS bound | `form_timeZero_multiplier_bound`, `BF4WilsonTimeZeroMultiplierBound.lean:144` |
| Radius-preserving insertion + common chart -> intrinsic norm bound | `intrinsicForm_multiplier_bound`, `BF4WilsonTimeZeroIntrinsicMultiplier.lean:113` |
| Distributivity in BOTH form slots -> intrinsic squared-distance bound | `distSq_multiplier_bound`, `BF4WilsonTimeZeroIntrinsicMultiplier.lean:143` |
| Literal zero-shift inclusion -> common-base compatibility | `inclusion_multiply`, `BF4WilsonTimeZeroIntrinsicMultiplier.lean:68`; `atBase_multiply`, `BF4WilsonSpatialUnionTimeZeroMultiplier.lean:53` |
| Computed maximum support base -> SAME union distance bound | `distance_multiply_bound`, `BF4WilsonSpatialUnionTimeZeroMultiplier.lean:96` |
| Positive epsilon/(c+1) -> actual Cauchy map and explicit modulus | `multiplierTolerance`, `BF4WilsonSpatialUnionTimeZeroMultiplier.lean:70`; `multiplierContinuous`, :114; `multiplyCauchy_modulus`, :134 |
| Existing completion quotient -> actual observable map and dense pin | `completedMultiply`, `BF4WilsonSpatialUnionTimeZeroMultiplier.lean:140`; `completedMultiply_embedStage`, :148 |
| Original distance convergence -> SAME completed squared-distance cap | `completedDist_multiply_bound`, `BF4WilsonSpatialUnionTimeZeroMultiplier.lean:167` |

The cap is computed solely from spin; the fundamental cap is four by
`characterBound`, `QuaternionHaarPolynomialSquareBound.lean:196`.
It is independent of loop length, base, radius, nome and finite regulators.
The finite selected-action estimate retains its physical face, reflection,
support, cutoff and `0<w<1` guards. The limiting carrier still requires
`hsmall`, `hd`, `hs`; no all-coupling or changing-spacing claim follows.
Each stream term gets its own computed common support base, not a chosen
uniform bound for the stream. `loopAt` has spatial shift zero, whereas
the actual centered chart has its original placement by `r+1`.

### Boundary and next mathematical consumer

Zero preservation, norm bound about the existing zero, add/scalar linearity,
reflection symmetry and observable-vacuum pins are subsequent consumers.
Full gauge-observable coverage and canonical Hilbert/OS/QFT realization
are not proved by this multiplication map. No arbitrary positive-time
multiplier is asserted. The existing fixed-spacing two-step strict bound
remains `completed_twoStep_form_gap`,
`BF4WilsonSpatialUnionCompletedGap.lean:153`; it is not reopened or replaced
by the cap above. Spatial symmetry, changing-scale original-action control,
finite positive physical mass, continuum survival and every compact simple
group remain open. No canonical frontier field or original guard changed.

### Focused verification

Five final serialized one-worker/20 GiB monitored checks passed all 35
public axiom gates within `{propext, Quot.sound}`, with no final warning,
error or `sorryAx`. The limiting form proof needed explicit coefficient-
equality method resolution; the intrinsic norm proof needed dependent-safe
`simp only` instead of `rw`. Those recovery logs are not verification.
No source sorry was added or discharged. No resource limit was raised.
Fresh preflights found no competing compiler/test/runner; swap was stable
or decreasing, 6821.19 to 6813.19 MiB for the final intrinsic/union checks.
Root imports were added; root/full-tree/full audit/guard checks were not run.
CI remains manual. Main alone compiled.

Parallel agents supplied finite action positivity, chart geometry and
intrinsic transport. Main read all files, supplied normalized limiting
control and the union/completion consumer, repaired elaboration issues,
and checked the actual endpoints. A bounded independent source review
found no action, normalization, zero-recenter, modulus or carrier mismatch.

Final logs and SHA-256:

- `/tmp/ym-site-multiplier-bound-20260917.log`:
  `9c3aea05fe2522fa9670887bdabe5922779bae75ffc0aae60b3fdfc8e5014861`
- `/tmp/ym-wilson-timezero-chart-20260917.log`:
  `70fa7c69f3dd76986db544a36ebf331357fcd6798223aa94487f17118ba3a5e3`
- `/tmp/ym-wilson-timezero-multiplier-bound-20260917-final.log`:
  `c9f713a7698f82ef0fde7a342683169e25b89ef65f9ff61a00c936018474227b`
- `/tmp/ym-wilson-timezero-intrinsic-multiplier-20260917-final.log`:
  `df576162d39f5043fbac1a5e48a2dd041daf01934a3a315f00ea9d05764605f8`
- `/tmp/ym-wilson-union-timezero-multiplier-20260917.log`:
  `98ca40b880e7c174b98b041a47b2a92da67a52382779fdd9c716887feae63715`

The following sections preserve earlier checkpoints and their then-open
boundaries; the time-zero multiplier result above supersedes that specific
earlier open multiplication obligation.

## Source Haar identities and an actual backtracking loop

2026-09-17 UTC, after pushed `d985bb7`: **PROGRESS**. The existing
supported Haar relation now transports from one finite source certificate
through the actual charts to literal equality in the SAME Wilson completion.
The physical base-one backtracking loop gives a concrete sphere-dependent
application: its fundamental character state equals the constant-two state.

### Short mathematical argument

`SupportedHaarEqv`,
`lean/YMGap/Continuum/SU2QuaternionAuxiliaryLiftAlgebra.lean:119`, tests
equality against every supported polynomial insertion. Testing by the
supported difference d gives Haar(d*d)=0. The converse uses the genuine
unit-weight finite Haar form and its already proved radical descent.
The block embedding preserves both the difference square and its Haar
integral. Hence equality transports to EVERY supported target insertion,
not only those localized to the embedding image.

All three new declarations below are in
`lean/YMGap/Continuum/SU2QuaternionHaarBlockEmbeddingSupportedEquality.lean`.

| Checked edge | Declaration and line |
| --- | --- |
| Supported Haar equality -> zero difference square | `difference_square_zero`, :46 |
| Zero difference square + actual Haar positivity -> supported Haar equality | `supportedHaarEqv_of_difference_square_zero`, :61 |
| Original embedding preserves the supported square -> target supported Haar equality | `polynomial_supportedHaar_congr`, :92 |

The target test is the fixed upper observable TIMES the full selected
heat action; it is supported on the original carrier. All interacting
factors and the common reciprocal partition remain present. The original
two convergence witnesses give equal limiting right slots. Testing by
the upper difference gives zero reflected distance and thus equality of
the original embedded states. Ordinary Haar positivity is used only to
transport observable identities; it is never identified with OS positivity.

All five new declarations below are in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionHaarObservableDescent.lean`.

| Checked edge | Declaration and line |
| --- | --- |
| Supported insertion equality + full original action -> same finite scalar | `chartScalar_reflected_haar_right`, :80 |
| Original diagonal convergence -> same limiting reflected right slot | `form_haar_diagonal_right`, :109 |
| Upper difference -> zero original window distance | `window_distSq_zero_of_haar_diagonal`, :130 |
| Actual common chart -> zero intrinsic distance | `intrinsic_distSq_zero_of_haar_diagonal`, :145 |
| Existing union distance/null embedding -> same completed state | `embedStage_eq_of_haar_diagonal`, :156 |

### Source transport and concrete sphere identity

The old chronological and translated polynomial pins feed the existing
`SupportedHaarEqv.of_padded`; both endpoint support proofs are supplied.
The auxiliary slab again supplies coordinates, not a replacement action.

All five new declarations below are in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionHaarSourceIdentity.lean`.

| Checked edge | Declaration and line |
| --- | --- |
| Source certificate + chronological embedding -> placed Haar identity | `placed_source_haar_congr`, :54 |
| Literal translated embedding -> actual centered-chart Haar identity | `chartInsertion_source_haar_congr`, :71 |
| One source certificate -> all diagonal premises -> intrinsic state equality | `embedStage_eq_of_haar_source_identity`, :100 |
| Direct signed-window source consumer | `embedWindow_eq_of_haar_source_identity`, :111 |
| Explicit physical backtrack -> actual constant-two state | `embed_backtrack_eq_constant`, :123 |

The concrete certificate is in
`lean/YMGap/Continuum/BF4WilsonBacktrackSourceIdentity.lean`:
`backtrackLink_physical`, :46, proves that the origin-x0 link really
belongs to `baseLinks 1`, excluding the off-carrier identity fallback.
`sourceLoop`, :52, has the two opposite traversals, with proved
compatibility and closure. `backtrack`, :62, and `constant`, :64, are
the actual window expressions; their `Within 0` proofs are :66 and :68.
`sourceWord_haar`, :71, uses `haarNorm_coordinate`
(`lean/YMGap/Continuum/BF4ExactSlabSymmetricPowerHaarTrace.lean:92`)
and `haarUnit_mul_conj`
(`lean/YMGap/Continuum/SU2QuaternionHaarGaugeCancellation.lean:55`).
`source_haar`, :88, then gives the original source-polynomial identity
under arbitrary insertions; `source_supported_haar`, :95, supplies the
checked completed-state consumer. No source-identity hypothesis is
assumed in this example. Original small-nome guards remain on its
completed-state theorem.

### Boundary and next join

The general result consumes supplied supported Haar certificates; it
does not prove complete representation of all gauge observables or
all pointwise functional identities. It does not define multiplication
on arbitrary OS-null classes. Canonical state/representative coverage,
the rational GNSData/CReal-form interface, full Hilbert/OS/QFT, spatial
symmetry, changing-scale original-action control, finite physical mass,
continuum survival and every-group construction remain open. None of
the canonical frontier fields or earlier physical guards is changed.

### Focused verification

Four final monitored serial one-worker/20 GiB checks passed all 23 public
gates within `{propext, Quot.sound}`, with no final warning/error. The
generic module needed namespace resolution; the concrete example needed
explicit local decidability and controlled unfolding instead of eager
reduction of the closed carrier. Recovery logs are not verification.
No resource limit was raised. Fresh preflights found no competing
compiler/test/runner; swap remained 6837.19 MiB. Main alone compiled.

The generic embedding proof and final source consumer were implemented
by main; parallel agents implemented the reflected-form consumer and
concrete source certificate. Main read all files, repaired elaboration
issues and checked the actual endpoints. A separate source review of
the generic/source transport found no support or pinning defect.

Final logs and SHA-256:

- `/tmp/ym-block-supported-equality-20260917-checked.log`:
  `1331b4fa6fdf761e22e40aa1d6872607ce5b391f6507f417e46e735bbe3c1622`.
- `/tmp/ym-wilson-haar-observable-descent-20260917.log`:
  `175c03d6442e343d91405d5fec98c05062d276f9e595640044bf79ee0b220d7c`.
- `/tmp/ym-wilson-backtrack-source-20260917-final.log`:
  `f28ded866c022482ae9cec528a2304b01a97215920db9492651b9b2b25fefb65`.
- `/tmp/ym-wilson-haar-source-identity-20260917-final.log`:
  `8991347a742d2804052cf68d83b9e8b4dc767b28e34aefa5daa4fdb2104bf3cc`.

Root imports added; root/full-tree/full audit/guard NOT run. No sorry,
axiom, prior proof, analytic guard, canonical frontier field or safety
limit changed. CI stays manual; no literature scan ran. No Clay atom
closes. The following sections are historical checkpoints.

## One finite source identity reaches the same completed states

2026-09-17 UTC, after pushed `2247bd7`: **PROGRESS**. A single padded
coefficient identity on the finite chronological source now supplies all
the diagonal identities required by the preceding observable-descent
theorem. The result is literal equality in the EXISTING Wilson completion.

The generic embedding argument pulls arbitrary coefficient probes back
along its monomial map. Padded equality needs BOTH source support guards:
they also control the sentinel source coordinate read for unused target
blocks. No out-of-source variable is silently discarded.

All three declarations below are in
`lean/YMGap/Continuum/SU2QuaternionHaarBlockEmbeddingCongruence.lean`.

| Checked edge | Declaration and line |
| --- | --- |
| Source coefficient equality -> embedded coefficient equality | `polynomial_coeff_congr`, :71 |
| Supported source -> identity padding leaves its embedding unchanged | `polynomial_identityReindex`, :91 |
| Both supported sources + padded equality -> target padded equality | `polynomial_padded_congr`, :104 |

Chronological placement at time zero in extent `base+H` first gives the
same finite-slab insertion. The literal translation has spatial offset
`r+1` and time offset `paddedWidth base r+1+t`. Existing chronological
and translated expression pins identify its output with the actual
centered chart insertion. The auxiliary slab is only a coordinate
carrier; no equality of its action with the target action is needed.

All five declarations below are in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionSourceIdentity.lean`.

| Checked edge | Declaration and line |
| --- | --- |
| One supported source identity -> actual chronological placement equality | `placed_source_congr`, :52 |
| Source/base and chart indices -> explicit placement with room proofs | `sourcePlacement`, :65 |
| Chronological placement + literal translation -> actual centered-chart equality | `chartInsertion_source_congr`, :75 |
| One source identity -> all diagonal premises -> actual intrinsic state equality | `embedStage_eq_of_source_identity`, :100 |
| Original signed windows -> direct same-state interface | `embedWindow_eq_of_source_identity`, :111 |

### Boundary and next consumer

This discharges source-identity transport for free-polynomial coefficient
equality. It does not identify all expressions equal only on the unit
quaternion sphere. The existing `HaarCarrierEqv` in
`lean/YMGap/Continuum/SU2QuaternionFactorizedHaarContraction.lean:191`
is equality of integrals against every polynomial insertion, not merely
equality of one expectation. Transport of that relation to the supported
original-action insertions and descent to these same states is a separate
next proposition, not proved by these files.

Arbitrary OS-null multiplication, full gauge-observable coverage,
canonical state/representative identification, rational GNSData/CReal-form
compatibility, full Hilbert/OS/QFT, spatial symmetry, changing-scale control,
finite physical mass, continuum survival and every-group construction
remain open. The original action, partition, completion and normalized
positive-response certificate are unchanged. No Clay atom closes.

### Focused verification

Both new modules passed their first focused monitored serial checks with
one worker and a 20 GiB ceiling. All 8 public gates lie within
`{propext, Quot.sound}`; the logs contain no warning/error. The first
coefficient-congruence theorem uses only `propext`. Fresh preflights found
no competing compiler/test/runner; swap stayed at 6837.19 MiB. Root imports
added; root/full-tree/full audit/guard NOT run. No sorry, axiom, prior
proof, analytic guard, canonical frontier field or safety limit changed.
CI stays manual; no literature scan ran.

Final logs and SHA-256:

- `/tmp/ym-block-embedding-congruence-20260917.log`:
  `f92cf477f932a23d9a6e7af52338eaee91fe89ee4ae3ff6e6421981298d4497e`.
- `/tmp/ym-wilson-source-identity-20260917.log`:
  `9ae14d0e44ddf96005afe05d4652a11f4b8a4f8a143ab2774967f96211b36fdd`.

A parallel agent implemented the generic embedding congruence and
source-reviewed the placement proof. Main read both complete files,
implemented the same-state consumer and alone performed the Lean checks.

The following sections are historical checkpoints; their open transport
claims describe the status then.

## Original polynomial identities descend to the same states

2026-09-17 UTC, after pushed `0730bef`: **PROGRESS**. Padded coefficient
equality of the actual lower observable polynomials is needed only along
the existing three-regulator diagonal. Multiplication by the fixed upper
test and the SAME full action preserves that equality. All factors have
proved support in the original carrier, so padding removes no variables;
the normalization uses the unchanged original partition.

The existing two convergence witnesses give equality in the right slot
of the limiting reflected form. Taking the upper test to be the literal
difference gives zero difference norm by bilinearity. The existing
intrinsic/union distance pins and seminorm embedding then prove literal
equality in the SAME completed carrier. This avoids any need to prove
equality of the reflected polynomials separately.

All declarations in this table are in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionObservableDescent.lean`.

| Checked edge | Declaration and line |
| --- | --- |
| Lower polynomial equality + fixed supported upper/action -> same finite scalar | `chartScalar_reflected_padded_right`, :74 |
| Equal diagonal scalars + unchanged convergence witnesses -> same limiting right slot | `form_padded_diagonal_right`, :104 |
| Upper difference + bilinearity -> zero window distance | `window_distSq_zero_of_padded_diagonal`, :125 |
| Actual common chart -> zero intrinsic distance | `intrinsic_distSq_zero_of_padded_diagonal`, :140 |
| Existing union distance and null embedding -> literal state equality | `embedStage_eq_of_padded_diagonal`, :151 |
| Concrete polynomial product commutativity -> actual state equality | `embedStage_mul_comm`, :165 |

`embedStage_mul_comm` has no semantic-equality assumption: it supplies the
polynomial identity directly and retains only the within-window guards.
The general theorem accepts the existing padded coefficient relation;
ordinary coefficient and prefix equalities can feed it through `of_coeff`
and `of_prefix` in
`lean/YMGap/Continuum/SU2QuaternionTranslationPolynomialImages.lean:51`
and :54. It does not add a parallel equivalence/scorecard structure.

### Boundary and next consumer

This is exact coefficient-polynomial equality, not a proof identifying
all functions equal only on the quaternion sphere. It does not assert
that products are well defined on arbitrary OS-null classes or completed
vectors. Full gauge-observable coverage, canonical state/representative
surjectivity and the rational GNSData/CReal-form interface remain open.
So do full Hilbert/OS/QFT, spatial symmetry, changing-scale original-action
control, finite physical mass, continuum survival and every-group producers.
The normalized response on this carrier from the preceding checkpoint
is retained, not replaced by a new vector or form.

Next: supply the diagonal premise from source-observable identities,
through actual source recentering and chronological placement.
`expression_pin` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindow.lean:172`
identifies each source polynomial's chronological embedding with its
placed polynomial. `recenterExpression` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonRecenter.lean:92`
is the actual source-box recentering used by `centeredExpression` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialComparison.lean:49`.
This checkpoint does not prove a general source-identity transport lemma
through those operations. No canonical field or analytic guard changes.

### Focused verification

The module passed the monitored serial one-worker/20 GiB check; all 6
public gates report only `{propext, Quot.sound}` and the final log has
no warning/error. The first check found only a missing namespace open
for `SupportedQuaternionBlocks`; its recovery output is not verification.
No proof statement, estimate or resource limit was changed to fix it.
Fresh process checks found no competing compiler/test/runner; swap
stayed at 6837.19 MiB. Root import added; root/full-tree/full audit/guard
NOT run. No sorry, axiom, previous proof or frontier field changed.
CI stays manual and no literature scan ran.

The final log is `/tmp/ym-wilson-observable-descent-20260917-final.log`,
SHA-256 `25e99c656feaf1c1c68ce008395c64e70391d4047017f6ece14f94178a1cb10d`.
A parallel agent implemented the new file; main read its complete source,
checked the support/quotient APIs and performed both compiler checks.

The sections below are historical checkpoints; their open descent
claims describe the status then.

## Normalized same-vector response

2026-09-17 UTC, after pushed `11cecc3`: **PROGRESS**. The exact scalar
pin at lag zero identifies the actual Wilson norm N and supplies its
existing scalar Cauchy data. Its positive local-star floor and the
original geometric prefactor give rational lower and upper bounds.
The existing clamped inverse-square-root construction returns s and a
modulus with `s*(s*N)=1`. The actual Wilson real action scales the
existing vector, preserving orthogonality and its original time map.

The resulting vector has norm one, with the same two-step response r
satisfying `0 < responseFloor/normCeiling <= r <= twoStepRate(nome) < 1`.
The lower bound uses the norm ceiling, not an uncomputed sample of the
norm stream. The upper bound is the universal bound on THIS Wilson
unit complement. Neither bound changes the carrier, observable or time.

All declarations in this table are in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean`.

| Checked edge | Declaration and line |
| --- | --- |
| Original lag-zero scalar and modulus -> actual Wilson norm | `originalNorm`, :60; `originalNormCauchy`, :64; `originalNorm_pin`, :68 |
| Existing star floor and geometric bound -> rational norm bounds | `originalNorm_floor`, :73; `normCeiling`, :79; `originalNorm_ceiling`, :84 |
| Witnessed positive norm -> computed inverse-root scalar and modulus | `normalizer`, :92; `normalizerCauchy`, :96 |
| Actual real action -> same-carrier unit vector | `unitExcitation`, :101; `unitExcitation_orthogonal`, :103; `unitExcitation_norm`, :107 |
| Original positive two-step response -> scalar floor and modulus | `responseRepresentative`, :115; `responseCauchy`, :119; `response_floor`, :123 |
| Actual time/scalar compatibility -> normalized response pin | `normalizedResponseCauchy`, :130; `normalizedResponse_pin`, :134 |
| Norm ceiling and original response -> positive rational lower endpoint | `rayleighFloor`, :141; `rayleighFloor_positive`, :143; `normalizedResponse_floor`, :151 |
| Universal same-carrier strict bound -> subunit upper endpoint | `rayleighCeiling`, :146; `rayleighCeiling_lt_one`, :148; `normalizedResponse_ceiling`, :157 |
| Vector, response, bounds, modulus and pins returned as data | `normalizedCertificate`, :165 |

### Scope and next source-backed proposition

This is fixed-spacing SU(2) at nome 1/1024. Normalized positive-time
response on the same Wilson carrier is now supplied. Full Hilbert and
canonical OS/QFT realization, full observable coverage and spatial
symmetry, changing-scale original-action control, finite physical mass,
continuum survival and every-group producers remain open. The interval
is not a spectral resolution or a physical mass calibration.

A parallel read-only review identified semantic observable descent as
a bounded next proposition. `spatialLimit_congr` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws.lean:90`
currently transports coefficient equality of the entire placed chart
insertion. The next equality must instead start from the actual lower
observable, retain the same upper test and selected heat factors, and
give mixed-pairing equality through the original diagonal limits.
Zero-distance separation then has an existing consumer:
`completedDist_embedStage` and `completedDist_zero_iff` in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionCompletedDistance.lean:83`
and :94. This paragraph is a proof plan, not a new descent theorem.

The canonical scalar mismatch is explicit in current source:
`GNSData.B`, `lean/YMGap/Continuum/GNSQuotient.lean:102`, returns Q';
actual `pairing`, `lean/YMGap/Continuum/BF4WilsonSpatialUnion.lean:113`,
returns CReal; actual `completedInner`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionPairingData.lean:132`, returns RC.
No rational-valued factorization is supplied by this normalization.
This does NOT infer that the individual values are irrational or that
such a factorization is impossible. No canonical field is changed.

### Focused verification

The new module passed on the first attempt through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check
lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean
--check-output <its olean>`. All 25 public gates report only
`{propext, Quot.sound}`, with no warning/error. Preflight found no
competing compiler/test/runner; swap was 6837.19 MiB. Root import added;
root/full-tree/full audit/guard NOT run. No sorry, axiom, prior proof,
analytic guard, canonical frontier field or safety limit changed.
Main alone compiled; CI stays manual and no literature scan ran.

The final log is `/tmp/ym-wilson-normalized-excitation-20260917.log`,
SHA-256 `b6fd17e44189bf06dda280bca8596f0d71eb8f948379a68158a043c9ce65a836`.
The older normalization module was a proof template; its vector was not
substituted for the Wilson vector. The scalar inverse-root machinery
was reused with the now-proved actual norm and response pins.

The sections below are historical checkpoints; their open normalization
and next-step claims describe the status then.

## Positive response of the existing Wilson excitation

2026-09-17 UTC, after pushed `2d466ff`: **PROGRESS**. The previously missing
scalar pin is proved. At radius zero, both literal separated Wilson
plaquette probes are coefficient-equivalent to the old face-character
probes at every lag. The joint expectation and each mean have the SAME
extent, original selected action, heat stage and partition. Their finite
connected scalars therefore agree. Uniqueness of limits compares their
unchanged three-regulator diagonals using the separately supplied
convergence witnesses; no moduli are equated and no limits interchanged.

The existing fixed-base completion map then identifies the time correlator
of `BF4WilsonSpatialUnionSmallNomeGap.vector` with this original scalar.
The older lag-THREE floor applies to this actual Wilson vector. Positivity
of `x-T_n x` and original time contraction give `B(x,T_n x)<=B(x,x)`.
Time balance applied to `T_n x` gives the odd/even comparison, so the full
lag-three floor also bounds lag two from below. This does not assume
one-step positivity or identify the two completions.

All paths in the table are under `lean/YMGap/Continuum/`.

| Checked edge | Declaration and module:line |
| --- | --- |
| Both literal separated probes agree coefficient-wise | `upperProbe_plaquette`, `BF4ExactSlabFixedSpatialWilsonPlaquetteTimePin.lean:54`; `lowerProbe_plaquette`, :66 |
| Same joint and marginal action/partition -> finite covariance equality | `connectedScalar_plaquette_pin`, same file:81 |
| Unchanged regulator diagonals -> limiting scalar equality | `centeredTimeMoment_plaquette_pin`, same file:117 |
| Actual difference positivity and time contraction -> response upper bound | `completedTime_form_le`, `BF4WilsonSpatialUnionPositiveResponse.lean:87` |
| Same time balance -> odd response bounded by preceding even response | `odd_response_le_even`, same file:101; `lagTwo_floor_of_lagThree`, :109 |
| Existing vector and original time -> Wilson scalar pin | `vector_correlator_pin`, same file:125 |
| Exact scalar equality -> old original-action scalar pin | `vector_spatial_correlator_pin`, same file:134 |
| Original scalar response floor -> actual lag-three and lag-two floors | `lagThree_floor`, same file:143; `lagTwo_floor`, :149 |
| Existing vector and positive rational floor returned as data | `positiveResponse`, same file:154 |

The inherited constant is `responseFloor = (1/16)*(1/1024)^36`, defined
by `responseFloor` in
`lean/YMGap/Continuum/BF4ExactSlabOriginalResponseNumeratorFloor.lean:37`;
its strict positivity is `responseFloor_positive`, same file:39.
The limit floor used here is `spatial_response_floor` in
`lean/YMGap/Continuum/BF4SpatialUnionPositiveResponse.lean:105`.

### Scope and next consumer

The scope is fixed-spacing SU(2) at nome 1/1024. This removes the missing
positive-time-response input on the SAME Wilson carrier, not continuum
survival or physical mass calibration. Next: use the actual norm scalar
pin, explicit Cauchy data and positive norm floor with
`PositiveCRealNormalizationScalar`, then combine normalized positive
lag-two response with the existing strict form bound. That Wilson
normalization has NOT been implemented in this checkpoint.

Full Hilbert and canonical OS/QFT realization, rational GNSData/state/
observable pins, spatial symmetry, changing-scale original-action control,
finite physical mass, continuum survival and every-group producers remain
open. No canonical frontier statement or analytic guard changed; no
beta-uniform gap, one-step positivity or Clay-atom closure is claimed.

### Focused verification

Both files passed focused serialized one-worker/20 GiB checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check
<file> --check-output <its olean>`. All 12 public gates report only
`{propext, Quot.sound}`; final logs have no warning/error. Fresh process
checks found no competing compiler/test/runner and swap stayed at
6845.19 MiB. Root imports added; root/full-tree/full audit/guard NOT run.
No sorry, axiom, prior proof, guard, frontier field or safety limit changed.
CI stays manual; no literature scan ran.

Development checks of the scalar pin required a defining-module import,
the correct coefficient-equivalence namespace, local opacity and an
explicit second limit sequence. Failed development logs are not evidence
of verification. The response consumer passed its first compiler check.
One parallel agent implemented that consumer; main read both complete
sources and ran all checks serially.

Final `/tmp/` logs and SHA-256 hashes:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-wilson-plaquette-time-pin-20260917-final.log` | 4 | `e840a37025bc9aff808d06079f9cc115f7502b6e067e5185d03ef9401b30c6c9` |
| `ym-wilson-positive-response-20260917.log` | 8 | `7650c22ca5c2f379f2ab137f0e13d505216be65300d25d6d42dd514a28956643` |

The remaining sections are historical checkpoints. Their open joins and
source-search results describe the status then, not this positive-response
closure.

## Real action, vacuum projection and all-vector relaxation

2026-09-17 UTC, after pushed `435a3ee`: **PROGRESS**. The new estimate is
`d(a*x,b*x)=(a-b)^2 B(x,x)` on the ORIGINAL Wilson stages. Together with
the existing scalar-square distance law and quadratic triangle, it gives
an explicit modulus for `s.approx(n)*X.seq(n)`. The actual pairing limit
identifies this stream's form with scalar multiplication of the old form.
Pairing separation proves quotient independence, including independence
of the supplied scalar modulus. This constructs the real action without
choosing representatives for bare quotient scalars.

The actual unit coefficient of each supplied vector stream has its own
computed scalar Cauchy data. Applying that scalar to the original unit
constructs P; subtracting P from the identity constructs C. The resulting
projection/centering are self-adjoint and idempotent, obey mixed Pythagoras,
and commute with original time. The existing strict complement bound proves
`T_2 x=x` iff `x=P x`.

The causal contraction is now an ALL-vector theorem:

```text
same completed real action + actual unit coefficient with modulus
    -> P x and C x = x-P x, with B(C x,U)=0
    + original time fixes P x and commutes with C
    + checked norm decay on the same orthogonal complement
    -> d(T_n x,P x) = B(T_n Cx,T_n Cx) <= q(w)^n B(Cx,Cx)
    -> computed tail certificate and original time-orbit limit = P x

same centered-vector time pairing = existing connected scalar
    + same-carrier Cauchy-Schwarz and norm decay
    -> K_n(x,y)^2 <= B(Cx,Cx) q(w)^n B(Cy,Cy)
```

Here d is squared distance and `q(w)=twoStepRate w hd`, not a
beta-independent or physically calibrated mass. The time orbit in the last
limit is the original UNcentered orbit of x, not an inserted surrogate.

All table paths are under `lean/YMGap/Continuum/`.

| Checked edge | Declaration and module:line |
| --- | --- |
| Original coefficient change -> squared error | `distSq_scalar_difference`, `BF4WilsonSpatialUnionScalarDistance.lean:61`; `scalar_change_bound`, :74 |
| Two error legs -> explicit stream modulus | `realScalarRate`, `BF4WilsonSpatialUnionRealScalarCauchy.lean:56`; `realScalar_bound`, :64; `realScalarCauchy`, :123 |
| Same mixed limit -> quotient real action | `representativeInner_realScalar_left`, `BF4WilsonSpatialUnionCompletedRealScalar.lean:45`; `realScalarCauchy_congr`, :64; `completedRealSmul`, :74 |
| Actual form homogeneity and scalar-independence | `completedInner_realSmul_left`, same file:84; `completedRealSmul_congr`, :96 |
| Computed scalar sums/products -> real laws | `completedRealSmul_addScalar`, `BF4WilsonSpatialUnionRealScalarAlgebra.lean:45`; `completedRealSmul_mul`, :56 |
| Original time and distance -> real compatibility | `completedTime_realSmul`, same file:99; `completedDist_realSmul`, :107 |
| Actual mixed pairing -> coefficient with modulus | `unitCoefficient`, `BF4WilsonSpatialUnionVacuumProjection.lean:69`; `unitCoefficientCauchy`, :73; `unitCoefficient_pin`, :77 |
| Coefficient times original unit -> actual projection | `unitProjectionCauchy`, same file:82; `unitProjection`, :104; `unitProjection_pairing`, :114 |
| Same projection -> centering and orthogonality | `center`, same file:167; `centerCauchy`, :169; `center_orthogonal`, :187 |
| Exact decomposition -> contractive centering | `orthogonal_decomposition_inner`, same file:239; `center_norm_le`, :243; `center_nonexpansive`, :249 |
| Same original time -> scalar and fixed-space pins | `centered_time_pairing`, same file:261; `fixed_twoStep_iff`, :268 |
| Complement norm decay -> all-vector distance decay | `distance_to_projection`, `BF4WilsonSpatialUnionVacuumRelaxation.lean:63`; `distance_to_projection_decay`, :68 |
| Connected scalar -> norm-controlled decay and original dense pin | `connected_sq_decay`, same file:74; `connected_embedStage`, :82 |
| Actual centered representative -> data-valued tail certificate | `vacuumModulus`, same file:94; `distance_to_projection_small`, :97; `vacuumCertificate`, :108 |
| Original uncentered time rows -> computed projection limit | `vacuumRows`, same file:116; `vacuumRows_modulus`, :135; `vacuumRows_limit`, :140 |

The real-scalar rate is the maximum of the scalar and vector tail anchors,
the vector modulus at `scalarTolerance(A,epsilon/4)`, and the scalar modulus
at `coefficientTolerance(B,epsilon)`, with A/B the computed scalar/norm
ceilings. Each of the two squared-distance legs costs epsilon/4 before
the triangle doubles them. For vacuum relaxation, the direct distance
cutoff is `relaxationModulus(centerCauchy X,epsilon)`; the outer Cauchy-row
cutoff uses epsilon/4. Both inner and outer moduli remain Type-level data.

### Boundary and next consumer

The scope remains fixed-spacing, small-nome SU(2). This removes the
modulus-bearing real-action and actual projection/centering joins; it does
not construct an unrestricted legacy RC-module or representatives for
arbitrary quotient-valued Cauchy sequences. Full Hilbert and canonical
OS/QFT realization, state/observable pins, normalized positive-time response
on THIS carrier, spatial symmetry, changing-spacing original-action control,
finite physical mass, continuum survival and every compact simple group
remain open. No analytic guard or canonical frontier statement changed.

The next useful analytic join is a scalar equality, not an isomorphism of
entire carriers: compare the actual Wilson plaquette connected moment at
lag THREE with the old original selected-chain scalar bounded by
`spatial_response_floor`, `BF4SpatialUnionPositiveResponse.lean:105`.
That existing theorem preserves the original full-action response floor
through a proved finite-action comparison and the unchanged diagonal limit.
It is not automatically a theorem on the new Wilson completion. The new
`centered_time_pairing` and `connected_embedStage` are its intended
same-object consumers after the scalar pin; actual contraction can then
relate lag three to lag two. Positive zero-time variance alone is insufficient.

A parallel source review identifies a bounded proof plan for the missing
scalar pin (PLAN, not a new theorem). At radius zero, compare the two
separated plaquette probes coefficient-wise using
`recentered_fundamental_placedSpan`,
`BF4ExactSlabFixedSpatialWilsonPlaquette.lean:182`, and `recenter_faceSpan`,
`BF4ExactSlabFixedSpatialLocalVariance.lean:155`. The two
`connectedScalar_selected_pin` declarations,
`BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay.lean:127` and
`BF4ExactSlabFixedSpatialUniformConnectedDecay.lean:135`, name the same
extent, selected action and cutoff. After proving the probe pins,
`finiteValue_coeff_congr`, `BF4ExactSlabSelectedTwoProbeCovariance.lean:52`,
can compare their joint and two marginal values. The unchanged diagonal
limit consumers are `connectedScalar_time_converges`,
`BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator.lean:81`, and
`originalConnected_diagonal_converges`,
`BF4ExactSlabFixedSpatialSpatialCenteredForm.lean:127`.

To retain the already constructed `BF4WilsonSpatialUnionSmallNomeGap.vector`,
use `completionMap_time` / `completedInner_map`,
`BF4WilsonSpatialUnionFixedBase.lean:117` / :110, and
`centeredVector_time_pairing`,
`BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments.lean:155`.
The desired lag-three scalar equality was NOT FOUND in the reviewed Wilson
plaquette, plaquette-moment, intrinsic-form, centered-time or response modules.
This review is a source-backed next action, not a positive-response closure.

### Focused verification

All six new modules passed on the first attempt: exit 0, all 78 public gates
within {propext, Quot.sound}, no warning/error or forbidden axiom. Main alone
compiled serially through `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>`.
Fresh process/swap checks found no competing Lean/test/runner and swap
stable at 6845.19 MiB. Root imports added; root/full-tree/full audit/guard
NOT run. No old proof, sorry, axiom, guard or safety limit changed. CI
stays manual and no literature scan ran.

A parallel agent implemented the projection module and independently
source-reviewed the all-vector relaxation, original-orbit pin and
quarter-tolerance budget. Main read the entire contributed source and
performed all compiler checks. The older scalar-action modules supplied
proof templates; only carrier-independent scalar estimates were reused
directly, and all Wilson-specific estimates were checked on the Wilson data.

Final `/tmp/` logs and SHA-256 hashes:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-wilson-union-scalar-distance-20260917.log` | 2 | `25a04b57fe42bd24448dc443134e3cea98d27b7e0758d7c2bfdc519145dde338` |
| `ym-wilson-union-real-scalar-cauchy-20260917.log` | 5 | `693c3ea0e7b5fe3b0337caf5b0597d2c9b540b3088b36b972633fa08ecc88d55` |
| `ym-wilson-union-completed-real-scalar-20260917.log` | 12 | `39f08f427620d61b9d3f8b1aff6d738bae72ec4a42f7d57eb6f498cb0b0c4c0a` |
| `ym-wilson-union-real-scalar-algebra-20260917.log` | 9 | `7503e30dd73fb6aa7be365d5ccaa3a876a4afc6185f00c9c46706b7d85e7d13c` |
| `ym-wilson-union-vacuum-projection-20260917.log` | 39 | `1f291db5d1bfebc295647216b57f438008af3b66bcf588d4f2a0e7e43e894191` |
| `ym-wilson-union-vacuum-relaxation-20260917.log` | 11 | `83e4b0d9d61f19d5b07ca74f8135f3b3cf0df6b2ba62bacc9280f9f9bd79256f` |

The sections below are historical checkpoints; use this follow-up for the
current scalar-action, projection and all-vector relaxation status.

## Rational linear geometry and represented limits follow-up

2026-09-17 UTC, after pushed `0bf2c0c`: **PROGRESS**. On the SAME Wilson
union, common-base dense bilinearity and positivity prove the parallelogram
bound `d(x+y,x'+y') <= 2d(x,x')+2d(y,y')` and exact scalar identity
`d(c*x,c*y)=c^2 d(x,y)`. No new physical estimate is assumed. Their computed
moduli lift addition and signed rational scaling to the existing completion.
The actual pairing limits prove bilinearity. Zero difference norm constructs
closeness of the original streams; testing pairings therefore proves vector
equality, rational linear laws and linearity of the original time maps.

The squared norm of this actual completed difference is the scalar limit
of the ORIGINAL stage distances. It supplies positivity, separation,
symmetry, the quadratic triangle bound and physical-time contraction.
Every field of the existing generic DistanceData is proved, not assumed.
Thus the generic diagonal limit works for supplied Cauchy rows, retaining
their representatives and both layers of moduli. Time commutes with those
limits. The previously proved orthogonal norm decay constructs its actual
time orbit as such rows, and the computed limit is the existing zero vector.

All table paths are under `lean/YMGap/Continuum/`.

| Proved edge | Declaration and module:line |
| --- | --- |
| Common-base original bilinearity | `pairing_add_left`, `BF4WilsonSpatialUnionLinear.lean:50`; `pairing_smul_left`, :71 |
| Positivity -> addition/scalar distance control | `pairing_sum_bound`, same file:136; `distSq_add`, :182; `distSq_smul`, :209 |
| Explicit moduli -> operations on SAME completion | `addCauchy_modulus`, same file:246; `smulCauchy_modulus`, :250; `completedAdd`, :253; `completedSmul`, :254 |
| Actual mixed limits -> bilinearity | `completedInner_add_left`, `BF4WilsonSpatialUnionBilinear.lean:68`; `completedInner_smul_left`, :78 |
| Zero difference norm -> computed closeness -> equality | `closeOfDifferenceZero`, same file:128; its modulus, :149; `completedSub_norm_zero_iff`, :156; `completed_eq_of_pairings`, :167 |
| Separation -> rational/time-linear laws | `completedTime_addition`, same file:197; `completedSmul_mul`, `BF4WilsonSpatialUnionLinearLaws.lean:79`; `completedTime_smul`, :112 |
| Original distances -> actual completed distance | `representativeDist_converges`, `BF4WilsonSpatialUnionCompletedDistance.lean:67`; `distanceData`, :161 |
| Same time -> completed-distance contraction | `completedDist_time_contraction`, same file:154 |
| Supplied rows -> time-compatible computed limit | `timeRows`, `BF4WilsonSpatialUnionCauchyRows.lean:51`; `timeRows_modulus`, :62; `rowLimit_time`, :65 |
| Geometric norm decay -> actual Cauchy orbit -> zero limit | `relaxationRows`, same file:84; `relaxationRows_modulus`, :105; `relaxationRows_limit`, :111 |

Addition uses `max(M_X(epsilon/4),M_Y(epsilon/4))`; scalar multiplication
uses `M_X(epsilon/(c*c+1))`, with the positive denominator supplied by
`scalarTolerance`, `BF4ExactSlabPlaquetteCompletionLinear.lean:55`.
The actual difference's pairing rate is the explicit zero-norm closeness
modulus. For represented outer rows R, the diagonal rate is
`max(R.modulus(quarter(quarter epsilon)),(quarter(quarter epsilon)).den)`,
`CRealSeminormCauchyRows.diagonalRate`, :66; `diagonalCauchy`, :98, and
`rowLimit_bound`, :109, construct and bound the limit. The decaying orbit
uses the prior `relaxationModulus(X,quarter epsilon)` to pay for the
quadratic triangle. Its direct distance-to-zero rate remains
`relaxationModulus(X,epsilon)`. All supplied moduli remain data.

This is not arbitrary quotient-sequence completeness: the rows must carry
their representatives. No real scalar is selected from a bare quotient,
and no full real Hilbert or canonical OS/QFT instance is claimed. Next is
the actual coefficient-change estimate and modulus-bearing real scalar
action, feeding unit projection/centering. Full observable coverage,
canonical state/representative pins, positive-time response/normalization,
spatial symmetry, changing-scale action control, finite physical mass,
continuum survival and every compact simple group remain open. No canonical
field, small-nome guard or AF obstruction changed; no Clay atom closes.

Five focused serial checks exited 0, all 89 public gates within
{propext, Quot.sound}, with no final warning/error. Main alone compiled
with the monitored one-worker/20 GiB policy and fresh process/swap checks;
no competing Lean/test/runner and swap at 6845.19 MiB. Root imports were
added; root/full-tree/full audit/guard checks were NOT run. Development
checks required explicit common-base rewrite arguments and local opacity
of a computed modulus; no estimate or resource limit was weakened.
Failed development logs are not verification evidence. A parallel agent
implemented the bilinear/linear-law/distance modules and independently
reviewed the row limit's same-carrier and quarter-tolerance arguments;
main read all contributed source and compiled. CI stays manual; no scan.

Final logs under `/tmp/`:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-wilson-union-linear-20260917-pins.log` | 27 | `bc699832d68991f7b5ac146cbd1d71fa762dd526d7d6574954cfa6aadd1b1f55` |
| `ym-wilson-union-bilinear-20260917.log` | 25 | `5fdc50d5b05dd5ae97029e533298fbf9a3f67a89fff7ade87e8fd79f2150ee00` |
| `ym-wilson-union-linear-laws-20260917.log` | 11 | `8a14f51f7d397a878f0609e0ecd7a5eae9f704e8af8ea8e03677035bd8345e8f` |
| `ym-wilson-union-completed-distance-20260917.log` | 17 | `361fea2188820d60569f55cb1493accb9956bb2fef583d415fad7296b22a12bf` |
| `ym-wilson-union-cauchy-rows-20260917-opaque.log` | 9 | `8d7ab864083f1db9c7e5d0c27f26290d15f4f3512190bc39ed27ed9285a8ce55` |

The sections below are historical checkpoints; use this follow-up for
the current algebra, distance and represented-limit status.

## Time balance and quantitative decay follow-up

2026-09-17 UTC, after pushed `699bff9`: **PROGRESS**. The original
time-sum identity now passes through each pair's computed common base and
the actual completed pairing limits. Thus `B(T_m x,T_n y)=B(x,T_(m+n) y)`.
The fixed unit implies `B(T_n x,U)=B(x,U)`, so its orthogonal complement
is invariant. The existing two-step form bound then gives
`B(T_1 x,T_1 x)<=q(w) B(x,x)`, and induction proves
`B(T_n x,T_n x)<=q(w)^n B(x,x)` on that SAME complement.

This removes the time/form compatibility join listed at the preceding
checkpoint below. No spectral model, eigenbasis, one-step positivity or
new analytic hypothesis is used. Sharp CS gives
`B(x,T_n y)^2 <= B(x,x) * (q(w)^n B(y,y))`; x is arbitrary and only y
must be orthogonal to U. Original dense correlators retain the literal
time advance. The result applies to the prior actual nonzero vector,
`vector_orthogonal` in `lean/YMGap/Continuum/BF4WilsonSpatialUnionSmallNomeGap.lean:69`.
It does not prove a nonzero positive-time response.

All paths in the following table are under `lean/YMGap/Continuum/`.

| Proved edge | Declaration and module:line |
| --- | --- |
| Computed common base -> original time-sum identity | `pairing_time_sum`, `BF4WilsonSpatialUnionTimeForm.lean:51` |
| Actual pairing limits -> completed time balance | `representativeInner_time_sum`, same file:74; `completedInner_time_sum`, :85; `completedInner_time_balance`, :92 |
| Same fixed unit -> invariant complement | `completedUnitCoefficient_time`, same file:129; `completedTime_preserves_orthogonal`, :132 |
| Actual completed time -> original dense correlator | `completedTime_correlator`, same file:137 |
| Strict two-step form -> one-step squared-norm bound -> iteration | `oneStep_norm_gap`, `BF4WilsonSpatialUnionRelaxation.lean:58`; `norm_decay`, :64 |
| Half-time diagonal / sharp CS -> correlator bounds | `even_autocorrelation_decay`, same file:79; `mixed_correlator_sq_decay`, :85 |
| Supplied scalar Cauchy data -> norm ceiling | `normCap`, same file:93; `norm_le_cap`, :108 |
| Explicit geometric cutoff -> late-tail tolerance certificate | `relaxationModulus`, same file:113; `norm_small`, :116; `relaxationCertificate`, :132 |

The rate is exactly the existing `twoStepRate`,
`BF4ExactSlabFixedSpatialSpatialDenseGap.lean:65`: the square of
`timeRate(w)=entropyRate(625,adjustedCoreRate(w,hd))` (:48). Its strict
positivity and upper bound use the original nome guards (:68, :72).
n counts original ONE-step advances, so the squared-norm exponent is n,
not 2n. The bound is vector/base independent at fixed w, not uniform in
bare coupling or physical spacing.

For supplied X, let s be its actual representative diagonal and cs its
computed rational Cauchy data. `normCap(X)=abs(s.approx(cs.M 1))+1`, using
`scalarCeiling`, `BF4ExactSlabPlaquetteRealScalarCauchy.lean:52`.
The threshold is `geometricCutoff(q(w),normCap(X),epsilon)`, defined in
`PositiveContractionResidual.lean:119` and certified by `geometric_bound`
(:126). It depends on nome, the supplied stream and tolerance. It is not
asserted equal for different representatives, nor selected from a quotient.

Next: completed linear operations and form laws on this Wilson union.
Full Hilbert completeness and the canonical observable/state realization
remain open, as do positive-time response/normalization, full spatial
symmetry, changing-spacing control, finite physical mass calibration,
continuum survival and the every-group theorem. Canonical frontier fields
and the AF obstruction are unchanged. No Clay atom closes.

Both focused checks exited 0, all 23 public axiom gates within
{propext, Quot.sound}, with no warnings/errors. Main alone compiled with
one monitored worker and a 20 GiB ceiling after fresh process/swap checks;
no competing build/test/runner, swap stable at 6869.19 MiB. Root imports
were added; root/full-tree/full audit/guard checks were NOT run. No prior
proof, sorry, axiom, analytic guard or safety limit changed. CI remains
manual and no literature scan ran. Independent read-only review confirmed
time normalization, complement invariance and the mixed bound's one-vector
orthogonality condition; it did not run a build.

Final logs under `/tmp/`:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-wilson-union-time-form-20260917.log` | 13 | `c9695db120023807438d09bb43bfd6a18bc713e50c42582d0c524350ced8084b` |
| `ym-wilson-union-relaxation-20260917.log` | 10 | `5b20ae21fa53dc45117938111f72be129c79b9e5f1ef0df117e23e9530abad5e` |

The remaining sections record the preceding coherent-union checkpoint;
their next-step language is historical. Use the follow-up above for the
current time/form and decay status.

## Original checkpoint: result and causal argument

The actual original Wilson limiting form and distance are independent of
enlarging the source-base guard. The proof retains the literal oriented loop
words, spins, offsets and signed coefficients. Under the original ambient
embedding, the smaller selected action becomes the masked target action,
not the full target law. Each law retains its own partition. The signed
boundary estimate compares masked and full laws before taking absolute values.

The support box has side `max(base+1,2*H+1)`, computed from the SOURCE
expression. The error amplitude and the explicit late-margin modulus do
not depend on the larger base, cutoff stage or exterior time buffer. Both
actual three-regulator diagonal convergence witnesses are used; equality
of the limits does not assert equality of their approximations or moduli.

EXPANSION isolates these original-word, action, support, interval, modulus
and limit-identification proofs. CONTRACTION composes them into coherent
mixed pairings and distances at finite common bases. One staged carrier
contains the existing finite-base Wilson windows, and one Cauchy quotient
completes that union. The base/radius/cap may grow along a supplied stream;
there is no whole-stream maximum-base assumption and no union of fixed-base
completions masquerading as a completion of the union.

Original time acts termwise and retains each supplied Cauchy modulus.
Its embedded unit is fixed through actual null distance, not literal equality
of radius-tagged unit syntax. Quantitative four-input continuity supplies
the completed pairing, its symmetry, positivity, normalization and sharp CS.

The prefactor-free centered estimate is applied at each stage's OWN positive
base. The three actual pairing limits then give
`B(x,T_2 x) <= q(w)*B(x,x)` for every unit-orthogonal vector in this SAME
union completion. Here `q(w)=entropyRate(625,adjustedCoreRate(w,hd))^2`.
The original guards give `0<q(w)<1`; the rate is independent of the vector
and its bases, but depends on nome. There is no beta-independent or
changing-spacing physical mass assertion.

The actual fixed-base completion map preserves mixed pairings, time, unit,
zero, and supplied stream/closeness moduli. The original nome-1/1024,
base-one excitation maps to a unit-orthogonal union vector with the SAME
positive norm floor, hence remains nonzero. Finally, the distance-to-zero
identity gives completed positive definiteness, with a computed closeness
modulus. The strict bound therefore forces any two-step stationary vector
in the unit complement to be zero.

## Declaration-to-dependency map

All paths in this table are under `lean/YMGap/Continuum/`.

| Proved edge | Declaration and module:line |
| --- | --- |
| Actual polynomial-level masked/full action estimate | `finiteValue_bound`, `BF4ExactSlabFixedSpatialBaseBoundaryComparison.lean:101` |
| Unchanged original ordered loop | `includeLoop_edges`, `BF4ExactSlabFixedSpatialWilsonBaseInclusion.lean:52` |
| Same ambient Wilson polynomial across source guards | `includeExpression_placed`, same file:128 |
| Original recentered insertion under actual Haar embedding | `aligned_chartInsertion_pin`, `BF4ExactSlabFixedSpatialWilsonBaseCoherence.lean:82` |
| Source-sized locality and uniform original scalar comparison | `included_chartInsertion_local`, same file:114; `chartScalar_inclusion_bound`, :129 |
| Computed larger-base-independent threshold | `inclusionModulus`, same file:153; `chartScalar_inclusion_close`, :160 |
| Actual three-regulator limit equality | `spatialLimit_inclusion`, same file:179 |
| Same intrinsic mixed form and squared distance | `intrinsicForm_inclusion`, same file:203; `distSq_inclusion`, :212 |
| Common-base original scalar and explicit Cauchy data | `pairing_at_base`, `BF4WilsonSpatialUnion.lean:122`; `pairingCauchy`, :118 |
| Actual union distance on finite comparisons | `distSq_at_base`, same file:151 |
| Arbitrary-stage Cauchy quotient and original time | `unionSeminorm`, `BF4WilsonSpatialUnionSeminorm.lean:98`; `UnionCompletion`, :139; `completedTime`, :143 |
| Supplied time-stream modulus unchanged | `time_cauchy_modulus`, same file:163 |
| Actual unit fixed by null distance | `time_unit_null`, same file:170; `completedUnit_fixed`, :176 |
| Four-input continuity, no stream-wide support cap | `pairing_close`, `BF4WilsonSpatialUnionPairingData.lean:75` |
| Actual quantitative completed pairing | `pairingData`, same file:117; `representativeInnerCauchy`, :128; `completedInner`, :132 |
| Each stage's own original centered scalar | `centeredMoment_diagonal_pin`, `BF4WilsonSpatialUnionCenteredForm.lean:83` |
| Same nome-only strict rate at every stage | `centered_twoStep_bound`, same file:102 |
| Arbitrary union streams -> actual scalar limits | `representativeCenteredMoment_converges`, `BF4WilsonSpatialUnionCompletedGap.lean:73` |
| Universal bound on the SAME completed unit complement | `completed_twoStep_form_gap`, same file:153 |
| Fixed-base maps with supplied moduli | `liftCauchy`, `BF4WilsonSpatialUnionFixedBase.lean:52`; `liftClose`, :68; `completionMap`, :82 |
| Exact completed mixed pairing and original time | `completedInner_map`, same file:110; `completionMap_time`, :117 |
| Original unit and zero retained | `completionMap_unit`, same file:125; `completionMap_zero`, :137 |
| Concrete positive strict rate | `rate_strict`, `BF4WilsonSpatialUnionSmallNomeGap.lean:53` |
| Actual nonzero excitation with positive norm and SAME strict bound | `concreteGapCertificate`, same file:102; `concreteGapCertificate_image`, :111 |
| Distance-to-zero/form-diagonal identity | `distance_zero`, `BF4WilsonSpatialUnionPosdef.lean:49` |
| Computed zero-norm closeness and its exact modulus | `closeZeroOfInnerZero`, same file:68; `closeZeroOfInnerZero_modulus`, :74 |
| Positive definite completed form | `completedInner_posdef`, same file:93 |
| No nonzero stationary vector in the unit complement | `fixed_orthogonal_eq_zero`, same file:99 |

## Exact scope and next joins

The spatial union is of the existing syntax, not a coverage theorem for
every gauge observable. Its `Stage.value` is an `IntrinsicExpression` of
spatial loops scheduled in time windows. In particular, this checkpoint
does not identify all loops traversing several time slices with this syntax.
A fixed-base completion map is not asserted to be surjective.

The immediate next carrier work is completed linear structure and time/form
compatibility on this exact union. The old PhysicalSpan union's
`completedAdd` and `completedSmul`,
`lean/YMGap/Continuum/BF4SpatialUnionLinear.lean:241` / :245, are templates,
not operations already proved on this Wilson union. Full constructive
Hilbert completeness is separate from forming a quotient of supplied
Cauchy streams.

Canonical OS realization is still open. `PositiveTimeOSRoot`,
`lean/YMGap/Continuum/CanonicalOSRoot.lean:268`, requires its actual
`positive : GNSData` (:272), representative/state inverse and support
pins, `stateEssentiallySurjective` (:296), `reflectedForm` (:298), and
`transferRepresentative` (:302). The new CReal-valued form cannot silently
replace these canonical fields, nor does a coherent spatial union supply
their missing observable-algebra realization.

Positive-time nonzero response/normalization, full spatial symmetry,
changing-scale original-action control, finite physical mass calibration,
continuum existence/nontriviality and every compact simple group's physical
producers remain open. The prior AF obstruction and canonical frontier
fields are unchanged. Positivity remains an even-time assertion. No
one-step positivity, continuum Hamiltonian, beta-uniform physical mass,
or canonical Clay-atom closure is claimed.

## Verification and source review

Eleven focused final checks exited 0, with all 152 public gates reporting
only {propext, Quot.sound} or no axioms. No final log contains a warning,
error, sorryAx, classical-choice or native-reduction dependency. Development
fixes made zero-shift and identity-inclusion pins explicit, corrected a
namespace/parameter scope, and prevented expensive implicit scalar unfolding
with local opacity. No proof statement, analytic guard or resource limit
was weakened. Failed development logs are not verification evidence.

Main alone compiled serially through `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>`.
Fresh process/swap preflights found no competing Lean/test/runner processes;
swap remained 6869.19 MiB. Root imports added; root/full-tree/full-audit/
guard checks NOT run. No old Lean proof, sorry, axiom or canonical field
changed. CI remains manual; no routine literature scan ran.

Three parallel agents developed inclusion, boundary comparison, union
carrier/seminorm, pairing, centered moments, fixed-base maps and nonvacuity.
Independent source review specifically checked masked/full normalization,
source-sized support, comparison signs, three-moment centering and the absence
of a common-base assumption for streams. Main supplied and checked coherence,
completed-gap passage and the norm-separation/stationarity consequence.

Final logs are under `/tmp/`:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-base-boundary-comparison-20260917.log` | 1 | `5a9ed21575af3a37d71a6dfeda262bebbfe89293b2a44aabb990f73b3fca9a2d` |
| `ym-wilson-base-inclusion-20260917-final.log` | 26 | `bbf422b33780f420961043b020c58bdc62bb4730770f07eb19ed9a4aa43349c0` |
| `ym-wilson-base-coherence-20260917-pin.log` | 11 | `57f52a25ee1c3b52825bac05f39dffffca6b2d2074cf61a9e3802dae743f26c8` |
| `ym-wilson-spatial-union-20260917-pins.log` | 27 | `a394a5b4e2a011770cb5cf8636c3b2edb9df2ec6f75884a7edd24ea13f860baa` |
| `ym-wilson-union-seminorm-20260917.log` | 20 | `d2cd5ad8a201af227af9f6748af77fe19794815f8d00a4357a7adbfb77bb6bdb` |
| `ym-wilson-union-pairing-20260917.log` | 15 | `97f5e3ea89da56b2986247656cbbe1bfc0dbb6ee009bd319dc2c73f64d71b562` |
| `ym-wilson-union-centered-20260917.log` | 7 | `c386841fbfe822cde523f3faf90f873f96c472284feeb1bc94a2d1525db28a9a` |
| `ym-wilson-union-completed-gap-20260917.log` | 11 | `49aef83e790777dfa003f7793452d5064734b82e1896a8d8a3e8691c14bce739` |
| `ym-wilson-union-fixed-base-20260917.log` | 13 | `55ae5c054541a6e98c48da0cf82c7b04ca58250ce2fbc3ab77a73cd220d3cfe6` |
| `ym-wilson-union-posdef-20260917.log` | 9 | `54ce5c7af33f513521d4fd63f6c5ae56e2a960f52f01779e93ef31d6300873bc` |
| `ym-wilson-union-small-nome-20260917.log` | 12 | `2a334e76cea0de5a1c0bcc48c78ff00283dab3766a47a1dfaf344360648d5ea4` |
