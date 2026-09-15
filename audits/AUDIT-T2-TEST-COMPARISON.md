# Actual T2, collar tests, and the missing range estimate

Latest local-selection follow-up, 2026-09-15, after `655cf04`: exact selected
heat-cutoff saturation now retains the COMPLETE physical face list while
its threshold ignores all detached cutoff choices. The touching cutoff B
remains fixed. These are finite Haar identities, not an OS-norm comparison.

| Result | Declaration and source | Boundary |
| --- | --- | --- |
| Actual original heat profiles | `profileHeat`, `lean/YMGap/Continuum/BF4ExactSlabLocalBulkSelection.lean:51`; `profileHeat_supported`, same file `:54`; `profileHeat_local`, same file `:60` | Original ordered plaquette factors, arbitrary individual rational nomes and finite cutoffs. |
| Computed local split | `nearIds`, `lean/YMGap/Continuum/BF4ExactSlabLocalBulkSelection.lean:65`; `farIds`, same file `:68`; `nearIds_length_le`, same file `:71`; `localHeat_pin`, same file `:88` | Incidence partition, at most six touching faces; polynomial factorization, not integral independence. |
| Detached degrees do not enter | `farHeat_degree_zero`, `lean/YMGap/Continuum/BF4ExactSlabLocalBulkSelection.lean:112`; `localDegree`, same file `:133`; `local_character_zero`, same file `:139` | One computed threshold from p and the touching B-cutoff collar; all detached factors retained at arbitrary cutoffs. |
| Exact selected heat saturation | `tail_zero`, `lean/YMGap/Continuum/BF4ExactSlabLocalBulkCutoff.lean:65`; `pairing_append`, same file `:80`; `pairing_stable`, same file `:92` | All high-spin terms cancel in the same Haar functional. No limiting estimate or positivity premise. |
| Complete physical action | `otherFaces`, `lean/YMGap/Continuum/BF4ExactSlabLocalBulkCutoff.lean:102`; `fullCutoff`, same file `:114`; `fullPairing`, same file `:117`; `fullPairing_pin`, same file `:121` | Just the selected face is separated; every other original heat factor remains in its actual position/carrier. |
| Five-neighbor bound and concrete threshold | `fullNear_length_le`, `lean/YMGap/Continuum/BF4ExactSlabLocalBulkCutoff.lean:144`; `fullDegree`, same file `:165`; `fullPairing_stable`, same file `:169` | At most five other touching faces. Exact saturation for EVERY detached cutoff profile; B, insertion and extent remain parameters. |
| Pre-existing diagonal | `fullPairing_diagonal`, `lean/YMGap/Continuum/BF4ExactSlabLocalBulkCutoff.lean:178` | Equal nomes/cutoffs give the old full original numerator by equality. Does not identify arbitrary profiles with a reflected positive Gram form. |

**NOT FOUND in these two modules:** a reflection-compatible profile pin to
`profile_form_comparison`,
`lean/YMGap/Continuum/BF4ExactSlabProfileInterfaceComparison.lean:99`,
touching-cutoff removal controlled in the original thermodynamic OS norm,
or an arbitrary-state approximate preimage for `certificateOfRangeApproximation`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicZeroTimeCertificate.lean:190`.
No reflection positivity for arbitrary mixed profiles, fixed-source
volume-invariant threshold, coupling-uniform strict floor or physical mass
claim is made. These missing comparisons remain ledgered. Twenty-five exact
public gates passed within {propext, Quot.sound}; no full-tree run or changed
canonical field. Exact verification scope/hashes are in `work_plan.md`.

Previous localized-interface follow-up, 2026-09-15, after `b97335a`: the finite
comparison factor now charges ONLY changed physical crossing faces. The
existing shared channels and original bulk dressing are retained. This removes
the whole-interface factor from this comparison, not the independent
original-norm range obstruction.

| Result | Declaration and source | Boundary |
| --- | --- | --- |
| Individual factors on the same trees | `finiteProduct_factors`, `lean/YMGap/Continuum/BF4ExactSlabProfileInterfaceComparison.lean:46` | Product of per-face factors; no independence of overlapping channels. |
| Actual crossing profiles and old constant pin | `profilePolynomial`, `lean/YMGap/Continuum/BF4ExactSlabProfileInterfaceComparison.lean:63`; `profileExpansion`, same file `:66`; `profileForm`, same file `:70`; `profileForm_constant`, same file `:74` | Actual centralFixedFaceIds; same physical Gram channels; the constant profile is the previous interface. |
| Same-p reflected comparison | `profile_weight_bound`, `lean/YMGap/Continuum/BF4ExactSlabProfileInterfaceComparison.lean:89`; `profile_form_comparison`, same file `:99` | Supplied coefficient inequalities multiply; p and all its shared-variable dependence stay unchanged. |
| Exact local reference and floor | `referenceNome`, `lean/YMGap/Continuum/BF4ExactSlabLocalInterfaceCoercivity.lean:45`; `factorProduct_pin`, same file `:68`; `localFloor`, same file `:79`; `localFloor_positive`, same file `:86`; `localReference`, same file `:91` | Only selected faces change nome w to one at the same finite cutoffs. Floor w^(sum selected K_f(K_f+2)), positive for w>0. |
| Both finite inequalities | `local_lower`, `lean/YMGap/Continuum/BF4ExactSlabLocalInterfaceCoercivity.lean:94`; `local_upper`, same file `:112` | 0<=w<=1, same p and actual physical face list. Unnormalized forms, not completed OS norms. |
| Selected physical count | `changedFaceCount`, `lean/YMGap/Continuum/BF4ExactSlabLocalInterfaceCoercivity.lean:126`; `changedEnergy_constant`, same file `:129`; `localFloor_constant`, same file `:137` | At common cutoff K, exact floor w^(K(K+2)*S), S=selected physical count, not whole-interface size. |
| Untouched cutoffs are arbitrary | `changedEnergy_bound`, `lean/YMGap/Continuum/BF4ExactSlabLocalInterfaceCoercivity.lean:144`; `local_lower_bounded`, same file `:158` | One factor w^(N(N+2)*S) for every untouched cutoff profile; only selected cutoffs are assumed <=N. No bound independent of w, N or a growing selected mask. |
| Original full-action numerator | `originalLocalReference`, `lean/YMGap/Continuum/BF4ExactSlabLocalInterfaceCoercivity.lean:171`; `original_local_lower`, same file `:176`; `original_local_upper`, same file `:184` | Common K; p is actual dressedLower w K e and old original_interface_pin identifies the target numerator. Same bulk dressing, no partition change or marginal replacement. |

**NOT FOUND in these two modules:** a source-observable-specific selected mask
with controlled changed-face degrees through the bulk limit, a normalized
thermodynamic original-OS-norm comparison, or an actual approximate preimage.
No arbitrary-profile original temporal-action identity is asserted. The finite
nome-one reference is not an infinite heat law. The existing range consumer
`certificateOfRangeApproximation`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicZeroTimeCertificate.lean:190`,
still needs a supplied Cauchy preimage with squared-distance error epsilon/128;
`Certificate.continuityData`, same file `:138`, then constructs the time-zero
radius. This local floor does not supply that input.

Thirty exact public gates passed within {propext, Quot.sound}; exact scope and
hashes are in `work_plan.md`. No full-tree run, new analytic premise, canonical
field change or literal hole. Injectivity/range density, full-space time zero,
physical Hamiltonian, beta(a)/spacing, continuum/QFT, other compact simple groups
and Clay remain open. Earlier checkpoints follow.

Previous geometric-time identification follow-up, 2026-09-15, after `e838e34`:
the old constructed positive root equals the ORIGINAL geometric T1 on the
EXISTING completion. The previous positive-real-time action at n/2 now equals
original lattice time n, including odd n. Its time unit is unchanged: A(1)=T2.

| Result | Declaration and source | Boundary |
| --- | --- | --- |
| Actual time commutes with the old calculus | `time_polynomialVector`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricRootIdentification.lean:51`; `time_polynomialOperator`, same file `:59`; `sequenceAction_time`, same file `:64`; `rootAction_time`, same file `:82` | Every original integer lag; original polynomial composition and explicit-modulus row pairing limits. |
| Geometric root identification | `geometric_one_eq_root`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricRootIdentification.lean:86`; `generator_one_geometric`, same file `:132` | T1=rootAction on all old completed states. Uses original T1 positivity, commutation, common square T2 and the already constructed next root; no inverse or kernel-zero premise. |
| Explicit old time units | `geometric_mesh_value`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricTimePins.lean:39`; `geometricTime`, same file `:44`; `geometricTime_real`, same file `:46` | Constructed time data with value n/2, n>0; no physical-spacing rescaling. |
| Every original lattice step is recovered | `dyadic_geometric`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricTimePins.lean:50`; `positiveAction_geometric`, same file `:57`; `positiveAction_at_geometric`, same file `:62`; `realTimeAction_geometric`, same file `:68` | Existing dyadic and positive-real-time operators equal original completedTime n, including odd n; any supplied time presentation with the proved same value. |
| Same semigroup and integer translations | `realTimeAction_geometric_commutes`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricTimePins.lean:72` | The previous positive-real-time semigroup commutes with every original lattice translation. |

**NOT FOUND in these two modules:** arbitrary-state approximate-range data,
injectivity/range density or full-space time-zero continuity. These remain
ledgered. The existing consumer `certificateOfRangeApproximation`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicZeroTimeCertificate.lean:190`,
requires an actual Cauchy preimage with squared-distance error epsilon/128;
`Certificate.continuityData`, same file `:138`, returns a positive radius.
Neither input is produced for arbitrary unshifted observables here.
Physical Hamiltonian, beta(a)/spacing, continuum/QFT, other groups and Clay
remain open. Fourteen exact public gates passed within {propext, Quot.sound};
no full-tree run, changed canonical field or added analytic premise. Exact
scope/hashes are in `work_plan.md`. Older open-root statements below are
historical checkpoint/module boundaries, superseded by this identification.

Previous completed-positivity follow-up, 2026-09-15, after `4d27795`: the
ORIGINAL geometric T1 is now proved positive on the EXISTING thermodynamic
completion. The proof consumes the full-action site square and the actual
odd/even comparison; it does not substitute a positive root for geometric time.

| Result | Declaration and source | Boundary |
| --- | --- | --- |
| Same spacetime expression on the even carrier | `evenEvaluate`, `lean/YMGap/Continuum/BF4ExactSlabSpacetimeEvenComparison.lean:60`; `evenSquareBound`, same file `:68`; `evenLocal`, same file `:78`; `inclusion_pin`, same file `:87` | Actual translated original holonomies; constructed cap/support/locality and original coordinate-inclusion image. |
| Fixed-size probe and old rate | `parity_bound`, `lean/YMGap/Continuum/BF4ExactSlabSpacetimeEvenComparison.lean:112` | Original even/odd expectation difference <= old amplitude times rate^(margin+1-boxSize); explicit small-nome and entropy guards. No margin-dependent probe-size loss. |
| Same existing thermodynamic limit | `evenVolumeModulus`, `lean/YMGap/Continuum/BF4ExactSlabSpacetimeEvenComparison.lean:139`; `evenSequence_close`, same file `:142`; `evenSequence_converges`, same file `:170` | Computed old volume modulus at epsilon/4; reaches existing meanLimit at nome 1/1024, not a newly chosen even-family state. |
| Actual one-step reflected square | `lower_oneSided`, `lean/YMGap/Continuum/BF4ExactSlabSiteOneStepForm.lean:83`; `one_step_face`, same file `:103`; `one_step_reflection`, same file `:113`; `oneStepExpression`, same file `:133`; `insertion_pin`, same file `:136` | Original boundary-touching insertions, literal shifted reflection plane and ordered temporal orientation. |
| Full original expectation and dense one-step form | `site_expectation_pin`, `lean/YMGap/Continuum/BF4ExactSlabSiteOneStepForm.lean:155`; `even_one_step_nonnegative`, same file `:171`; `one_step_form_nonnegative`, same file `:178` | Retains every original heat factor and the same partition, then passes site positivity to the old thermodynamic form. |
| Entire existing completion | `presented_one_step_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicOneStepPositivity.lean:37`; `representative_one_step_nonnegative`, same file `:45`; `completedTime_one_nonnegative`, same file `:51` | Existing time_inner_bulk, pairing limits and quotient descent prove <T1 x,x> >= 0 for every old completed state. No new positivity hypothesis. |
| All integer lags | `completedTime_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicOneStepPositivity.lean:57` | Same old time symmetry/composition, now including odd lags. |

**NOT FOUND in these three modules:** equality of geometric T1 with
`rootAction`, arbitrary-state approximate-range/density data, injectivity or
full-space time-zero continuity. These remain open ledgered obligations;
positivity is not strict positivity. Physical Hamiltonian, beta(a)/spacing
control, continuum/QFT, other compact simple groups and Clay remain open.
Twenty-three exact public gates passed with {propext, Quot.sound}; no new
axiom/hole, canonical field or analytic premise. No full-tree run; exact
verification scope/hashes are in `work_plan.md`. The historical NOT FOUND
statements below describe their named modules/checkpoints, not this later result.

Previous geometry/action follow-up, 2026-09-15, after `933bd55`: the actual
odd/adjacent-even inclusion and its normalized original-law boundary comparison
are now proved. No coordinates move; only actual finite enumeration indices
change. This supplies the parity geometry previously missing below, not the
literal one-step insertion pin or completed positivity.

| Result | Declaration and source | Boundary |
| --- | --- | --- |
| Actual carrier inclusion | `embedding`, `lean/YMGap/Continuum/BF4ExactSlabCoordinateInclusion.lean:74`; `link_pin`, same file `:95`; `plaquette_pin`, same file `:130`; `character_pin`, same file `:137`; `odd_even_room`, same file `:144` | Injective original block map; same ordered holonomy at the same coordinates; any source <= target, including odd/even. |
| Full action retains the exterior | `kept_perm`, `lean/YMGap/Continuum/BF4ExactSlabCoordinateAction.lean:70`; `full_action_split`, same file `:82` | Kept faces are exactly source images. Original exterior factors, including shared-link dependence, remain explicit. |
| Exact insertion and heat transport | `heatFactor_pin`, `lean/YMGap/Continuum/BF4ExactSlabCoordinateAction.lean:110`; `heatProduct_pin`, same file `:123`; `numerator_pin`, same file `:130`; `partition_pin`, same file `:159` | Every rational w and finite K. Supported source insertion and source action move through the same map. |
| Original normalized source law | `numeratorLimit_pin`, `lean/YMGap/Continuum/BF4ExactSlabCoordinateAction.lean:174`; `partitionLimit_pin`, same file `:183`; `expectation_pin`, same file `:190`; `expectation_pin_of_prefix`, same file `:206` | Existing cutoff limits, same partition cancellation; explicit small-nome guards, not an equality with the full target law. |
| Constructed source preimage and separation | `facePreimage`, `lean/YMGap/Continuum/BF4ExactSlabCoordinateBoundaryComparison.lean:67`; `RootCeiling`, same file `:84`; `exterior_distance`, same file `:87`; `shifted_base_ceiling`, same file `:101` | Computed physical face index. Far-side root clearance suffices because no negative-coordinate exterior is added. |
| Active cores pay distance | `core_size_floor`, `lean/YMGap/Continuum/BF4ExactSlabCoordinateBoundaryComparison.lean:110` | margin+1-|probe.support| <= |core|; consumes the existing actual-animal distance theorem. |
| Cross-parity normalized estimate | `expectation_bound`, `lean/YMGap/Continuum/BF4ExactSlabCoordinateBoundaryComparison.lean:119`; `odd_even_bound`, same file `:140` | Full even expectation versus EXISTING odd expectation, bounded by (c+c)*summedBoundaryBudget with the explicit probe-size loss and coupling guards. |

**NOT FOUND in these three modules:** a construction of the one-step reflected
insertion as the even site square, its translated bounded-size probe, or the
thermodynamic limit application. `time_inner_bulk`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeBalance.lean:70`, is the
existing intended pairing consumer; these modules do not yet identify its
insertion. Completed T1 positivity/root equality and the independent range
obligation remain open. Thirty-four exact public gates passed within
{propext, Quot.sound}; no full-tree run. No canonical field or analytic premise
changed. Exact verification scope and hashes are in `work_plan.md`.

Previous cutoff-limit follow-up, 2026-09-15, after `3fdebff`: normalized site
reflection positivity now survives heat-cutoff removal at each fixed even
volume. Arbitrary-mask normalized boundary response is also proved without
an odd/even restriction. This does not identify the thermodynamic T1 form.

| Result | Declaration and source | Boundary |
| --- | --- | --- |
| Actual positive finite partition | `partitionFloor`, `lean/YMGap/Continuum/BF4ExactSlabFaceSetExpectation.lean:44`; `partition_floor`, same file `:61` | (1-delta(w))^|ids|, explicit small-nome guards and physical face list; not volume-uniform. |
| Original normalized cutoff and limit | `finiteValue`, `lean/YMGap/Continuum/BF4ExactSlabFaceSetExpectation.lean:70`; `partition_cancellation`, same file `:79`; `expectation`, same file `:83` | Same numerator, same partition and original cutoff limit, any extent. |
| Computed two-index control | `finiteCauchy`, `lean/YMGap/Continuum/BF4ExactSlabFaceSetExpectation.lean:135`; `expectationCauchy`, same file `:141`; `approx_close`, same file `:165` | Explicit raw-cutoff and actual-representative moduli; w/extent/face-list/insertion dependence retained. |
| Existing odd law is unchanged | `odd_expectation_pin`, `lean/YMGap/Continuum/BF4ExactSlabFaceSetExpectation.lean:206` | Full odd specialization equals the pre-existing polynomial expectation by partition cancellation. |
| Site positivity after cutoff removal | `site_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabSiteExpectation.lean:63`; `existingNome_site_nonnegative`, same file `:71` | Fixed even volume, full original action and normalization. Original p fixed; cutoff-dependent C(p*L_K) is not a fixed state. |
| Both partitions cancel | `finite_mask_bound`, `lean/YMGap/Continuum/BF4ExactSlabFaceSetBoundaryComparison.lean:102`; `mask_bound`, same file `:110` | Actual determinant bound passes to normalized expectation difference with unchanged coefficient. |
| Existing core tail reaches normalized law | `mask_tail_bound`, `lean/YMGap/Continuum/BF4ExactSlabFaceSetBoundaryComparison.lean:123` | Arbitrary physical mask and extent; explicit finite core-size condition and coupling guards, not a transfer gap. |

**NOT FOUND in these three modules:** the literal odd/even slab inclusion,
its observable/reflection identity, or the receding-volume comparison to the
existing thermodynamic one-step form. The older
`Placement.source`, `lean/YMGap/Continuum/BF4ExactSlabOffsetHaarEmbedding.lean:47`,
and `Placement.target`, same file `:48`, are both odd `centralExtent` slabs;
their definitions do not supply this parity change.
Completed T1 positivity/root equality and the independent range obligation
remain open. Twenty-three exact public gates passed within {propext, Quot.sound};
no full-tree run. Exact verification evidence is in `work_plan.md`.
No canonical field or analytic premise changed. Earlier checkpoints follow.

Previous finite follow-up, 2026-09-15, after `95cca6b`: the conditional-square
identity now retains the FULL ORIGINAL heat action on the actual even slab.
This closes the finite heat-action input on the geometric T1 positivity branch,
not the thermodynamic one-step pin or the separate T2 range estimate.

| Finite result | Declaration and source | Boundary |
| --- | --- | --- |
| Shared weight is retained | `conditional_weighted_square`, `lean/YMGap/Continuum/BF4ExactSlabSiteWeightedSquare.lean:130` | Arbitrary signed supported boundary-local W; H((theta(p)*p)*W)=H(C(p)^2*W). |
| Weight certificate gives positivity | `certified_weighted_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabSiteWeightedSquare.lean:165` | Existing constructive Haar certificate, not a supplied analytic positive form; no boundary-locality assumption on individual square features. |
| Actual heat locality | `lowerHeat_oneSided`, `lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:90`; `fixedHeat_local`, same file `:101` | Lower temporal faces retain the shared spatial links; all fixed-face links are fixed. |
| Original full action splits | `lowerHeat_reflection`, `lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:135`; `fullHeat_split`, same file `:143`; `fullAction_dressing`, same file `:155` | Actual face partition and original heat polynomials, not the positive multiplicity-product model. |
| Full finite site square | `fullAction_square`, `lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:173` | H((theta(p)*p)*fullHeat)=H(C(p*L)^2*W), every finite K/radius and rational w; p supported and one-sided. |
| Actual small-nome positivity | `fixedHeatCertificate`, `lean/YMGap/Continuum/BF4ExactSlabSiteHeatAction.lean:191`; `fullAction_nonnegative`, same file `:197`; `existingNome_fullAction_nonnegative`, same file `:208` | Explicit guards 0<=w<=1, heatRatio(w)<=1/2, heatRemainderBound(w)<=1, discharged at 1/1024. Nonnegativity only, not a strict gap or beta-uniform rate. |

**NOT FOUND in these two modules,**
`BF4ExactSlabThermodynamicTimeBalance.lean`, or
`BF4ExactSlabThermodynamicSquareRootAction.lean`: identification of this full
finite site form and its normalized limits with the existing thermodynamic
geometric one-step pairing. `one_step_balance` remains a symmetry statement;
`rootAction_nonnegative` concerns the separately constructed positive root.
Neither supplies the missing pin. C(p*L) depends on the cutoff and is not
asserted to be an original fixed observable or a transfer preimage.

Twenty exact public axiom gates passed within {propext, Quot.sound}.
Focused check/dependency-build boundaries and hashes are in `work_plan.md`;
no full-tree run. No new analytic premise, canonical-field change or hole.
The following dated checkpoint records the preceding unweighted result.

Previous finite follow-up, 2026-09-15, after `941b2ae`: the integer-slice
conditional-square calculation is now proved for arbitrary supported one-sided
polynomials, with the boundary polynomial computed from their original monomials.
This addresses a finite input to the separate geometric T1 positivity branch,
not the missing T2 range estimate. The full heat-weighted thermodynamic T1 pin
is not a theorem of the modules below.

| Finite result | Declaration and source | Boundary |
| --- | --- | --- |
| Actual side exchange | `blockSide_reflection`, `lean/YMGap/Continuum/BF4ExactSlabSiteHaarFactorization.lean:64` | Existing boundary-complete even slab and literal link reflection. |
| Shared-slice factorization | `pairing_factor`, `lean/YMGap/Continuum/BF4ExactSlabSiteHaarFactorization.lean:107`; `sum_pairing`, `lean/YMGap/Continuum/BF4ExactSlabSiteHaarFactorization.lean:211` | Strict halves integrate separately; the shared spatial-link Haar integral and every signed mixed term remain. |
| Boundary reflection is proved | `boundary_reflection`, `lean/YMGap/Continuum/BF4ExactSlabSiteBoundaryReflection.lean:135` | Finite block locality implies the actual polynomial reflection identity. No supplied reflection premise in the final result. |
| Computed original monomial split | `pieces`, `lean/YMGap/Continuum/BF4ExactSlabSiteConditionalSquare.lean:111`; `pieces_pin`, `lean/YMGap/Continuum/BF4ExactSlabSiteConditionalSquare.lean:116` | Every one-sided input polynomial is reproduced on its declared carrier. Support is separately required before taking the full Haar identity. |
| Witnessing boundary polynomial | `conditionalPolynomial`, `lean/YMGap/Continuum/BF4ExactSlabSiteConditionalSquare.lean:124`; `conditional_local`, `lean/YMGap/Continuum/BF4ExactSlabSiteConditionalSquare.lean:132` | Explicit finite data on the shared slice, not an original OS state or a transfer preimage. |
| Original unweighted reflected square | `conditional_square`, `lean/YMGap/Continuum/BF4ExactSlabSiteConditionalSquare.lean:138`; `one_sided_reflection_nonnegative`, `lean/YMGap/Continuum/BF4ExactSlabSiteConditionalSquare.lean:167` | H(theta(p)*p)=H(C(p)*C(p))>=0 for arbitrary supported one-sided polynomials. No heat action or beta-uniform rate occurs. |

The three new modules passed 40 exact public axiom gates within
{propext, Quot.sound}; final focused logs and hashes are in `work_plan.md`.
No full-tree check. **NOT FOUND in these three modules,**
`BF4ExactSlabThermodynamicTimeBalance.lean`, or
`BF4ExactSlabThermodynamicSquareRootAction.lean`: a declaration identifying this
site Haar square with the full original heat-weighted thermodynamic T1 form.
That identification and the independently missing original range estimate
remain open; no canonical field or analytic premise changed.

Latest implementation follow-up, 2026-09-15, after `b0f695b`: the scalar-test
identification branch is CLOSED through the existing completion. The new
`completedTest_represented`,
`lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean:96`, identifies
the test with pairing against the original embedded plaquette scaled by 1/128.
The full action, original cutoff normalization, volume family and completed
pairing are retained. Details and exact source pins are in the final section.
This supplies no new separating information beyond that existing pairing;
the actual-transfer range obligation below remains open. Earlier dated
follow-ups record their own verification boundaries.

Second implementation follow-up, 2026-09-15: original interior presentations
now have literal geometric T1 preimages, with no analytic range premise.
All declarations in the following table are in
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicInteriorTimePreimage.lean`.

| Source result | Declaration and source | Boundary |
| --- | --- | --- |
| Computed support test | `Interior`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicInteriorTimePreimage.lean:77`; `interiorDecision`, same file `:84` | Every syntactic character generator has maximum face time strictly below the reflection plane. Sufficient condition only. |
| Box enlargement cannot create this margin | `interior_enlarge`, same file `:95`; `boundary_top`, same file `:72` | Ordinary zero-lag enlargement preserves the test; a lower face failing the strict inequality touches the plane. No claim about semantic non-membership in the range. |
| Original-link polynomial preimage | `polynomial_translate_preimage`, same file `:161` | Translating the computed inward expression back gives the literal original polynomial at every common volume >=base+2. No measure or exterior interaction is changed. |
| Same completed state | `completed_preimage`, same file `:178` | The existing completed geometric T1 maps the constructed presentation to the original interior state. |
| Actual approximate range and time zero | `interiorApproximationCertificate`, same file `:184`; `interiorZeroContinuityCertificate`, same file `:196` | Returns approximate original T2 preimages and a positive time-zero radius, consuming the preceding geometric-range estimate. |

Boundary-touching source expressions remain outside this construction's scope.
Density of the interior family is not proved. A failed syntactic test does not
imply that its completed state lies outside the range. This narrows the missing
source comparison without establishing full-space time zero or limit injectivity.
The new module passed 18 focused public axiom checks (one axiom-free, the rest
within {propext, Quot.sound}); no full-tree audit. The exact log/hash, initial
check corrections and safe-build boundary are recorded in `work_plan.md`.
The dated source baseline and findings below are preserved.

Implementation follow-up, 2026-09-15: the restricted geometric one-step
range now has the approximate-preimage data discussed here.
`oneStep_residual_weighted`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricRangeContinuity.lean:95`,
proves `n * ||(I-T2)^n T1 x||^2 <= ||x||^2` using nonnegative mixed moments.
`oneStepApproximationCertificate`, same file `:131`, computes original
approximate T2 preimages for supplied geometric T1 states, and
`oneStepZeroContinuityCertificate`, same file `:160`, gives time zero there.
This does not supply approximate range for every unshifted dense presentation,
which remains the missing data in the dated audit below. No exact T1 preimage
under T2, T1 positivity, or identification T1=A(1/2) is asserted.

Date: 2026-09-15. Source baseline: `5067234`, plus the independently checked
`PositiveTransferLimitKernelFence.lean` recorded below. This is a mathematical
route review, not a closure of a physical frontier or a replacement for the
group-dependence audit. Sections explicitly distinguish source results,
paper arguments, and unsupplied data.

The whole-project goal is unchanged: for each compact simple gauge group,
construct the nontrivial continuum Yang--Mills theory required by the Clay
problem, with its QFT axioms and positive physical Hamiltonian mass gap.
The repository's constructive axiom gate and explicit-witness requirements
remain in force; see `work_plan.md`, opening goal and execution instructions.

## Finding

The original thermodynamic collar tests separate states, but the inspected
source does not connect annihilation by the actual T2 to annihilation of those
tests. Requiring a bounded test functional relative to the T2 norm is a
sufficient but stronger route than approximate range membership. Finite-box
strict positivity cannot fill this gap just by taking a limit: the new
constructive counterexample retains a common excited-sector upper gap and
an explicit uniform-over-vectors convergence estimate, yet its limit has a
nonzero kernel. It is **not** evidence that the actual T2 has a kernel.

## 1. Source-backed consumers and boundaries

All paths below are relative to the repository root. `completedDist` is
squared distance, not distance; the tolerance budgets below respect that.

| Actual object/result | Declaration and source | What its statement supplies |
| --- | --- | --- |
| Thermodynamic two-step transfer | `twoStepTransfer`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean:197` | The existing `completedTime 2`, not a heat-bath generator. |
| Transfer geometry | `twoStepTransfer_symmetric`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean:204`; `twoStepTransfer_positive`, same file `:207`; `twoStepTransfer_contraction`, same file `:210`; `twoStepTransfer_unit`, same file `:213` | Symmetry, nonnegative form, norm contraction and fixed unit on the original completion. Strict positivity is not the assertion of `twoStepTransfer_positive`. |
| Physical dense time shift | `translate`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeGeometry.lean:74` | Uses the actual bulk/time embedding of the source expression. |
| Common discrete kernel | `time_positive_kernel_equal`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeKernel.lean:63`; `positive_range_no_further_kernel`, same file `:72` | All positive discrete times have the same kernel; no additional annihilation on positive-time ranges. Neither says the common kernel is zero. |
| Original collar tests | `dressedTest`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCollarTestDensity.lean:90` | Multiplies the source expression by the finite source collar, at its own base. |
| Constructive collar approximation | `approximationCofactor`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCollarTestDensity.lean:94`; `approximationCofactor_spec`, same file `:98` | Computes a nearby dressed test from supplied original Cauchy data and a squared-error tolerance. |
| Actual test separation | `completed_zero_of_collar_tests`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCollarTestDensity.lean:138`; `completed_eq_iff_collar_tests_eq`, same file `:168` | Vanishing against every test in this family implies zero; equality of all pairings implies state equality. No T2 image assertion. |
| Actual translated norm samples | `norm_pin`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicTranslatedChannelPacket.lean:45`; `approximationCertificate`, same file `:128`; `twoStepTransfer_norm_interval`, same file `:167` | Computes a volume, crossing cutoff and numerical precision enclosing the original translated norm. A scalar norm interval is not a comparison with the unshifted tests. |
| Existing candidate preimages | `partialPreimage`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicRangeApproximation.lean:51`; `partialPreimage_identity`, same file `:60` | With D=I-T2, the finite sum P_n satisfies T2(P_n x)+D^n x=x. |
| Exact residual, with original representative | `partialPreimage_distance`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicRangeApproximation.lean:89`; `approximationCertificate`, same file `:108` | The squared error is `mixedMoment x 0 (n+n)`; a supplied representative computes the candidate preimage and residual CReal. No smallness threshold for an arbitrary x. |
| Already available range decay | `range_residual_small`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicRangeDefectEnergy.lean:124` | Computes residual smallness for x of the form T2(point X), not every original x. |
| Actual time-zero consumer | `twoStep_range_zero_bound`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.lean:84`; `twoStepZeroContinuityCertificate`, same file `:91` | Computes a positive time radius for continuity at zero on T2(point X). |
| Extension estimates | `approximationData`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedApproximation.lean:58`; `completedDist_three_segment`, same file `:84`; `realTimeAction_distance_contraction`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveRealSemigroup.lean:96` | Original dense approximation, explicit squared-distance triangle budget, and nonexpansiveness of the actual positive-real-time action. |

**NOT FOUND in these inspected modules:** a construction returning, for each
dense presentation p and each positive rational eta, an original Cauchy
representative Y with `completedDist (T2(point Y)) (embedPresentation p) <= eta`.
The finite `approximationCertificate` returns an exact residual but does not
make that residual small for arbitrary p. This missing estimate remains an
open analytic obligation, not a newly added hypothesis or scorecard field.

## 2. Classical review: exact range is stronger than needed

The following is a paper argument in ordinary real Hilbert-space language,
**not a Lean theorem about the repository's constructive carrier** and not a
classical input to its proof.

For a bounded selfadjoint operator T, suppose a fixed test f satisfies

`|<x,f>|^2 <= C_f * ||T x||^2` for every x, with a finite `C_f >= 0`.

Then L(Tx)=<x,f> is well-defined: the bound makes the pairing zero on ker T.
It is bounded on Ran T, extends by continuity to its closure, and the
classical Hilbert-space representation theorem gives a vector y in that
closure such that <Tx,y>=<x,f> for all x. Selfadjointness yields Ty=f.
Conversely, an exact preimage f=Ty gives the displayed bound by
Cauchy--Schwarz with C_f=||y||^2.

Thus this bound asks for **actual range membership**, not just membership in
the closure of the range. The distinction is real: on real l2, T with diagonal
entries 1/n (n>=1) has dense range, because every finitely supported vector is
an image. The vector f_n=1/n lies in l2 but is not an image: its only coordinate
preimage would be the non-square-summable constant sequence. This elementary
example is a paper review example only; it is not the Lean fence below.

Consequence for planning: the C_f route may be useful if an actual source
identity produces it, but it must not become a mandatory requirement for all
collar tests. Approximate preimages with tolerance-dependent norms can suffice
for the existing time-zero consumer. No classical representation theorem is
being imported or used to choose a constructive preimage.

## 3. Constructive consumer calculation, conditional on missing data

This is an explicit paper composition of the source estimates in section 1;
the missing physical approximation data have **not** been supplied.

Given a supplied original Cauchy representative X and desired squared error
epsilon>0, ask for the following data, using only original objects:

1. `approximationData` computes p within epsilon/64 of point X.
2. The missing approximate-preimage construction returns Y with
   z=T2(point Y) within epsilon/64 of embedPresentation p.
3. `completedDist_two_segment` gives squared distance from z to point X
   at most epsilon/16. This declaration is at
   `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedApproximation.lean:72`.
4. `twoStepZeroContinuityCertificate Y (epsilon/16)` computes delta>0
   controlling the squared distance from A(t)z to z for 0<t<=delta.
5. `realTimeAction_distance_contraction` bounds the squared distance from
   A(t)(point X) to A(t)z by epsilon/16. The three-segment bound then gives
   squared distance from A(t)(point X) to point X at most epsilon.

Here A is the existing positive-real-time action, and
`oneTime_action`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicPositiveRangeZeroContinuity.lean:81`,
pins A(1) to the pre-existing T2. No uniform bound on ||Y|| is required by this
calculation: delta is computed after Y has been supplied. Geometric one-step
time identification and a physical Hamiltonian remain separate obligations.

For the existing candidate P_n, the missing quantitative task can instead be
stated as computing n from p and eta so that its exact residual moment is at
most eta. The original representative already comes from
`BF4ExactSlabThermodynamicRangeApproximation.approximationCertificate` cited
above. Its `kernel_residual_moment` at
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicRangeApproximation.lean:126`
shows why a possible kernel is a genuine obstruction: on such a vector the
residual moment remains its original squared norm for every n.

## 4. Lean-checked fence against an invalid limit inference

This is a rational two-coordinate counterexample, **not a Yang--Mills model,
not a physical transfer realization, and not a frontier-bundle inhabitant**.
Every declaration in this table is in
`lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean`.

| Declaration | Source | Checked statement |
| --- | --- | --- |
| `rate_positive` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:63` | r_n=(1/16)*2^(-n)>0 for every n. |
| `rate_le_gap` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:65` | r_n<=1/16 for every n. |
| `transfer_symmetric` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:79` | T_n=diag(1,r_n) is symmetric for the rational Euclidean pairing. |
| `transfer_coercive` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:85` | <x,T_n x> >= r_n*||x||^2. |
| `transfer_strictly_positive` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:95` | Positive squared norm implies a strictly positive finite-index form. |
| `vacuum_fixed` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:99` | Every T_n fixes (1,0), componentwise in rational setoid equality. |
| `uniform_excited_form_bound` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:103` | On (0,b), the form is at most (1/16)*||(0,b)||^2 for every n. |
| `operator_error` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:114` | ||T_n x-Px||^2 <= 2^(-n)*||x||^2 for P=diag(1,0). |
| `operatorErrorModulus`; `operator_error_atModulus` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:129`; same file `:132` | The computed modulus is epsilon.den; n beyond it gives squared error <=epsilon*||x||^2 for every rational vector x. |
| `limit_nonzero_kernel` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:139` | e=(0,1) has squared norm 1 and Pe=(0,0). |
| `limit_test_bound_impossible` | `lean/YMGap/Continuum/PositiveTransferLimitKernelFence.lean:141` | No rational C can give |<e,e>|^2<=C*||Pe||^2. |

The encoded estimates are on rational pairs; this module does not construct a
second Hilbert completion. Already at this elementary level, the disappearing
eigenvalue defeats the inference. The common **upper** excited-sector bound
does not furnish a lower spectral floor at zero. The actual T2 may or may not
have a kernel; no assertion in this example settles that physical question.

## 5. Finite-box literature and source mismatches

Luescher's finite-spatial-box construction factors its transfer kernel into
invertible dressing factors and a product of one-link convolution kernels.
Strictly positive representation coefficients establish strict positivity of
that convolution. The time-zero space has finitely many spatial links with
periodic boundary conditions. The subsequent reconstruction passes the
temporal extent M to infinity; this is not a proof of injectivity after the
spatial thermodynamic limit L->infinity. See equation (17), Proposition 1 and
its proof, and section II.C of
[Luescher, DESY 76/54](https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf).
This is a source for reviewing the required factorization, not an imported
theorem about the repository's different action and slab construction.

The inspected repository declarations do not yet supply that identification:

- `temporalInterface_haar_gram`,
  `lean/YMGap/Continuum/BF4ExactSlabAllExtentSpatialGramPositivity.lean:138`,
  is an actual arbitrary-spin interface Gram identity. It does not identify
  the thermodynamic T2 with a time-slice convolution and invertible dressing.
- `lowerHeat_image`,
  `lean/YMGap/Continuum/BF4ExactSlabGrowingChannelInterior.lean:80`, and
  `interiorLimit_selected`, same file `:121`, transport the source's lower
  interaction. The enlarged action has additional factors:
  `lowerHeat_dressing`,
  `lean/YMGap/Continuum/BF4ExactSlabGrowingChannelExterior.lean:78`.
  `responseLimit_pin`, same file `:142`, identifies the exact response;
  `responseCutoff`, same file `:147`, controls numerical precision at fixed
  source/target sizes, not decay with enlargement.
- `lowerCollar`,
  `lean/YMGap/Continuum/BF4ExactSlabBulkProbeInterface.lean:137`, uses only the
  faces incident to the probe links; `lowerCollar_length_le`, same file
  `:147`, bounds its length by 24. This local collar is not the whole spatial
  dressing in a time-slice transfer factorization.
- `correctedAmplitude_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabOriginalCollarCorrector.lean:119`, has the
  **same heat cutoff K** in its original test, spectator heat, correction
  and corrected integral. In contrast, `dressedTest` in the thermodynamic
  density module fixes its finite collar K while using the already
  cutoff-removed thermodynamic form. The density statement does not identify
  these two limiting procedures or turn a corrected finite amplitude into
  an actual T2 preimage.

## 6. Repointed next work, without changing a frontier type

First derive a same-action, same-normalization comparison tied to actual
time translation that makes original candidate residuals small on a dense
family, with a computable degree/tolerance rule. A local channel argument or
finite time-slice factorization is useful only if its estimates reach that
consumer through the actual volume limit. Preserve all exterior interactions
and distinguish action cutoff from test cutoff. If the comparison fails,
record that obstruction before extending its interface.

Do not add another preimage wrapper: the candidate, original representative
and residual moment already exist. Do not assume every dressed test is an
exact T2 image. Do not infer thermodynamic injectivity from finite positivity,
from scalar packet norm approximation, or from the existing upper gap.
No canonical field is weakened and no new analytic premise is introduced by
this review. Full-space time zero, physical Hamiltonian identification,
beta(a)/continuum control, the remaining QFT/spectral identifications, other
compact simple groups and the Clay theorem remain open.

## Verification boundary

Only the new rational fence was freshly compiled; the other modules were
read for this audit, not re-audited as a tree. Its 21 public def/theorem gates
match the clean focused output exactly: 11 axiom-free, the remainder within
{propext, Quot.sound}. No executable forbidden tokens, new hole, classical
input or noncomputable declaration. Only `autoImplicit false` is set.
The own artifact is fresh. Lake's narrow 40-job dependency target validates
content hashes; some unchanged dependency source mtimes are newer than their
cached artifacts, so blanket dependency-mtime freshness is not claimed.

The focused check used the safe-build skill, one worker and explicit 20 GiB.
One narrow dependency invocation accidentally inherited the existing 32 GiB
default, completed with only the new module built (330 ms), and was repeated
with explicit `--lake-worker-limit-gib 20`. No limits were edited. Separate
process/swap preflights found no competing compiler; swap stayed 12718.31 MiB.
No full build/audit/guard/progress run; the root import was statically checked,
not compiled. The focused log is `/tmp/ym-positive-transfer-limit-kernel-fence.log`,
SHA-256 `8c9ec6898eefebdc243a6bb11c6a55483f47ea6ef098d1dc86a9f55ad2e8d978`.

## Subsequent local boundary calculation (2026-09-15)

This addendum is exact polynomial Haar algebra, not a proof of the missing
thermodynamic comparison in section 1.

`four_pair`, `lean/YMGap/Continuum/SU2QuaternionHeadLinearHaar.lean:171`,
contracts four head coordinates with arbitrary retained polynomial
coefficients to their dot product times 1/4. Its concrete consumer
`path_schur`, `lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteGluing.lean:137`,
gives the fundamental conditional Schur identity with arbitrary outer paths.
No unit-quaternion or disjoint-support assumption on those paths is needed.

`shared_link_contraction`,
`lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteGluing.lean:194`,
identifies the integral over the common link s exactly:

`integral_s chi(a s c^-1 d^-1) chi(b e f^-1 s^-1)`
`= (1/2) chi(a b e f^-1 c^-1 d^-1)`.

`adjacent_boundary_haar`, same file `:237`, retains any polynomial in the
outer and spectator coordinates **independent of s**. It does not permit
dropping the other heat factors that depend on s. `selectedHeatFactor_pin`,
same file `:252`, gives the selected coefficient `2*w^6`; neither it nor the
Haar normalization factor is a full-action lower bound or a spectral rate.

The output is the explicit six-link `rectangle` (same file `:185`). No theorem
in these two modules says that this polynomial has an original
`PlaquetteExpression`, approximates such a state in the original OS norm, or
is an actual geometric transfer image. Nor do they prove its
nonrepresentability. This output-algebra check and retention of shared-link
action factors precede any use of the identity as a boundary-state comparison.
No canonical field or original observable algebra has been changed.

Verification for this addendum only: 13+9=22 exact focused public gates,
11 axiom-free and the rest within {propext, Quot.sound}; own/direct artifacts
fresh, clean final logs, no new holes/classical input/extra options. The
initial expanded coefficient calculation hit its 20 GiB kernel cap and was
replaced by a structural proof, with no limit increase. The safe-build skill
kept one worker and explicit 20 GiB throughout these focused checks. No
full-tree run; the two new root imports were checked statically, not compiled.
Exact final log hashes are recorded in the new work-plan entry.

## Exact pointwise recoding is now refuted on the original slab (2026-09-15)

The preceding addendum left rectangle representability open. The new result
answers the **exact pointwise/coefficient** question negatively. It does not
answer the completed-state or OS-norm approximation question.

All declarations in this section are in
`lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean`:

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `unitI`, `unitJ`, `field` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:44`, `:45`, `:51` | Explicit rational unit-norm configurations I,I versus I,J on consecutive corner x0 links; unit elsewhere. |
| `plaquette_scalar_equal` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:57` | Class coordinates agree for ALL elementary 4D plaquettes, by a structural six-plane proof. |
| `fieldEnvironment`; `fieldEnvironment_unit` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:97`; `:107` | The original corrected-slab coordinate decoder, with every block certified on S^3. |
| `original_lower_equal` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:251` | Every original `PlaquetteExpression`, under the existing `lower` evaluator, agrees on these two fields at every half-size and spin. |
| `rectanglePolynomial`; `rectangle_evaluation` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:270`; `:293` | The six-link rectangle on the SAME original extent-one slab has values -2 and 0. |
| `no_pointwise_plaquette_recoding` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:311` | No half-zero original expression represents the rectangle on all rational unit fields. |
| `no_polynomial_plaquette_recoding`; `no_coefficient_plaquette_recoding` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:324`; `:338` | Neither `RatPolyEqv` nor `RatPolyCoeffEqv` can give that recoding. |
| `no_coefficient_half_rectangle_recoding` | `lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:344` | The 1/2 Schur normalization does not fix the obstruction: rational scaling is already in the original algebra. |

**Planning consequence:** reject a universal exact coefficient compiler back
into the original plaquette-only algebra. The previous shared-link identity's
outer-loop output cannot simply be assumed to have such a recoding.

**Not proved:** almost-everywhere nonrepresentability, Haar-carrier inequality,
OS-norm non-density, absence of a completed-state realization, a nonzero actual
T2 kernel, or failure of the Yang--Mills route. Pointwise evaluations have not
been proved continuous in the original OS norm. The required next comparison
must address that norm and retain the shared-link-dependent action factors.
A larger observable algebra has not been installed, nor has a canonical type
or field been changed; any use of one needs an explicit original-carrier bridge.

Verification: 19 exact focused public gates, five axiom-free and the remainder
within {propext, Quot.sound}; own/direct-import artifacts fresh, clean final log,
no new holes/classical input/extra options. One missing holonomy dependency was
built with a narrow :olean target. Safe-build skill: one worker, explicit
20 GiB, separate process/swap checks. No full-tree build/audit/guard/progress
run; root import checked statically only. Final log:
`/tmp/ym-plaquette-character-nonseparation.log`, SHA-256
`84e92c60f5eaa46109d6738285e82d6d0243669bdc6ad3269c73e5881a7fbf1e`.

## Shared-link quadratic heat calculation, not an OS inverse (2026-09-15)

The whole-plaquette local identity already exists as `one_layer`,
`lean/YMGap/Continuum/SU2QuaternionFullHeatTubeLayer.lean:96`.
It requires the retained insertion to be independent of each of the four
integrated links. Thus multiplying known coordinate transmission formulas is
not a justified way to handle repeated occurrences of the same link. The new
calculation addresses that next polynomial degree directly, using the existing
`relativeHeat`, `lean/YMGap/Continuum/SU2QuaternionRelativeHeatTransmission.lean:37`.

Every declaration in the table is in
`lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean`.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `quadratic`; `quadratic_trace_decomposition` | `lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:61`; `:69` | The original coordinate product is its trace-free degree-two part plus the explicitly retained radius trace. |
| `low_spin_partial`; `high_spin_partial_zero` | `lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:83`; `:90` | Exact low-spin moments and annihilation of all higher solid characters, with polynomial tail coefficients retained. |
| `character_quadratic_boundary` | `lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:118` | For ordinary characters, only spin two survives, with coefficient 1/3, against every retained polynomial insertion. |
| `quadratic_heat_transmission` | `lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:183` | The SAME full relative heat packet transmits the quadratic by w^8 for every K>=2. Nome, cutoff guard and carrier are explicit. |
| `quadraticInverse`; `quadratic_inverse_transmission` | `lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:226`; `:231` | An explicit polynomial scaled by 1/w^8 for supplied w>0 is an exact relative-kernel preimage. This is not a geometric T1/T2 or OS-state preimage. |
| `cutoff_one_quadratic_zero`; `off_diagonal_haar_norm` | `lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:248`; `:269` | K=1 annihilates these modes, including a polynomial with ordinary Haar squared norm 1/24. |
| `heat_not_multiplicative` | `lean/YMGap/Continuum/SU2QuaternionQuadraticHeatTransmission.lean:276` | At w=1/2, K=2, integrating U_0 U_1 differs from multiplying the two known degree-one images, as tested by the same retained coordinate product. |

This removes the multiplicative-extension shortcut and a cutoff-independent
inverse shortcut. It does not introduce a new observable algebra or prove
that the local inverse is an admissible original test with a controlled OS
norm. The full shared-link action and that original-state comparison remain
necessary for this proposed route. An all-degree local inverse alone would
not establish those identifications or the continuum theorem.

Verification: 19 exact focused public gates, three axiom-free and the remainder
within {propext, Quot.sound}. Own/direct artifacts are fresh. No forbidden
executable tokens, extra options, holes or classical input. Safe-build skill:
one worker, explicit 20 GiB, separate process/swap preflights. One additive
root import was checked statically; root not compiled and no full-tree run.
Final log `/tmp/ym-quadratic-heat-transmission.log`, SHA-256
`d39ae2a89e20371de284c1929572d4c2bc5054ae8599ac0e7cd2b28fd5320048`.

## Auxiliary dual tests need not be original states (2026-09-15)

Source baseline: `87ea5eb`. This is a read-only source finding and a planning
correction, not a new Lean result. The preceding recoding obstruction must not
be expanded into a prohibition on using non-plaquette polynomials as auxiliary
dual tests. The following declarations already distinguish the two inputs.

| Declaration | Source | Actual scope |
| --- | --- | --- |
| `testAmplitude` | `lean/YMGap/Continuum/BF4ExactSlabPartialInterfaceTests.lean:45` | State input e is `PlaquetteExpression half`; test input q is arbitrary `RatPoly`. |
| `referenceEnergy`; `referenceEnergy_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabPartialInterfaceTests.lean:48`; `:51` | Nonnegative finite rational test energy on the retained interface; depends on w, K, half, retained choice and q. |
| `testAmplitude_bound` | `lean/YMGap/Continuum/BF4ExactSlabPartialInterfaceTests.lean:55` | A(q,e)^2 <= rawForm(e,e) * referenceEnergy(q), for w>=0 and K>=1. No original-expression representation of q is required. |
| `testAmplitude_add`; `testAmplitude_smul` | `lean/YMGap/Continuum/BF4ExactSlabPartialInterfaceTests.lean:63`; `:71` | Rational linearity in the ORIGINAL expression e. |
| `rawForm` | `lean/YMGap/Continuum/BF4ExactSlabPlaquetteFiniteGNS.lean:41` | The original full-action finite-cutoff numerator with upper(e)*lower(f), not the normalized thermodynamic form. |
| `testAmplitude_haar`; `referenceEnergy_haar` | `lean/YMGap/Continuum/BF4ExactSlabPartialInterfaceHaarForm.lean:156`; `:164` | Actual retained Haar pins require q supported on the slab and `LowerLocal`; neither type asks for plaquette recoding. The e insertion retains its original lower dressing. |
| `normalizedTolerance` | `lean/YMGap/Continuum/BF4ExactSlabNormalizedChannelReconstruction.lean:70` | Existing packet normalization divides tolerance by an explicitly volume-dependent original-partition reciprocal ceiling. It is not a volume-uniform bound for arbitrary q. |
| `normalizedSample`; `normalizedSample_approx_close` | `lean/YMGap/Continuum/BF4ExactSlabAllSpinSpectatorIntegralLimit.lean:102`; `:117` | Existing all-spin spectator integral samples use the original action reciprocal and converge to the existing finite-volume normalized retained packet. Not a thermodynamic arbitrary-q dual functional. |
| `completedCoefficient`; `completedCoefficient_norm_bound` | `lean/YMGap/Continuum/BF4ExactSlabIntrinsicChannelCompletion.lean:125`; `:194` | Original fixed-volume completed channel functionals and their intrinsic norm-floor bound already exist. This is not a new arbitrary-q or thermodynamic extension. |
| `completed_zero_of_coefficients_zero`; `completedCoefficients_injective` | `lean/YMGap/Continuum/BF4ExactSlabCompletedChannelSeparation.lean:144`; `:174` | These fixed-volume channels already separate the original completion; do not rebuild that result. |
| `norm_pin`; `twoStepTransfer_norm_interval` | `lean/YMGap/Continuum/BF4ExactSlabThermodynamicTranslatedChannelPacket.lean:45`; `:167` | The actual thermodynamic translated norm is pinned and numerically enclosed. No persistence or transfer-intertwining assertion for individual auxiliary test functionals. |

**Corrected instruction:** when claiming an original observable or transfer
preimage, prove its original realization or equality in the original OS
completion. When using q only as an auxiliary dual test, prove the relevant
original-norm bound and all required quotient/limit and time-translation
identifications; do not impose exact plaquette-expression recoding as an
extra premise. The finite bound above is a real available starting point,
not an identification of q with an original state or of a conditional local
heat inverse with the physical transfer inverse.

**NOT FOUND in the inspected modules:** a normalized thermodynamic extension
of this arbitrary-q test family with an explicit usable reference-energy bound
and a pin connecting it to the actual geometric T2 for the unshifted original
state. Searched `BF4ExactSlabPartialInterfaceTests`,
`BF4ExactSlabPartialInterfaceHaarForm`,
`BF4ExactSlabNormalizedChannelReconstruction`,
`BF4ExactSlabAllSpinSpectatorIntegralLimit`,
`BF4ExactSlabIntrinsicChannelCompletion`,
`BF4ExactSlabCompletedChannelSeparation`, and
`BF4ExactSlabThermodynamicTranslatedChannelPacket`, all under
`lean/YMGap/Continuum/`. A name search for `testAmplitude` and `referenceEnergy`
also returned no uses in `lean/YMGap/Continuum/BF4ExactSlabThermodynamic*.lean`;
that name search is not a proof that no differently formulated bridge exists.

This refines the task selection, not the canonical frontier: derive that
physical comparison for a suitable family, or obtain explicit approximate
original preimages directly. Section 2's stronger exact-range bound is not a
mandatory premise of every route. Existing candidate/residual and time-zero
consumers remain those in section 1. No abstract dual-to-range compiler was
added without a physical input to consume. Full-space time zero, geometric
T1/root identification, physical Hamiltonian, continuum/QFT/spectral pins,
other compact simple groups and the Clay target remain open.

Verification: source/type inspection and documentation diff checks only.
No `.lean` file or proof-status flag changed; no compiler, full build, audit,
guard or progress script was run. Historical checks above are not new checks.

## Implemented finite normalization and original null descent (2026-09-15)

Implementation after `a38acb4`, not a revision of the dated source findings
above. All declarations in the following table are in
`lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean`.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `background_partition` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:74` | Integral of full lower action, full spatial-Gram interface and full upper action equals the ORIGINAL raw unit diagonal. |
| `dress`; `backgroundCertificate` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:82`; `:98` | Auxiliary p is multiplied by the entire original lower action; ordinary positive-polynomial evidence for the full background is constructed under explicit small-nome guards. |
| `full_energy_haar` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:108` | Exact full-channel energy identity for supported lower-local p and its literal reflection image p'. No original-expression realization of p is required. |
| `reference_le_full`; `reference_partition_bound` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:135`; `:146` | Pruning followed by interval bounds gives referenceEnergy(dress p) <= (upperCap*lowerCap)*Z_original. |
| `partition_positive`; `normalizer`; `normalizer_partition` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:175`; `:180`; `:186` | Constructed positive rational reciprocal of the SAME finite partition, with exact cancellation. The supporting partition floor itself is volume-dependent. |
| `normalized_amplitude_bound` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:191` | (A/Z)^2 <= (upperCap*lowerCap)*(rawForm(e,e)/Z), with the ORIGINAL plaquette expression e unchanged. |
| `normalized_bulkScalar_bound`; `normalized_unit_pin` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:222`; `:236` | The existing spatial-coordinate product test has coefficient one at every slab/cutoff; the all-channel unit test evaluates to one. |
| `amplitude_null`; `amplitude_rad_congr` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:250`; `:262` | Arbitrary polynomial tests vanish on/respect the original finite-cutoff raw OS radical, using only w>=0 and K>=1. |
| `quotientAmplitude`; `quotientAmplitude_mk`; `quotient_unit_pin` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestBound.lean:274`; `:282`; `:288` | Normalized functional on EXISTING finiteGNSData.QuotSpace, with its original representative and unit pins. No new state algebra or choice of representatives. |

The normalization estimate assumes `0<=w<=1`, `heatRatio(w)<=1/2`,
`heatRemainderBound(w)<1`, `K>=1`, and the supplied constructive test interval
certificates. The existing nome 1/1024 satisfies the two extra heat guards by
`existingNome_guards`,
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeHaarComparison.lean:195`.
The resulting coefficient is exactly the product of test caps: it contains
no partition reciprocal or face-count factor. Its volume/cutoff uniformity
is conditional on uniform test caps; `normalized_bulkScalar_bound` supplies
those caps concretely. A conditional heat inverse may have growing caps, so
this theorem does not assert uniform bounds for all inverse families.

The proof does not convert an arbitrary auxiliary polynomial into an original
gauge-invariant observable. It bounds its energy directly on the certified
spatial-Gram background, then uses the original UNIT partition pin. The state
slot remains an original expression and its norm is the original raw OS norm.

**Still open:** the cutoff/volume compatibility and actual time-translation
comparison identified in the preceding addendum. `quotientAmplitude` has a
finite-cutoff domain; it is not a functional on the cutoff-removed finite-volume
or thermodynamic completion. Uniform boundedness alone is not convergence,
does not remove a thermodynamic kernel, and does not provide a time-preimage.
No canonical field or mathematical target changed.

Verification: 23 exactly matched public gates, all within {propext, Quot.sound};
clean focused log and fresh own/direct artifacts. No executable forbidden tokens
or raised options; initial syntax/scoping and reflection-multiplication dispatch
errors were corrected. Safe-build skill: one worker, explicit 20 GiB and fresh
process/swap preflights. One additive root import, old multiplicities preserved;
root not compiled. No full build/audit/guard/progress run. Log
`/tmp/ym-dressed-dual-test-bound.log`, SHA-256
`ed58b1463adcac8f380114b4f19733bd68619aeed0fcc9d173df58900d053621`.

## Implemented full-channel cutoff removal (2026-09-15)

Implementation after `82518a0`; the preceding dated findings are preserved.
All source references below are to
`lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean`.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `bulkScalar_temporal_fixed` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:90` | The existing temporal ledger fixes the concrete lower-link scalar product. |
| `original_numerator_spatialGram`; `full_amplitude_original` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:114`; `:148` | For a supported lower-local, temporally fixed auxiliary test, the full-channel amplitude equals the ORIGINAL numerator with fixed insertion upper(e)*p. No crossing channel or bulk factor is dropped. |
| `rawTestLimit`; `testCutoff`; `full_amplitude_approx_close` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:174`; `:178`; `:183` | Existing numerator limit plus computed all-later cutoff and representative thresholds; all action cutoffs vary together. |
| `rawTestLimit_bound`; `testLimit_bound`; `bulkScalar_limit_bound` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:234`; `:306`; `:325` | The cap survives cutoff removal and exact original normalization; the concrete scalar test has coefficient one in the ORIGINAL cutoff-removed OS norm under explicit small-nome guards. |
| `testLimit`; `testLimitCauchy` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:274`; `:277` | The normalized value is the pre-existing original expectation, with its explicit Cauchy modulus. |
| `bulkScalar_limit_null`; `bulkScalar_null_congr`; `bulkScalarQuotientTest`; `bulkScalarQuotientTest_embed` | `lean/YMGap/Continuum/BF4ExactSlabDressedDualTestCutoffLimit.lean:379`; `:386`; `:393`; `:397` | Concrete test descends to the EXISTING cutoff-removed finite-volume null quotient, with its original representative pin. |

This closes cutoff removal for the displayed full-channel family, not for
every partial selection or cutoff-dependent inverse. The general identity
retains an explicit algebraic temporal-image hypothesis; the concrete scalar
test supplies it. The convergence modulus remains volume-dependent even though
the concrete normalized size bound has coefficient one. No new limiting law,
original-state realization of p, or pointwise recoding theorem is asserted.

**Still open:** volume-compatible auxiliary tests, their completed extension
and actual geometric time comparison; no T2 range estimate or excited nonzero
witness follows from this module. The thermodynamic, Hamiltonian, continuum,
other-group and Clay obligations remain unchanged.

Verification: 20 exactly matched public gates within {propext, Quot.sound},
one monitored worker, explicit 20 GiB. No full-tree check. Log
`/tmp/ym-dressed-dual-test-cutoff-limit.log`, SHA-256
`049bdccc7eed1a7a81b4cf64bc7902bcdd47e51979c1da702c86a6d25400c65e`.

## Implemented concrete scalar-test volume limit (2026-09-15)

Implementation after `29a0da9`; earlier dated findings are preserved. All
declarations below belong to
`lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean`.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `probeLinks_shift` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:74` | The actual four-link test support is translated by the same bulk placement as the state. |
| `bulkScalar_image` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:90` | Exact prefix-polynomial image of the scalar product under every original inter-slab embedding. |
| `insertionInterval` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:101` | The mixed upper-state/lower-test insertion has the upper expression's interval cap, since the scalar product has cap one. |
| `insertion_local` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:109` | Both factors lie in the same translated fixed source box. |
| `insertion_image` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:121` | The complete mixed insertion follows the original inter-volume map; it is not a changing unrelated observable. |
| `mean_difference_bound` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:147` | Original normalized expectations differ by at most A(w,base,e) times the existing rate to power margin+1-boxSize(base), uniformly in further padding under the explicit coupling guards. |
| `volumeModulus` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:188` | Reuses the existing upper-expression volume modulus at nome 1/1024. |
| `meanLimit` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:229` | Constructs the CReal volume limit from the original expectation sequence and explicit inner/outer moduli. |
| `meanLimitCauchy` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:237` | Returns numerical Cauchy data for that particular limit representative. |
| `meanLimit_geometric_bound` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:245` | The original geometric boundary estimate also controls the error from each finite volume to this limit. |
| `meanLimit_bound` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:263` | L(e)^2 <= formLimit(e,e), the EXISTING thermodynamic reflected OS norm. |
| `meanLimit_add` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:273` | Additivity on original expressions at each source base. |
| `meanLimit_smul` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarThermodynamicTest.lean:280` | Signed rational linearity on those expressions. |

The boundary estimate uses the same original action and partition cancellation;
the test was not made an original plaquette expression. The concrete limit is
constructed only at the existing nome. Its cap-one norm bound does not assert
coupling-uniform volume convergence or a beta/spacing-uniform spectral gap.
The cutoff modulus remains the existing volume-dependent one; the new outer
modulus controls the subsequent volume passage for a fixed source expression.

**Still open:** descent under original presentation equivalence and the
thermodynamic OS null relation, completed extension, and an identity/estimate
involving the ACTUAL geometric time operator. The new norm estimate concerns
e, not T2(e). No separating family, excited nonzero witness or residual
smallness threshold is supplied. Thus this construction does not yet discharge
the range/time-zero consumer in section 1. No canonical frontier was changed.

Verification: 25 exactly matched public gates within {propext, Quot.sound};
clean final log, fresh own and two direct-import artifacts. No executable
forbidden tokens or raised options. Initial notation, unfolding and namespace
errors were corrected without weakening the mathematical statements. The
safe-build skill kept one worker, explicit 20 GiB and separate process/swap
preflights; swap stayed 12389.81 MiB. One additive root import, not compiled.
No full build/audit/guard/progress run. Log
`/tmp/ym-bulk-scalar-thermodynamic-test.log`, SHA-256
`f986f380298bce830ec5f549fb23373d8232cf30283cac5d726b447945a05088`.

## Implemented original quotient descent and completed scalar test (2026-09-15)

Implementation after `41c057e`; the earlier dated findings are preserved.
The existing scalar test now acts on the existing thermodynamic completion.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `finite_lower_congr` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarQuotientTest.lean:43` | Equality of lower original Haar-carrier observables preserves the finite scalar test, by existing form congruence and OS-null descent. No new upper reflection recoding. |
| `meanLimit_same` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarQuotientTest.lean:78` | Common-volume comparison makes the test limit independent of the existing state-independent presentation equivalence. |
| `observableTest` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarQuotientTest.lean:95` | Constructed functional on the EXISTING semantic observable quotient. |
| `observableTest_null` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarQuotientTest.lean:168` | Original thermodynamic OS-null differences have equal test values. |
| `osTest` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarQuotientTest.lean:179` | Constructed functional on the EXISTING thermodynamic OS quotient. |
| `testTolerance` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarQuotientTest.lean:195` | The explicit squared-distance budget is epsilon^2/2. |
| `presentedTest_close` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarQuotientTest.lean:200` | That original-distance budget gives the two signed scalar bounds at epsilon. |
| `testRate` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:48` | Computed antitone closure of the supplied original Cauchy modulus at the scalar tolerance. |
| `representativeTest` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:61` | Actual diagonal CReal limit of the previously constructed test values on a supplied original Cauchy sequence. |
| `representativeTestCauchy` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:78` | Numerical Cauchy data for that particular representative. |
| `representativeTest_welldef` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:91` | Explicit original Cauchy closeness gives equal scalar limits. |
| `completedTest` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:106` | A scalar functional on the EXISTING original thermodynamic completion, without representative selection. |
| `completedTestRepresentative` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:113` | Supplied Cauchy data return a real representative, numerical modulus and quotient-value pin. |
| `completedTest_embedPresentation` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:118` | Exact agreement with the original presented test. |
| `completedTest_embedOSQuotient` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:128` | Exact agreement with the original OS-quotient test. |
| `completedTest_bound` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:140` | L(x)^2 <= completedInner(x,x), for the original completed form. |
| `completedTest_add` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:145` | Additivity for the existing completed operation. |
| `completedTest_smul` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:154` | Rational linearity for the existing completed operation. |
| `completedTest_distance_bound` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarCompletedTest.lean:173` | (L(x)-L(y))^2 <= completedDist(x,y), with coefficient one and the original squared distance. |

This closes presentation compatibility, thermodynamic OS-null descent and
completed extension for this particular test at nome 1/1024. The construction
does not select a Hilbert-space representing vector, enlarge the original
observable algebra or assert a value on any nonzero excited state.

**Still open:** a full-action identity or estimate connecting a sufficiently
rich test family to ACTUAL geometric time, or direct approximate original
preimages. Neither new module asserts separation by this single functional
or the missing unshifted-to-translated bound. The norm on the right is still
the norm of x, not T2(x). Therefore the actual-transfer range/time-zero
consumer in section 1 is not discharged. Physical Hamiltonian, continuum,
other-group and Clay obligations remain open; no canonical field changed.

Verification: 23 + 26 exact focused public gates within {propext, Quot.sound};
one axiom-free and one propext-only. Own/direct artifacts fresh; final logs
clean. Explicit presentation arguments, a displayed quotient pin and a
generic diagonal-Cauchy helper resolved elaboration timeouts without changing
the statements or increasing limits. Safe-build skill: one worker, explicit
20 GiB, separate process/swap preflights; swap stayed 12389.81 MiB. Two
additive root imports, old multiplicities preserved; root not compiled.
No full build/audit/guard/progress run. Logs and SHA-256:

- `/tmp/ym-bulk-scalar-quotient-test.log`:
  `9baf4125f5e4c6b77e1aa00e04eb51164f565c8c514bc1e9fa792215638d96f9`.
- `/tmp/ym-bulk-scalar-completed-test.log`:
  `2baf8dfb5223669d7276f3cb7338d00842b35a5e4b965a688b1836cd32eaff04`.

## Implemented local vertex-gauge average of the original scalar test (2026-09-15)

Implementation after `646d14d`. This identifies the local gauge average,
not yet the original interacting expectation or completed functional.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `scalar_schur` | `lean/YMGap/Continuum/SU2QuaternionAdjacentPlaquetteGluing.lean:106` | Existing normalized scalar Schur factor 1/4, now public; original proof unchanged. Retained path polynomials need neither unit norm nor mutually disjoint support. |
| `threeGauges_average` | `lean/YMGap/Continuum/SU2QuaternionScalarVertexGaugeAverage.lean:97` | Three auxiliary integrations give 1/64 times the ordered scalar path product, with original variables unintegrated. |
| `gaugedScalarProduct` | `lean/YMGap/Continuum/SU2QuaternionScalarVertexGaugeAverage.lean:120` | Literal three-vertex-gauged scalar product; base gauge fixed to one, auxiliary blocks 0,1,2. |
| `orientedScalarProduct_pin` | `lean/YMGap/Continuum/SU2QuaternionScalarVertexGaugeAverage.lean:133` | Endpoint ordering and conjugate reversal match that literal product, without commuting quaternion factors. |
| `characterFraction` | `lean/YMGap/Continuum/SU2QuaternionScalarVertexGaugeAverage.lean:151` | Explicit rational 1/128, independent of coupling/spacing; an algebraic coefficient, not a gap or decay rate. |
| `gaugedScalarProduct_average_with_tail` | `lean/YMGap/Continuum/SU2QuaternionScalarVertexGaugeAverage.lean:181` | The local average is 1/128 times the plaquette character with every supplied original-link insertion retained. Only auxiliary-gauge independence is encoded by `liftBoundary 3`. |
| `bulkScalar_product_pin` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarGaugeAverage.lean:57` | Existing `bulkScalar` uses the same four original links; source list A,D,C,B is reordered only at the scalar level. |
| `bulkProbe_word_pin` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarGaugeAverage.lean:65` | The ordered character equals the existing original lower plaquette expression. |
| `bulkScalarVertexImage` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarGaugeAverage.lean:77` | Literal local gauge image using the actual corrected-slab link polynomials. No global substitution is asserted. |
| `bulkScalar_vertex_average` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarGaugeAverage.lean:81` | Its three-gauge average is 1/128 of `lower (bulkProbe half)` at every half-size. |
| `bulkScalar_vertex_average_with_tail` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarGaugeAverage.lean:88` | The same original-probe identity retains arbitrary dependence on all original links. |

**Still open:** realizing this local image by a common Haar-preserving change
of variables on all affected original links, including every action factor
and the original plaquette-observable insertion. Ordered plaquette-character
gauge invariance is supplied by `plaquette_gauge_character`,
`lean/YMGap/Continuum/SU2QuaternionHaarGaugeCancellation.lean:139`; that
declaration alone is not the simultaneous original-slab change of variables.
The existing `applyTemporalTranslationLedger_haar`,
`lean/YMGap/Continuum/BF4ExactSlabTemporalGaugeLedger.lean:135`, preserves
Haar for a different, explicitly temporal link assignment. No equality of
that assignment with this three-vertex image is supplied here.

Only after the full-action identity and its original limit pins are proved
may the completed scalar functional be identified with the plaquette pairing.
There is no new separating-family or actual-transfer comparison theorem in
these modules. The range/time-zero consumer in section 1 remains open; no
canonical frontier or constructive assumption changed.

Verification: 13 + 15 + 5 exact focused public gates within {propext,
Quot.sound}, including 12 axiom-free and one propext-only. One monitored
worker, explicit 20 GiB and separate process/swap preflights. Own/direct
artifacts fresh; clean final logs, executable-token and option checks.
The original A,D,C,B enumeration required explicit scalar reordering; no
quaternion ordering or theorem statement was weakened. Two additive root
imports, not compiled. No full build/audit/guard/progress run. Exact logs
and hashes are recorded in the current work_plan increment.

## Implemented common all-link Haar change and literal scalar image (2026-09-15)

Implementation after `7256911`. This closes the global coordinate/Haar and
scalar-source parts of the preceding local-average residue. It does not yet
assemble the full original-action expectation identity or its completed limit.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `endpointSteps` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryVertexGaugeLedger.lean:46` | Computed left/right link translation with a distinct auxiliary gauge multiplier; original blocks begin at 3. |
| `steps_fix_gauge` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryVertexGaugeLedger.lean:82` | Every chain selecting only original links fixes the auxiliary gauges. |
| `batches_image` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryVertexGaugeLedger.lean:174` | A duplicate-free batch list sends each contained link to its whole endpoint word; other batches preserve that word. |
| `gaugeLedger` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryVertexGaugeLedger.lean:210` | Explicit batch list over every original link index. |
| `gaugeQuaternion_link` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryVertexGaugeLedger.lean:220` | The simultaneous global coordinate image is g_start^-1 U_i g_finish, with common carrier padding. |
| `gaugePolynomial_haar` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryVertexGaugeLedger.lean:238` | The WHOLE supported product-Haar integral is preserved at arbitrary polynomial degree. |
| `liftThree_coordinate` | `lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:65` | The existing triple lift is exactly coordinate-block offset +3. |
| `slabGauge_link` | `lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:93` | Same-vertex endpoint image on every member of the original corrected-slab link list. |
| `slabGauge_haar` | `lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:106` | Global Haar invariance for the physical common vertex assignment and any supported integrand. |
| `slabGauge_face_word` | `lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:121` | Ordered image of each physical lifted plaquette word. |
| `vertexFace_character` | `lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:156` | Every spin character is unchanged by the common endpoint gauges as a Haar-carrier equality under arbitrary insertions. |
| `probeTags` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarVertexImage.lean:83` | Explicit assignment of the three auxiliary gauges to the actual non-base probe corners. |
| `bulkScalar_global_vertex_image` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarVertexImage.lean:148` | The global ledger's image of the EXISTING lifted `bulkScalar` is precisely the EXISTING local `bulkScalarVertexImage`. |

The scalar image's existing consumer is `bulkScalar_vertex_average_with_tail`,
`lean/YMGap/Continuum/BF4ExactSlabBulkScalarGaugeAverage.lean:88`. The common
assignment, not the older temporal assignment, now supplies its scalar image.
However, character-polynomial substitution, the full action and original
observable insertion still require their combined image/support argument,
auxiliary integration and original normalization/limit pins. The local image
and global Haar identity are not yet a proved interacting expectation identity.

No equality of the existing `completedTest` with a plaquette pairing is claimed.
No new separating-family, actual-transfer range or full-space time-zero theorem
is supplied. No canonical frontier, new analytic assumption or hole changed.

Verification: 16 + 16 + 2 exact public gates within {propext, Quot.sound},
including four axiom-free and five propext-only. One monitored worker, explicit
20 GiB, separate process/swap preflights, fresh own/direct artifacts and clean
final logs. An axiom-gate failure in broad simplification of the vertex tags
was repaired constructively; explicit polynomial arguments removed an inference
timeout. No limits were raised. Three additive root imports, not compiled.
No full build/audit/guard/progress run. Exact logs and SHA-256 are in work_plan.

## Implemented full interacting identity through the ORIGINAL completion (2026-09-15)

Implementation after `b0f695b`. The preceding common-ledger/local-average
residue is now composed through the original completed scalar functional.

| Declaration | Source | Actual statement |
| --- | --- | --- |
| `lift_supported` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryLiftAlgebra.lean:73` | Adjoining n gauges retains every original coordinate and gives the explicit carrier size blocks+n. |
| `SupportedHaarEqv` | `lean/YMGap/Continuum/SU2QuaternionAuxiliaryLiftAlgebra.lean:119` | Only insertions supported on the stated carrier are admitted when using padded equality. No unsupported variables are erased. |
| `Invariant` | `lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:60` | Original polynomial support and equality of its actual lifted ledger image under supported insertions. Proved for the physical consumers below; no analytic premise. |
| `character_invariant` | `lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:208` | Every original physical plaquette character, at every spin, under the SAME common vertex assignment. |
| `heatProduct_invariant` | `lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:234` | The existing heat polynomial product over a supplied list of original physical face IDs; all coefficients and cutoff K retained. |
| `fullActionInsertion_invariant` | `lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:260` | The complete original physical face list multiplied by the original upper observable, including neighboring factors sharing probe links. |
| `bulkScalarVertexImage_supported` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarInteractingIdentity.lean:100` | The previously computed literal scalar image belongs to the augmented original carrier. |
| `bulkScalar_invariant_tail` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarInteractingIdentity.lean:112` | Full Haar substitution followed by three normalized auxiliary integrations; any proved invariant original tail is retained. |
| `scalar_numerator_eq_plaquette` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarInteractingIdentity.lean:146` | EXISTING original scalar numerator equals the EXISTING plaquette-pairing numerator /128, for all rational w, K, half-size and original expressions. |
| `scalar_numeratorLimit_eq_plaquette` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarInteractingIdentity.lean:167` | The existing cutoff limits, with their previous moduli and 0<w<1 guards, satisfy the same scaled identity. |
| `scalar_expectation_eq_plaquette` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarInteractingIdentity.lean:183` | Normalized cutoff-removed identity using exactly the same original partition reciprocal. |
| `testAt_eq_plaquette` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean:60` | Same common-volume test and original reflected pairing at the existing nome. |
| `meanLimit_eq_presented_pairing` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean:68` | Existing thermodynamic scalar limit is the common-presentation original pairing /128. |
| `representativeTest_eq_pairing` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean:78` | The same identity on every supplied original Cauchy representative, using the existing limits. |
| `completedTest_eq_pairing` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean:86` | EXISTING completed functional equals EXISTING completed pairing with the original plaquette /128. |
| `representingState` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean:94` | Explicit rational scaling of the original embedded probe; no representation theorem or selected representative. |
| `completedTest_represented` | `lean/YMGap/Continuum/BF4ExactSlabBulkScalarPlaquettePairing.lean:96` | `completedTest x = completedInner x representingState`. |

Scope: the finite identity has arbitrary rational coupling and cutoff; the
cutoff limit has the explicit 0<w<1 guards. The thermodynamic/completed pins
use the existing SU(2) nome 1/1024 at fixed spacing. The coefficient 1/128 is
an algebraic Schur factor, not a uniform-in-beta contraction or mass estimate.

**Causal consequence:** this scalar test is exactly an already-present
plaquette pairing. Its representation does not add a new separating family
or a backward-time preimage. The next actual consumer remains
`partialPreimage_distance`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicRangeApproximation.lean:89`:
the original candidate's squared approximation error is `mixedMoment x 0 (n+n)`.
The computed small-error index for arbitrary unshifted dense states remains
unsupplied by this increment. `oneStep_residual_weighted`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicGeometricRangeContinuity.lean:95`,
has an actual geometric T1 input, not an arbitrary unshifted state. The new
scalar identity does not remove that restriction. No canonical frontier,
analytic hypothesis, hole, physical Hamiltonian or continuum/Clay claim changed.

Verification: 17 + 17 + 5 + 6 exact public gates within {propext, Quot.sound},
including one axiom-free and two propext-only. Four focused monitored checks,
one worker, explicit 20 GiB and separate process/swap preflights; swap decreased.
Generic ordered-word algebra and explicit CReal equalities resolved elaboration
timeouts without raising limits. Clean final logs and fresh own/direct artifacts.
Four additive root imports, not compiled; no full build/audit/guard/progress run.
Exact logs and SHA-256 are in the latest work_plan increment.
