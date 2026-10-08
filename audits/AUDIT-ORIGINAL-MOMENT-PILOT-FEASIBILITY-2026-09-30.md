# Original six-moment pilot: quantitative feasibility screen

Initial source review, exact scalar arithmetic and a small geometry diagnostic.
That feasibility screen involved no Lean edits or theorem checks, and no
Haar moment or auxiliary-state margin was evaluated. Subsequent scalar
proof work is recorded separately in
`AUDIT-ORIGINAL-CHEBYSHEV-SQRT-RATE-2026-09-30.md`. The early-cutoff ORIGINAL
Haar positivity join checked on 2026-10-08 is recorded below; the old canonical
cutoff is not a necessary positivity threshold. No charged moment is produced.
The scaling estimate
and same-theory continuum/Clay target remain open.

## Why this check changes the next action

The direct comparison needs six original raw moments, not six inexpensive
numbers. The existing all-nome canonical positivity cutoff is already at
least 627 at nome 1/2. A Cartesian spin-assignment expansion on even a
24-face core would therefore enumerate at least 628^24 assignments.
Do not launch that expansion. This does NOT exclude compressed integration,
alternative proved positivity cutoffs, or an analytic estimate.

The existing test is not being rebuilt. Its declarations are
`marginValue` and `reverse_energy_of_finite_test`,
`lean/YMGap/Continuum/BF4ExactSlabChebyshevFiniteTest.lean:79` and `:115`.
The weaker direct diagnostic follows algebraically from
`finite_covariance_cleared`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:176`:
with `D(p,q)=Z*M(p*q)-M(p)*M(q)`, test
`D(p,q)^2 <= r^2*D(p,p)*D(q,q)` on the SAME action.
Success for one pair does not prove reverse energy, all-observable control,
or a parameter-uniform estimate.

## The canonical cutoff lower bound

Write `L=headFloor(w)`, `U=prefixCap(w)`, `Q=w*w`. Existing results give
`0<L<=1/32` and `U>=1`:

- `headFloor_positive`,
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:52`;
- `headFloor_le_oneThirtySecond`,
  `lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`;
- `prefixCap_ge_one`,
  `lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`.

The actual definitions, in ordinary rational-value notation, are

```
epsilon = weightTolerance(w,L) = L / (2*(U+1)) <= 1/128
A       = lossScale(Q)         = 2 / (1-Q)
delta   = lossTolerance(Q,epsilon) = epsilon / (A+1)
```

Sources: `weightTolerance`,
`lean/YMGap/Continuum/BF4ExactSlabJacobiDeficitInterval.lean:51`;
`lossScale`, `lossTolerance`, and `lossCutoff`,
`lean/YMGap/Continuum/FiniteJacobiWeightConvergence.lean:36`, `:42`, `:60`.

`powBaseCutoff` takes the positive numerator of the rational
`1/((1-Q)*delta)`, not a logarithmic cutoff:
`lean/YMGap/Continuum/HeatKernelConvGen.lean:266`.
The quotient convention is `HKConv.divPos`,
`lean/YMGap/Continuum/HeatKernelConv.lean:126`, with denominator identity
`divPos_den_cast` at `:136`. Since a structural rational denominator is at
least one, this numerator is at least its rational value. Consequently

```
lossCutoff >= 128*(2/(1-Q)+1)/(1-Q).
w=1/2: Q=1/4, so lossCutoff >= 5632/9, hence lossCutoff >= 626.
headCutoff = bandSize + lossCutoff >= 1+626 = 627.
```

The last equality uses `bandSize` and `deficitCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabJacobiDeficitInterval.lean:49`, `:69`;
`centeredCutoff`,
`lean/YMGap/Continuum/FiniteJacobiWeightConvergence.lean:88`;
and `headCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55`.
Main and Sol independently checked this derivation against source. Tiny
Python `Fraction` arithmetic checked 5632/9 and the integer ceiling. This
derived lower bound is not recorded as a new Lean theorem. Unreduced
rational representations can make the actual cutoff larger still.

## Small geometry diagnostic, not a reduced-action theorem

`boundaryCompleteSlabPlaquettes`,
`lean/YMGap/Continuum/Z4HalfTimeReflectionGeometry.lean:169`, retains
3(E+1)^4 spatial and 3E(E+1)^3 temporal faces. The existing executable
mirror is `boundary_complete_slab_plaquettes`,
`computations/dual_half_time_reflection_route.py:122`.
Luna inspected the definitions; main ran a bounded E=0,1,2,3 diagnostic
using this mirror and `edges_of` from
`computations/dual_positivity_geometry_bridge.py:57`.

The diagnostic repeatedly removes a face with a link incident to exactly
one remaining face. It handles finite incidence sets only: no characters,
heat polynomials, Haar contractions, representation sums or compiler.

| E | Full faces | Full links | Full vertices | Removed faces | Remaining faces | Remaining links |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 3 | 9 | 7 | 3 | 0 | 0 |
| 1 | 72 | 116 | 52 | 48 | 24 | 32 |
| 2 | 405 | 513 | 189 | 189 | 216 | 216 |
| 3 | 1344 | 1488 | 496 | 480 | 864 | 768 |

Extent zero has no temporal face. Extent one is NOT literally a 24-face
action; its 24-face remainder is the output of this graph diagnostic.
No equality of the original six moments with reduced moments was proved.
Such an equality must check that the observables avoid each removed link.
The existing fixed-spatial result `spatialWeight_haar_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSpatialWeight.lean:130`,
is a precedent with explicit independence hypotheses, not a pin for this
whole-slab diagnostic.

Even assuming that reduction is supplied, the naive 24-face label expansion
at K>=627 has at least

```
628^24 = 14158963092163953508691265632276558109170103555323872424556658425856
```

candidate assignments BEFORE admissibility and contraction. This is not a
lower bound on the runtime of every possible algorithm. No large run was
started and no successful six-moment instance is claimed.

## Targeted literature screen: finite groups are not compact SU(2)

Adhikari--Cao, [Correlation decay for finite lattice gauge theories at weak
coupling](https://arxiv.org/html/2202.10375v3), Theorem 1.1, treats finite
groups with a Wilson exponential action. Section 3 uses a weight-preserving
two-copy swapping map; Section 6 bounds the failure event. The decay uses
the positive nonidentity character defect Delta_G from Section 1.3 and
constants involving the finite group cardinality. This supplies no bound
for the repository's compact SU(2) heat action. No theorem was imported.

Our elementary obstruction to transplanting that defect assumption is
constructive: the rational unit quaternions
`q_N=((N^2-1)/(N^2+1), 2*N/(N^2+1), 0, 0)`, N>=1, are nonidentity and
have fundamental trace defect `2-2*(q_N).scalar=4/(N^2+1)`.
For epsilon=a/b>0, N=4*b+1 makes the defect smaller than epsilon.
Thus there is no positive uniform defect away from the identity on this
rational SU(2) subcarrier. This argument is not a mass-gap counterexample
and has not been formalized here. The paper's swapping idea alone does not
provide a compact-group replacement for its probability estimate.

The cached general math-ph listing was reused, not refreshed. This was a
targeted primary-source scope check. Next work remains the useful averaged
signed estimate on the original action, or a genuinely bounded compressed
calculation with its same-action pin; no further conditional compiler is
warranted by the present screen.

## Exact compression ingredients and their boundary (2026-10-08 UTC)

Independent read-only review and root source verification. No Lean edit,
compiler run or original moment evaluation. A Cartesian assignment list is
NOT mandatory, but no feasible arbitrary-cutoff evaluator is certified here.

Exact local bucket elimination has genuine existing inputs:
`lean/YMGap/Continuum/SU2QuaternionHaarBlockConditionalAlgebra.lean:64`,
`project_mul_of_independent`, and `:79`, `project_mul_right_of_independent`,
pull ONLY link-independent factors through a selected Haar projection.
`lean/YMGap/Continuum/SU2QuaternionHaarBlockProjection.lean:132`,
`project_comm`, gives coefficientwise commutation; `:204`, `project_mean`,
preserves the original Haar functional.
`lean/YMGap/Continuum/SU2QuaternionSparseCoefficientCollector.lean:126`,
`collect_coeff`, permits exact coalescing after each local elimination.
Integrating a bucket can nevertheless couple its entire remaining boundary;
these equalities give no intermediate-size bound.

The actual two-link reduction
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkFeatureMoments.lean:102`,
`full_marginal_feature_pin`, retains exterior `neitherHeat` exactly once.
Its feature index is the expanded shared polynomial, not a proved small
rank. The arbitrary-spin original ordered-word input exists:
`lean/YMGap/Continuum/BF4ExactSlabSymmetricPowerHaarTrace.lean:134`,
`slabPlaquette_trace_haar_character`. In contrast,
`lean/YMGap/Continuum/SU2QuaternionCutoffOneLinkBucketHaarNetwork.lean:336`,
`finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_linkBucketKernelProduct`,
handles cutoff ONE and named environments. Expanding each spin n<=K into
fundamental occurrences permits up to 6K occurrences per bare physical
link, plus insertions; the six-occurrence dispatcher does not cover it.
This is a scope comparison, not a new proved occurrence/runtime bound.

Already-collected chronological iteration
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCollectedFamilyMargin.lean:68`,
`iterate`, evaluates `step` before collection. Its stored output bounds,
from `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyJointDegree.lean:109`,
`terminalMessage_degree`, and `:314`, `margin_numerators_monomials`, are
not bounds on those intermediate products or their evaluation cost.

Missing in these inspected modules: an ORIGINAL action factor-list/tensor
evaluator with a partial-integration invariant, together with a verified
contraction order and adequate intermediate/separator-size bound. Both
endpoint messages, OWN centers, distinct masses and signed insertions must
pass through that SAME evaluator. No large pilot is selected without those
bounds. A frozen vacuum-plus-fundamental algebra cannot repair closure:
`lean/YMGap/Continuum/SU2PeterWeylPlaquetteAlgebraClosureFence.lean:134`,
`no_fiveCoordinate_classCompatible_product`, and `:158`,
`fundamental_square_exposes_spinTwo`, explicitly expose the missing channel.
None of this produces a favorable relative estimate or scaling theorem.

## Selected early-cutoff ORIGINAL Haar positivity join (2026-10-08 UTC)

The canonical K>=627 lower bound at w=1/2 above is a bound on that particular
computed schedule, not a necessary threshold for positivity. Existing
`SU2AllLabelPointwiseHeatCorridor.pointwiseHeatMajorant_tail_le` proves the
entire label>=2 scalar majorant tail <=81/2272 for 0<=w<=1/2. The first
nonconstant label has cap <=1/2. Their sum is <=1217/2272<1, leaving the
explicit floor 1055/2272 for every inclusive prefix K>=1. The scalar
pointwise floor is already proved; do NOT count its reexport as new work.

Selected proposition: construct a `QuaternionHaarSquareCertificate.Certificate`
for the ORIGINAL `heatPrefix w K x -1055/2272`, using the actual
`SquareBound blocks x 1` and existing sharp `termInterval`, finite polynomial
sum and interval operations. Consumer: positivity of the same finite original
heat factors under arbitrary Haar insertions, enabling early-cutoff raw
moment diagnostics without a Cartesian expansion at the canonical cutoff.
No such diagnostic or favourable interacting moment is claimed yet. Do not
change `headCutoff`, weaken its consumers, change the action or infer a Haar
certificate solely from scalar pointwise positivity.

Prediction: a short positive-character-tail certificate pays this join with
no new analytic hypothesis. Test cutoff one, zero nome, shared-link factors
and all later prefix lengths. Budget: one bounded Sol leaf, independent
complete-source review, root-only serialized focused 20-GiB verification with
12-GiB reserve and fresh capacity preflight. Stop if the construction needs
pointwise-to-Haar inference, spectator independence or a changed law. Global
normalized cutoff errors, feasible contraction order, actual signed moments,
changing-family retention and the whole Clay target remain OPEN. Selection
is not a checked result and changes no canonical displayed claim.

### Reused cutoff-one contraction evidence, not new moment production

Parallel read-only review and root source inspection locate more than the
old incidence diagnostic. `BF4CutoffOneBinarySurfaceEmbedding.lean:646`,
`slabSurfaceIsClosed_iff_mem_embeddedBinarySurfaceMasks`, proves completeness
for bounded literal 72-face masks. `BF4ExactCutoffOneSurfaceCharacterReindex.lean:528`,
`cutoffOneFullDualSum_eq_embeddedSurfaceDualSum`, removes actual odd-link
zero terms from the original sum. `BF4ExactCutoffOneSurfaceForestGaugeBridge.lean:305`,
`actualBF4HaarFiveSurfaceBridge`, evaluates the remaining 128 contractions.
All paths in this paragraph are under `lean/YMGap/Continuum/`.

`BF4ExactCutoffOneHaarFiveClosure.lean:65`,
`exactConstantQuadraticMoment_cutoffOne_actual`, therefore supplies the
existing unconditional exact constant-moment polynomial
1+32w^18+96w^30+224w^36+192w^42+3w^48. Its header explicitly excludes
identification with the separately normalized positive physical kernel.
Reuse this vacuum calculation; do not count/rebuild its 128-mask rank as
new evidence or treat it as a charged-observable contraction.

Remaining inserted-moment requirements: original inserted odd-degree
annihilation, literal words/multiplicities, affine charged-mask completeness,
and actual charged Haar contractions. Insertions can repeat a face; the
nonrepeated-support guard of
`SU2QuaternionCutoffOneLinkBucketHaarNetwork.lean:336`,
`finiteProductHaarComplex_cutoffOneOrientedFaceTraceProductAt_eq_linkBucketKernelProduct`,
does not directly cover that case. The general dispatcher
`SU2QuaternionAtMostSixBlockWordFubini.lean:531`,
`finiteProductHaarComplex_atMostSixDistinctBlockWords`, is an available
structural ingredient, not a cheap global evaluation algorithm. No new
inserted moment, normalized tail bound or retention rate is evaluated here.
The existing `ChebyshevFiniteTest` still requires its canonical late cutoff;
early-prefix positivity does not discharge that guard.

### Observed early-cutoff Haar certificate and next action

Final complete 184-line source inspection, independent complete-source
semantic review and root-controlled focused Lean check PASS. The actual
positive floor is uniform over the NAMED range 0<=w<=1/2, all inclusive
K>=1 and supplied Haar-unit scalar carriers. It is not a weak-coupling
w->1 bound. Literal original slab-face instances have produced support
and Haar-unit norm witnesses; shared links and all original coefficients
are retained. No scalar pointwise-to-Haar inference occurs.

| Produced result | Exact declaration |
| --- | --- |
| Explicit positive floor 1055/2272 | `lean/YMGap/Continuum/QuaternionHaarSmallNomeHeatCertificate.lean:53`, `floor`; `:55`, `floor_positive` |
| Actual labels 2..count+1 interval, including empty tail | Same module `:69`, `higherLabelInterval` |
| Original inclusive prefix minus that floor has a Haar certificate | Same module `:111`, `prefixFloorCertificate` |
| Actual original prefix positivity, using existing lower-window producer | Same module `:150`, `prefixCertificate` |
| Literal original slab-face floor and positivity | Same module `:157`, `faceFloorCertificate`; `:168`, `faceCertificate` |

Seven printed gates: floor and its positivity are axiom-free; all five
certificate producers depend exactly on {propext, Quot.sound}. No warning,
sorryAx, new hole/axiom, classical/native shortcut or option increase.
The rational-cap type error was corrected during static review BEFORE
compilation; that earlier source is not evidence. One final focused check,
one 20-GiB worker, 12-GiB reserve, fresh preflight with 88% memory free,
zero swap and no competing compiler/runner. Root import registered only;
no root/tree build, audit, guard, metric or large moment expansion.

```text
Accepted log: /private/tmp/ym-small-nome-early-haar-20261008-a.log
SHA256 4ca0eabbd4c316508b9f98d53317593fab6ea9afcde695f4c494823c4c715e95
Checked source SHA256
9ee8e58c331205cc65a04de933a38157b5f6c3527742ce64f163733a5905cdce
```

Decision: CONTINUE the bounded original raw-moment path with actual early
Haar positivity and REUSE the existing vacuum 128-surface contraction.
Do not call the old guarded `ChebyshevFiniteTest` at K=1. Next missing
pieces are charged original-observable contraction, a feasible evaluator,
and quantitative normalized cutoff payment. No favourable interacting
moment, source survival, changing-family retention, physical calibration,
QFT or Clay closure follows; canonical displayed claims stay unchanged.

## Selected normalized early-cutoff payment (2026-10-08 UTC)

Exact next proposition: for NAMED 0<=w<=1/2 and inclusive K>=1, construct
the actual omitted-character Haar interval with cap
t_K=(81/2272)*(1/72)^(K-1), then bound the normalized change of ONE original
face occurrence from K to K+L by 2*c*eta_K,
eta_K=(81/1055)*(1/72)^(K-1). The observable carries its actual Haar interval
cap c. All shared-link spectator factors, multiplicities and BOTH different
partitions remain. Produce positivity for actual original mixed-cutoff
backgrounds; do not leave that specialization as a new analytic premise.

Available inputs: `SU2AllLabelPointwiseHeatCorridor.lean:217`,
`pointwiseHeatMajorant_succ_le`, and `:304`, `labelTwo_majorant_le`;
`Constructive/CharacterTail.lean:45`, `geom_dom`, and `:73`, `geom_series_le`;
the early actual Haar floor above and the existing `termInterval` compiler.
The normalized consumer is already proved in
`BF4ExactSlabOneFaceCutoffStability.lean:139`, `normalized_difference_bound`,
but its public original instance requires `relativeCutoff/headCutoff`.
Reuse its definitions and the existing relative determinant/partition
cancellation algebra; construct the early estimate without weakening that
guard. Continuum paths in this paragraph are under `lean/YMGap/Continuum/`.

Prediction: local normalization cancels both partitions BEFORE an absolute
volume-dependent reciprocal bound, so the one-occurrence coefficient is
2*c*eta_K, not an exponential product-floor loss. Sequential replacement
of F occurrences would cost a face-count factor F; neither that global
telescope nor a volume-uniform cutoff theorem is supplied by this selection.
The canonical `originalWindowScalar` stage schedule stays unchanged.

Decisive tests: K=1, empty tail L=0, w=0, repeated/shared-link spectator
occurrences and independently varying spectator cutoffs >=1. Stop if a
different action, spectator independence, an assumed normalized error,
or an old cutoff-guard weakening is needed. Verification budget: one bounded
Sol implementation, root and independent complete-source review, serialized
focused 20-GiB check with 12-GiB reserve and fresh dynamic preflight. This
selection is not checked evidence. Charged contraction, useful signed
moments, changing-family retention and every physical/Clay claim stay OPEN.

### Next charged-moment reduction: source-backed argument, not a proof

Independent read-only review and root source inspection select the literal
H116[O*rho72]=H32[O_cube*rho24] reduction for ONE/TWO fundamental inner-cube
face insertions, with repetitions retained. The missing degree/parity pin
is D_b=selected-action incidence_b+sum(inserted-face incidence_b), whose
parity is the incidence of actionMask XOR insertionParityMask. The existing
`BF4ExactCutoffOneTransmittedDegree.lean:225`,
`exactCorrectedSlabWeightedIntegrand_cutoffOne_blockDegree`, and `:133`,
`correctedSlabPlaquetteScalar_blockDegree`, supply homogeneity; `:251`,
`quaternionHaar_116_eq_zero_of_odd_blockDegree`, removes odd totals. The
128-mask completeness theorem above then restricts surviving action masks
to the 24 inner-cube faces, because the insertion parity mask is also inner.
None of the inserted parity/finite-expansion joins is proved by this review.

Reuse the actual carrier machinery:
`BF4ExactCutoffOneSurfaceActiveCarrier.lean:369`,
`reindexBF4SurfaceActiveCarrier_haar`; `:602`,
`reindexBF4SurfaceActiveSpinFactor_tailZero`; and `:258`,
`quaternionHaar_trim_inactive`. Produce the inserted product's full-length
and tail-zero pins before deleting exactly 84 normalized inactive blocks.
All module paths in this paragraph are under `lean/YMGap/Continuum/`.

Decisive multiplicity test: [p,p] has insertion parity zero but degree TWO
on each edge of p; it must not be replaced by a vacuum/bivalent integrand.
For each parity-selected summand, cube incidence <=3 and at most two
insertions give even surviving degree <=4; degree-four links lie in the
insertion-edge union, of size <=8 (<=4 for equal insertions). This is the
proposed contraction-size argument, not a new Lean certificate or a small-
runtime evaluator. The charged contractions and normalized actual moment
values remain missing. Differentiating a face coefficient removes its
action factor and misses the genuine fundamental-square/spin-two channel;
it is not a shortcut to these unchanged-action inserted moments.

### Observed normalized early-cutoff estimate and next action

Final complete 280-line source inspection, independent complete-source
semantic review and the repaired focused Lean check PASS. No analytic error
or positivity input is assumed: the actual tail certificates and original
mixed-cutoff spectator positivity/strict mass are constructed. Shared links,
repeated face occurrences, w=0, K=1 and L=0 remain in the displayed scope.

| Produced result | Exact declaration |
| --- | --- |
| Explicit t_K=(81/2272)*(1/72)^(K-1), eta_K=(81/1055)*(1/72)^(K-1) | `lean/YMGap/Continuum/BF4ExactSlabSmallNomeOneFaceCutoffStability.lean:59`, `tailCap`; `:62`, `relativeTailCap` |
| Exact shifted scalar-majorant bound from existing ratio/head inputs | Same module `:84`, `shifted_majorant_bound` |
| Actual Type-valued two-sided Haar tail and literal face instance | Same module `:121`, `tailInterval`; `:129`, `faceTailInterval_early` |
| Actual mixed-cutoff spectator product certificate and strict mass | Same module `:141`, `backgroundCertificate`; `:151`, `background_mass_positive` |
| Original one-face OWN-normalized error <=2*c*eta_K | Same module `:252`, `original_background_normalized` |

Eleven printed gates: both cap definitions axiom-free; cap nonnegativity
uses propext only; the other eight declarations depend exactly on
{propext, Quot.sound}. No warning, error, sorryAx, new hole/axiom,
classical/native shortcut or option increase in the accepted check. The
first failed parser/lambda elaboration is NOT acceptance evidence. Repairs
use List.length notation and explicit lambda application goals, without
changing a statement or guard. Accepted focused check completes in 0.92s;
one 20-GiB worker, 12-GiB reserve, fresh preflight with 88% free memory,
zero swap and no competing compiler/runner. Root import registered only;
no root/tree build, audit, guard, metric or large moment expansion.

```text
Accepted log: /private/tmp/ym-small-nome-normalized-cutoff-20261008-b.log
SHA256 4afd31177d36035816106628e0bac2419d42e36da598f125f2121885ae5e8281
Checked source SHA256
c5d32d2b75e8a91f18063ced7c771306d073bc879d2dbd8649b50991a77c8e10
```

Decision: CONTINUE. Next mathematical joins are the ACTUAL finite-list
normalized telescope and the repeated-insertion H116->H32 reduction, then
charged contraction values. The local coefficient has no background size
or inverse full-partition factor; it is NOT a volume-uniform bound on a full
list change. The canonical original-window stage schedule is unchanged.
No favourable signed interacting moment, changing-family retention,
physical calibration, continuum QFT or Clay closure is supplied. No
canonical displayed claim changes, so no chart reprint is warranted.

## Selected full finite-action cutoff payment (2026-10-08 UTC)

Exact next proposition: replace ALL F=ids.length original heat-factor
occurrences from inclusive K>=1 to K+L at NAMED 0<=w<=1/2, with normalized
observable error <=2*c*ofNat(F)*relativeTailCap(K). Freeze actual mixed-cutoff
spectators during induction; retain repeated faces/shared links and both
OWN masses. Actual local input is the checked `original_background_normalized`
above. Product-list recoding and normalized-moment congruence identify each
step; triangle inequality sums its cost. No coefficient-L1 product envelope,
absolute inverse partition floor, independence or new error premise is used.

Actual downstream consumer: compare a supplied early rational cutoff value
to the EXISTING original face-set expectation in
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:72`,
`expectation`. Its `finiteValue` uses headCutoff(w)+n, not the early schedule.
Use its explicit convergence and an actual common/later cutoff comparison;
do not construct a replacement limit or weaken the headCutoff guard. The
finite theorem admits zero nome; this strict-nome CReal consumer does not.

Prediction: normalized sequential comparison pays the LINEAR face count F,
not an exponential product-floor inverse. That count is explicit and is
NOT a thermodynamic-uniform estimate. Decisive tests: empty action list,
repeated occurrences, shared links, empty tail, K=1 and distinct early versus
canonical later cutoffs. Stop if recoding erases occurrences, changes the
physical action/normalization, or the limit join needs an unavailable input.
Budget: one bounded Sol leaf, root/independent complete-source review and
serialized focused 20-GiB verification with 12-GiB reserve/fresh preflight.
Selection is not checked evidence; charged moment values, changing-family
retention and every physical/Clay claim remain OPEN.

### Parallel selected inserted-degree producer

Exact next proposition: the literal product of fundamental physical-face
insertions, with factor TWO and repetitions retained, has the sum of its
occurrence block degrees. Multiplying by the original cutoff-one weighted
action summand adds the selected-action degree; an odd computed total gives
an actual 116-link Haar zero with support produced from physical-face guards.
This fills the inserted homogeneity/odd-vanishing pin named above; it is not
a charged-mask completeness theorem or an evaluated nonzero moment.

Available action/face homogeneity and odd-Haar compiler are the cited
TransmittedDegree declarations. Consumer is the proposed repeated-insertion
H116->H32 reduction, followed by charged contractions. Decisive test [p,p]:
degree TWO per face edge must remain although insertion parity vanishes.
Stop if this producer already exists or requires assuming support/Haar zero
instead of producing them from literal data. One bounded separate agent leaf;
root/independent source review and a later SERIALIZED focused check under the
same 20-GiB/12-GiB policy. No full-tree run or large evaluation is authorized.
Selection is not proof evidence; affine mask/reindex/evaluator joins and the
entire physical/scaling target remain OPEN.

### Charged-contraction route screen: retain signed quartic channels

Read-only source selection, not a new check or runtime certificate:
`lean/YMGap/Continuum/SU2FundamentalHaarCheckpoint.lean:62`, `fourthValue`,
is the exact coefficient (1/6) times the THREE epsilon-pairing products,
with local row identities `fourth_row_0000` through `fourth_row_1111`.
`second_entries` supplies the bivalent coefficient 1/2. The three tensors
are overcomplete (rank two), not three independent positive channels.
The alternative balanced projector retains four signed inverse-Gram terms;
its negative coefficients must not be replaced by a multiplicity.

Orientation/spectator tools already exist:
`lean/YMGap/Continuum/SU2QuaternionFundamentalSelfDuality.lean:150`,
`fundamentalOccurrenceCoefficient_eq_dual`, retains complemented TRANSPOSED
indices and signs; `SU2QuaternionGenericBlockOrientedEvenWordNormalization.lean:682`,
`genericBlock_orientedFourFundamentalWord_projector_with_complex_spectator`,
and the at-most-six multiblock dispatcher above retain actual integration.
The latter path is relative to `lean/YMGap/Continuum/`.

If the proposed <=8 exceptional quartic links and affine 128-mask pins are
proved, THREE-pairing expansion would have at most 128*3^8=839808 diagrams
(one insertion: 128*3^4=10368). These are proposed DIAGRAM counts, not
verified runtimes or an implemented original-moment evaluator. Missing:
generic-block arbitrary-oriented transport of the three-term formula and
exact signed delta/epsilon cycle contraction, pinned to the actual repeated
trace sum without a Boolean-environment expansion. The symbolic Boolean
contraction-plan module explicitly does not compile a concrete graph or
evaluate these loops. No vacuum topological amplitude is substituted for
a quartic/charged contraction; no large pilot is selected.

## Observed full-list cutoff payment and inserted degree (2026-10-08 UTC)

CHECKED actual full-list normalized estimate, not a supplied error premise:

- `lean/YMGap/Continuum/BF4ExactSlabSmallNomeCutoffStability.lean:150`,
  `original_mixed_cutoff_bound`, freezes literal mixed-cutoff spectators and
  changes each occurrence by the checked one-face cancellation estimate.
  Every intermediate OWN mass is produced positive. Repeats/shared links
  need no independence or distinct-face premise.
- `BF4ExactSlabSmallNomeCutoffStability.lean:248`, `original_cutoff_bound`,
  specializes to the ORIGINAL uniform-cutoff product with error
  2*c*ofNat(ids.length)*(81/1055)*(1/72)^(K-1), at NAMED 0<=w<=1/2,K>=1.
  Both normalizations remain; no exponential full-partition inverse appears.
- `BF4ExactSlabSmallNomeCutoffStability.lean:268`, `commonValue_cutoff_pin`,
  identifies the unchanged canonical stream with actual later raw moments.
  `expectation_cutoff_bound:299` reaches the EXISTING
  `AllNomeFaceSetExpectation.expectation`, using its convergence/modulus,
  not a replacement limit. This last join requires strict 0<w<=1/2.

The last two paths are relative to `lean/YMGap/Continuum/`. The constant c is
the supplied ACTUAL observable interval cap, not a computed useful retention
margin. Empty action lists and empty tails are included; the list induction
counts repeated occurrences, and K=1 is permitted. Face count is explicit,
so this is NOT volume-uniform or a w->1 estimate. In particular an exact
cutoff-one charged value alone is NOT certified accurate for the limit:
the uniform K=1 full-list cap may be too loose for that downstream decision.

CHECKED parallel actual inserted-degree producer:

- `lean/YMGap/Continuum/BF4ExactCutoffOneInsertedDegree.lean:40`,
  `fundamentalFaceFactor_eq_two_scalar`, retains the fundamental factor TWO;
  `insertedFundamentalProduct:45` is the literal occurrence-list product.
- `exactCutoffOneInsertedIntegrand_blockDegree:101` retains the COMPLETE
  original weighted 72-face summand and adds existing occurrence-counted
  `slabFacesBlockDegree` to the original selected-action degree.
- `exactCutoffOneInsertedHaar_eq_zero_of_odd_degree:117` invokes actual odd
  homogeneous Haar annihilation with produced 116-block support. No supplied
  support/Haar-zero premise replaces the producer.
- `repeatedFace_degree_and_parity:137` retains degree twice for [p,p],
  although the parity is zero. This does not replace its product by vacuum.

These inserted declarations are all in the same cited module. Support holds
even for literal fallback face factors; physical membership remains explicit
where needed for actual incidence homogeneity. No charged completeness,
H116->H32 pin or nonzero charged contraction value is proved by this leaf.

Verification: two SERIALIZED focused checks complete in 1.11s and 1.24s.
The telescope's eight gates have `atCutoff` axiom-free and seven exactly
{propext, Quot.sound}; all nine inserted gates have exactly the permitted
pair. Both accepted logs have no warning/error/sorryAx. No new hole/axiom,
native/classical shortcut or option increase. Independent complete-source
review passes both FINAL source hashes. The first telescope check failed
implicit-cutoff/dependent-rewrite elaboration and is NOT acceptance evidence;
explicit late-cutoff guard annotations and Nat-addition simp transport fix
it without changing any statement. Each launch followed fresh 88%-free,
zero-swap/no-competing-process preflight, one 20-GiB worker/12-GiB reserve.
Root imports registered only; no root/tree build, audit, guard, metric or
large original-moment expansion.

```text
Accepted telescope log: /private/tmp/ym-small-nome-full-cutoff-20261008-b.log
SHA256 a1dc3dbf534d009bc94b0717d035d8122ba58b0a6c45ca464a21f0239ab78e55
Final checked telescope source SHA256
e5cee3a75547b898ccb35e1e60f8159adb1acb9da6e0af8af68ede6299e8a7bd
Accepted inserted log: /private/tmp/ym-cutoff-one-inserted-degree-20261008-a.log
SHA256 7a371d1d602e67e7cdf0a49051aeccacd57498c8736309787ae07b3e5f367b40
Final checked inserted source SHA256
eba87bd243842213e5d6525e0216b179019cc63a5a03260d57ab680bfaf5b513
```

Decision: CONTINUE toward actual charged parity completeness/active reindex
and signed contraction, while keeping useful accuracy as a separate unpaid
consumer requirement. The two produced joins remove the FULL finite-list
cutoff-payment and inserted-degree gaps named in earlier checkpoints above;
they do not supply favourable interacting moments, DIRECT original macro
retention, justified changing-family estimates, physical calibration,
continuum QFT/every-group or Clay closure. Canonical displayed claims remain
unchanged, so no chart reprint.

### Next-route screen after the accepted proofs (read-only)

REUSE, do not rebuild, the existing action-incidence bridge:
`lean/YMGap/Continuum/BF4ExactCutoffOneSurfaceCharacterReindex.lean:201`,
`cutoffOneSlabSelectedBlockDegree_eq_maskIntersectionCount`, and its
`slabFaceBlockDegree_eq_incidenceBit:129`. Existing completeness is
`lean/YMGap/Continuum/BF4CutoffOneBinarySurfaceEmbedding.lean:646`,
`slabSurfaceIsClosed_iff_mem_embeddedBinarySurfaceMasks`.
The missing next parity pin identifies total insertion/action degree modulo
two with the incidence of action-mask XOR insertion-mask. A repeated pair
has zero insertion mask, not an absent polynomial. Actual action heat weights
must follow the resulting ACTION mask, not the shifted closed mask.
Reduction to the inner carrier also needs literal insertion face IDs in
`activeHypercubeSlabFaceIds`; mere physical-slab membership is insufficient.
These are proposed missing joins, not checked completeness or reductions.

REVISE the accuracy gate before a large cutoff-one computation: substituting
F=72,K=1 into the proved corridor budget gives (11664/1055)*c, already larger
than 2*c. Do not call this useful limit accuracy. A nome-sensitive first-tail
payment or a feasible higher-cutoff evaluator is still needed. Existing
`lean/YMGap/Continuum/SU2AllLabelPointwiseHeatCorridor.lean:217`,
`pointwiseHeatMajorant_succ_le`, provides the 1/72 ratio, while its
`labelTwo_majorant_le:304` replaces the actual nome-dependent head by the
worst-case half-nome head. Retaining the actual head is an eligible bounded
next estimate, not yet a produced interval/telescope certificate. No large
moment evaluation, new Lean check or displayed chart change in this screen.

## Selected nome-sensitive accuracy and charged parity joins (2026-10-08 UTC)

Exact next estimate: keep the actual label-two head 9*w^8 in the existing
1/72 geometric argument. Produce the literal face-tail Haar interval with
cap (648/71)*w^8*(1/72)^(K-1), and pay it by the unchanged early floor
1055/2272. Reuse the same normalized cancellation/list induction/limit,
giving relative cap (20736/1055)*w^8*(1/72)^(K-1). Existing public estimates
and canonical guards remain; do not clone their cancellation proofs.
Consumer: actual original early-cutoff moments compared to the EXISTING
all-nome expectation. Prediction: at 72 faces,K=1,w=1/4 the full error is
(729/16880)*c<=c/20, with coefficient 729/16880<1/20 and nonnegative cap c
from the actual observable interval (also valid at c=0).
Tests: w=0 tail zero; w=1/2 old cap; repeated faces and distinct OWN masses;
inclusive K=1; no new pointwise-to-Haar inference. This is fixed-corridor
pilot accuracy, not w->1/scaling/retention. Budget: two changed focused
targets, serialized 20-GiB/12-GiB verification, full independent review.
Stop/revise if a new analytic tail/floor input or action/limit change is needed.

Parallel bounded join: total occurrence-degree parity equals the edge parity
of action-mask XOR insertion-mask. Reuse the cited actual degree/incidence
pins and existing 128-mask completeness. Actual odd-degree Haar vanishing
must eliminate every nonclosed affine mask. Repeated insertions retain their
polynomial even when their parity mask is zero. Consumer: charged active-
carrier reduction, not an evaluated contraction. One bounded Sol leaf,
root/independent source review and later serialized check; no 2^72 expansion,
new elimination certificate, H32 evaluation, runtime or physical closure.
Selection is not acceptance evidence. Main DIRECT macro retention or
sufficient JOINT original-family estimate and full Clay target remain OPEN.

## Observed nome-sensitive ORIGINAL cutoff accuracy (2026-10-08 UTC)

CHECKED actual interval producer, not a scalar/measurement premise:
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeOneFaceCutoffStability.lean:227`,
`nomeFaceTailInterval`, retains the actual label-two majorant 9*w^8 with
the existing 1/72 ratio. It produces cap (648/71)*w^8*(1/72)^(K-1).
`nomeRelativeTailCap:145` divides by the unchanged produced floor 1055/2272;
`nomeRelativeTailCap_zero:171` and `nomeRelativeTailCap_half:179` check
zero tail and exact recovery of the old endpoint cap. Named corridor remains
0<=w<=1/2,K>=1. No canonical head guard changes or pointwise-to-Haar leap.

`lean/YMGap/Continuum/BF4ExactSlabSmallNomeCutoffStability.lean:304`,
`original_nome_cutoff_bound`, and `expectation_nome_cutoff_bound:398` supply
full-list error 2*c*ofNat(ids.length)*nomeRelativeTailCap(w,K), retaining
BOTH OWN masses, all occurrences and the SAME existing limit/modulus.
Shared cancellation, induction and limit passage are factored once; EVERY
old public bound retains its statement/guards and passes the focused regression.
`quarter_nome_72_cutoff_one_budget:410` kernel-checks coefficient 729/16880<1/20.
This is actual useful absolute accuracy at the chosen fixed small nome,
not a charged moment value, favourable signed reserve or scaling estimate.

Accepted focused checks: OneFace 1.04s/20 gates, Full 1.23s/11 gates. All
31 gates are within {propext,Quot.sound}; four OneFace definitions and two
Full declarations are axiom-free. Accepted logs have no warning/error/sorryAx.
Independent FINAL complete-source review passes. One preliminary check's
unknown reflexivity identifier is NOT evidence; repair uses the existing
setoid reflexivity/order lemma, without changing any statement or option.
Static review also replaced rational normalizer constants with explicit
scalar identities before checking. Each check used one 20-GiB worker,
12-GiB reserve/fresh 88%-free zero-swap/exclusion preflight. No root/tree
build, audit, guard, metric or large moment computation.

```text
Accepted OneFace log /private/tmp/ym-nome-sensitive-oneface-20261008-b.log
SHA256 afb4f219de04eb3a6a47bdf97d43a9dd7507773936ef9eed679ab673919fe867
Checked OneFace source SHA256
de3347b49b57364d5a7586458e2294170c58e44fc03851148a5ec4a75ddbaa36
Accepted Full log /private/tmp/ym-nome-sensitive-full-cutoff-20261008-a.log
SHA256 b87a8a8204439e9e087c40a37725bf0af585305b64e17ede3954fbf8a1fed6f8
Checked Full source SHA256
7a1cb7689c1cc000a90f196b41fab00939551e592b249c0f696b44ca64226751
```

Decision: CONTINUE. Chosen small-nome accuracy is now supplied; no need to
force a higher-cutoff evaluator solely to pay this corridor error. Charged
values/active reduction remain unpaid. At this checkpoint the parallel affine-mask draft is
NOT accepted yet: its successful elaboration still reports Classical.choice
in count_singleton and downstream parity declarations; focused diagnostic
gates locate it, and a constructive repair is underway. No classical
quarantine or frontier weakening is authorized or used. DIRECT retention,
justified changing-family/physical calibration, QFT/every-group and Clay
remain OPEN. No displayed chart claim changes. Earlier line citations refer
to their recorded checkpoint source hashes; new citations above are current.

## Observed constructive ORIGINAL inserted affine selection (2026-10-08 UTC)

Accepted leaf `lean/YMGap/Continuum/BF4ExactCutoffOneInsertedMask.lean`:

- `insertionMask:35` is occurrence-list XOR; `insertedFaces:40` preserves
  every literal face occurrence; `affineMask:46` is original action XOR charge,
  NOT an integrand action replacement.
- `inserted_degree_parity:148` and `inserted_totalDegree_parity:172` pin
  parity of the actual action-plus-insertion degree at every one of 116 links.
- `inserted_parity_allowed_iff_mem:189` joins actual every-link parity to the
  existing 128 embedded closed masks, using produced physicality/mask bounds.
- `exactCutoffOneInsertedHaar_eq_zero_of_affine_not_closed:232` proves literal
  inserted Haar zero for nonclosed affine masks. This is necessary parity
  selection, NOT nonzero sufficiency. Repeated [p,p] remains a squared
  insertion even though its XOR charge is zero. Original heat weights remain.

The first compiling draft was correctly rejected: its private singleton
bit-count helper depended on Classical.choice. Local gates and a printed
proof term isolated an arithmetic tactic's fallback while proving an entire
iff. Explicit decidable equality cases, constrained Boolean simplification
and introduction of both iff directions remove it. The accepted final
source uses no classical quarantine, new premise, hole or resource option.
Preliminary a--f logs are NOT accepted evidence; d was an elaboration repair
and b/c/e/f exposed the classical dependency. Final g check: exit 0, 0.88s,
19 gates ALL within {propext,Quot.sound}, no error/warning/sorryAx/choice.
Complete independent FINAL-source semantic review passes. One 20-GiB worker,
12-GiB reserve, fresh 88%-free/zero-swap/exclusion preflight. Root import is
registered only; no root/tree build, audit, guard, metric or large evaluator.

```text
Accepted log /private/tmp/ym-cutoff-one-inserted-mask-20261008-g.log
SHA256 e86079fec6d175a1eadf00f1cfa4398a9b511950fbe83be74d51881aa4079672
Checked final source SHA256
518a93a9653f88874626fa657a3b5e7eadd7339cce7825251af56418c442a29d
```

Decision: CONTINUE. Useful fixed-small-nome accuracy and necessary charged
selection now meet. NEXT is literal inserted H116->H32 reduction for the
actual inner insertion faces, then signed contractions of the surviving
action candidates. A closed affine mask z corresponds to action z XOR charge;
do NOT replace its original popcount/heat weight by that of z. No charged
value, active reduction, positive response reserve or scaling retention is
claimed here. DIRECT macroscopic retention or sufficient JOINT original-
family estimate, continuum survival, physical mass/QFT/every-group and Clay
remain OPEN. No canonical displayed claim changed; no chart reprint.

## Selected ORIGINAL inserted active-carrier join (2026-10-08 UTC)

Previous goal increment: PROGRESS, accepted accuracy and constructive affine
selection committed/pushed as 72ac2157 and 51631e1f. Current selected proposition:
H116(I) = H32(trim32(reindex(I))) for the literal
`BF4ExactCutoffOneInsertedDegree.exactCutoffOneInsertedIntegrand`, assuming
cutoff-one physical labels, actual inner insertion IDs and affine membership
in the existing 128 closed masks. This exact inserted consumer does not yet
exist; it removes the pilot's active-carrier reduction input, not charged
evaluation or changing-family retention. Keep original heat weights intact.

Available inputs: SurfaceActiveCarrier's actual inner-factor zero-tail theorem
(602), tail product closure (445), Haar reindexing (369), reindexed term lengths
(394), inactive deletion (258), and closed-mask face-support check (486).
Produce action inner support: outside the inner 24 faces both closed affine
mask and insertion XOR charge have zero bits, hence so does the action mask.
Generalize the selected-action fold locally; the legacy fold (682) assumes
an uncharged closed action and cannot be applied to translated candidates.

Prediction: no new geometry certificate, analytic input or permutation;
finite bit algebra and occurrence-preserving product induction suffice.
Decisive tests: empty/repeated insertion lists; charge-zero is NOT polynomial
one; translated action weight remains its original coefficient; outer
insertions do NOT qualify. Budget: one new focused leaf, bounded Sol
implementation and independent full-source review, serialized 20-GiB worker
with 12-GiB reserve/fresh dynamic preflight. Revise if a required support fact
is unavailable or if the proof assumes the desired zero tail instead of
producing it. No large contraction, root/tree build, audit, guard or metric.

## Observed ORIGINAL inserted H116->H32 reduction (2026-10-08 UTC)

Accepted source `lean/YMGap/Continuum/BF4ExactCutoffOneInsertedActiveCarrier.lean`:
`inner_insertionMask_bit_zero:59` and `affine_action_inner_support:82`
derive ORIGINAL action inner support from actual inner insertion IDs and
closed affine membership. The original action mask need not itself be closed.
`reindex_insertedIntegrand_tailZero:218` retains the literal heat coefficient
and both occurrence-preserving products. `exactCutoffOneInsertedHaar_eq_active:236`
uses the EXISTING checked permutation/exact term lengths/normalized deletion
to give the SAME inserted H32 value. Arbitrary Q' nome and list multiplicity;
no polynomial expansion, action replacement, repeated-factor deletion,
new geometry/permutation certificate or support conclusion as a hypothesis.
Outer insertions do not meet the actual-inner-ID guard.

Accepted final focused check c: exit 0, 1.53s, all 12 public/helper gates
exactly {propext,Quot.sound}, no error/warning/sorryAx/choice. Complete
independent FINAL-source review passes. Preliminary a/b logs are NOT evidence:
missing selective namespace and an unfolded-index arithmetic alignment were
repaired, with unchanged guards/math and no option increase. Each launch
used one 20-GiB worker/12-GiB reserve and fresh 88%-free/zero-swap/exclusion
preflight. Root import registered only; no root/tree build, audit, guard,
metric or large charged calculation. Minor accuracy documentation correction:
the coefficient is strictly below 1/20, but the c-scaled bound is non-strict
at c=0; no Lean theorem changed.

```text
Accepted log /private/tmp/ym-cutoff-one-inserted-active-20261008-c.log
SHA256 b31d6930c154c088bb5d3aefebf892e0b743f68b5f2f41db842c929ddc53a5c0
Checked final source SHA256
db12ed438218d8e1126ac9b0ea1f0ac3023d5e3863c7aa5ff394a2e71216d5c2
```

### Separate read-only next-budget screen (not a proved bound)

Sol source review and root reconciliation identify one missing actual
geometry certificate: on each raw block<116, the sum of incidence of the
literal inner24 faces is at most 3. No declaration asserting it was found
in `BF4CutoffOneBinarySurfaceCertificate`, `BF4CutoffOneBinarySurfaceEmbedding`,
`BF4ExactCutoffOneSurfaceActiveCarrier`, or the inserted degree/mask leaves.
Existing compact bivalency (`BF4CutoffOneBinarySurfaceCertificate.lean:124`,
`binarySurfaceMasks_edge_bivalent`) does not supply this translated-action
bound automatically. Actual insertion incidence is 0/1 by
`BF4ExactCutoffOneSurfaceCharacterReindex.lean:129`,
`slabFaceBlockDegree_eq_incidenceBit`; even actual total degree is supplied
by `BF4ExactCutoffOneInsertedMask.lean:189`, `inserted_parity_allowed_iff_mem`.

If the actual inner24 cap is produced, the new action-support theorem bounds
selected action degree by 3. One/two insertion occurrences add at most 2;
even degree then forces {0,2,4}. Away from insertion edges it forces {0,2}.
`BF4GeometricSpinNetworkMehler.lean:356`, `orientedPlaquetteBoundary_length`,
supplies four boundary entries per insertion, suggesting at most 8 quartic
links (at most 4 for a repeated face). This count/degree argument still needs
its actual finite proof. It bounds input degrees, NOT evaluator intermediate
sizes or runtime. No new numerical sweep, compiler or result from this screen.

Decision: CONTINUE with that small incidence/degree producer before selecting
a costly signed contraction. Active reduction and fixed-small-nome accuracy
are supplied; charged values, original positive reserve, DIRECT macroscopic
retention or sufficient JOINT changing-family estimate remain unsupplied.
Continuum survival, calibrated physical gap, SAME QFT/every-group and Clay
remain OPEN. No canonical displayed claim changed; no chart reprint.
