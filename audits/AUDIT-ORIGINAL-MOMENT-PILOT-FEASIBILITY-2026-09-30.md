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
