# Actual T2, collar tests, and the missing range estimate

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
