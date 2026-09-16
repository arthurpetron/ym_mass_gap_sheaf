# The original weighted step has a bounded ordinary-Haar completion

Date: 2026-09-16. Classification: PROGRESS after `1e8cd78`;
the intervening literature recheck is `7d9118b`.

Whole-project goal: constructive, nontrivial continuum Yang--Mills on R^4,
the required QFT axioms, and a positive physical Hamiltonian gap for every
compact simple group, on the SAME theory. This finite-cutoff ordinary-Haar
construction is not that physical completion or a mass-gap theorem.

## Mathematical result

On the width-only N-block spatial carrier, keep the original map

    T f(y) = integral_x K(x,y) V(x) f(x) dH_N(x).

For rational 0<w<1, set

    C(w,width) = prefixCap(w)^#temporalFaces(width)
                   * prefixCap(w)^#spatialFaces(width).

At every heat cutoff k>=headCutoff(w), the proved bound is

    H_N[(T f)^2] <= C(w,width)^2 * H_N[f^2].

It holds for every supported signed rational polynomial f. The constant
is independent of k; neither width nor nome dependence is suppressed.
The same T extends to a bounded Q'-linear map on the existing ordinary
product-Haar GNS completion. Its dense action and pairing are pinned
exactly, with no layer-by-layer normalization or rescaling.

## Proof and causal consumers

Paths in the table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | What it proves or constructs |
|---|---|---|
| `relative_unit` | `BF4ExactSlabFixedSpatialKineticOrder.lean:72` | Actual lower-times-inverse-upper word is unit under every Haar insertion. |
| `kineticCertificate`, `kineticInterval` | `BF4ExactSlabFixedSpatialKineticOrder.lean:152`, `:158` | Positive actual kinetic layer at late cutoff; all-cutoff cap with temporal-face count. |
| `kinetic_weighted_floor`, `kinetic_weighted_upper` | `BF4ExactSlabFixedSpatialKineticOrder.lean:191`, `:212` | Lower/upper kinetic comparison in every certificate-positive background. |
| `plaquette_unit` | `BF4ExactSlabFixedSpatialSpatialOrder.lean:98` | Ordered spatial source words are unit in any carrier with enough room. |
| `spatialCertificate`, `spatialInterval` | `BF4ExactSlabFixedSpatialSpatialOrder.lean:129`, `:136` | Actual head V certificates directly on N+N blocks, without an assumed certificate lift. |
| `kernelMap_pairing` | `SU2QuaternionHaarKernelBound.lean:137` | Exact ordered-head Fubini against the retained probe. |
| `kernelMap_bilinear_bound`, `kernelMap_square_bound` | `SU2QuaternionHaarKernelBound.lean:148`, `:195` | Weighted Cauchy--Schwarz and rational positive/zero norm cancellation. |
| `stepWeightCertificate`, `stepWeightInterval` | `BF4ExactSlabFixedSpatialTransferBound.lean:55`, `:61` | Both weights on the SAME pair carrier, with one head V. |
| `transferStep_kernelMap` | `BF4ExactSlabFixedSpatialTransferBound.lean:71` | Coefficient reassociation only; identifies the bounded map with original T. |
| `transferStep_square_bound` | `BF4ExactSlabFixedSpatialTransferBound.lean:93` | Actual original-step squared-norm estimate. |
| `BoundedMap.mapCauchy`, `mapCauchy_null` | `SU2QuaternionHaarBoundedCompletion.lean:74`, `:84` | Explicit modulus and proved null descent on existing representatives. |
| `BoundedMap.completionMap_norm_bound` | `SU2QuaternionHaarBoundedCompletion.lean:104` | Same rational bound on all completion points. |
| `denseTransfer`, `completedTransfer` | `BF4ExactSlabFixedSpatialCompletedHaarTransfer.lean:51`, `:62` | The original map inhabits the completion consumer using the proved estimate. |
| `transfer_modulus` | `BF4ExactSlabFixedSpatialCompletedHaarTransfer.lean:69` | Modulus is `X.modulus (epsilon * invSucc ((C*C).num.toNat))`. |
| `completedTransfer_embed`, `completedTransfer_norm_bound` | `BF4ExactSlabFixedSpatialCompletedHaarTransfer.lean:76`, `:84` | Exact dense action and completed norm bound. |
| `completedTransfer_add`, `completedTransfer_smul` | `BF4ExactSlabFixedSpatialCompletedHaarTransfer.lean:95`, `:110` | Additivity and rational scalar linearity on arbitrary completion points. |
| `completedTransfer_pair_dense` | `BF4ExactSlabFixedSpatialCompletedHaarTransfer.lean:132` | Ordinary completed pairing equals H_N[Tf*g]. |

The completion does not select representatives from propositions. It acts
termwise on supplied Cauchy representatives; explicit rational tolerance
transports the modulus and null relation. Quotient descent is then proved.
No new carrier replaces the existing GNS completion. The actual instance
discharges every generic algebraic/norm input.

## What remains open

The original selected-chain moment uses H_N[(T^n f)*V*g], not the
unweighted terminal g. A finite-power completed pairing pin must retain
this V and its support. The exact finite-chain scalar cutoff limit already
exists, but is not an operator-cutoff limit.

The kinetic positive floor depends on nome and face count. No rate below
one, width-/spacing-independent estimate, Perron vector, stationary vacuum,
reflection-positive OS quotient, completed physical transfer, or continuum
limit is proved here. Q'-linearity does not assert a newly proved CReal
module structure. Positivity/self-adjointness of this completed map is not
inferred from positivity of the integration weight.

Next mathematical work: actual partial-Haar square-certificate preservation
and quantitative order contraction/boundary forgetting, followed by a
stationary time construction and physical OS identification. None is
replaced by the existing finite-state refresh theorem. Uniform
thermodynamic/spacing control, continuum QFT/nontriviality and all compact
simple groups remain open. No frontier field or old statement was changed;
no literal hole, new axiom or analytic premise was added or discharged.

## Verification boundary

Six focused serialized checks used `scripts/safe_lean_build.py`, one worker
and the mandatory 20 GiB ceiling. All 57 public gates lie within
{propext, Quot.sound}. Process/swap preflights preceded each check; no
limits were raised. Fixes were namespace/layout issues, the explicit
CReal order slack, and factoring the dense inner-product proof to avoid
unfolding the full physical weight during elaboration.

Independent source review confirmed original weight accounting, cutoff
guards, empty-face behavior, support, quotient descent and ordinary/OS
scope. Six imports were added to the selective root. Root/full-tree
verification and the full axiom audit were NOT run. CI remains manual-only.

| Focused log in `/tmp/` | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialKineticOrder.log` | `3c78ef41f04a7bc76698ae9444f2c78e9beb90121002ca0e1381794ca9990ff0` |
| `BF4ExactSlabFixedSpatialSpatialOrder.log` | `5a33f70d00f9841d747c3ba597bb590b786a1fbb51b82bce711b2888c73cd6ac` |
| `SU2QuaternionHaarKernelBound.log` | `d7352672f80439995f678c2cf172b4333613267e1fb948f3ac82ca33a87fa13c` |
| `SU2QuaternionHaarBoundedCompletion.log` | `904eea1e5064c9d73ebc8b6246ea91d0122a26ab817805b6c8ba2ea63cd2ebe5` |
| `BF4ExactSlabFixedSpatialTransferBound.log` | `ed20ad6e197035c80cfaa72f1bb5df4097358f64f16f56acde5da062c5d6a6b8` |
| `BF4ExactSlabFixedSpatialCompletedHaarTransfer.log` | `2537aa3085163518daaf9ddbdd9ad9e16d1ccc07a506dff9efc88398c64d4a91` |

## Completed original moments and Gaussian square follow-up

Date: 2026-09-16. PROGRESS after `c7a5ddb`. The following checked result
closes the finite-power original-moment seam explicitly left open above.
Paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Checked content |
|---|---|---|
| `completedIterate` | `BF4ExactSlabFixedSpatialCompletedIteration.lean:48` | Finite powers of the same actual completedTransfer. |
| `completedIterate_embed` | `BF4ExactSlabFixedSpatialCompletedIteration.lean:57` | Exact dense pin to iterateStep, with support maintained. |
| `completedIterate_pair_dense` | `BF4ExactSlabFixedSpatialCompletedIteration.lean:79` | Completed inner product equals H[(T^n f)*V*g]. |
| `completedIterate_compactNumerator` | `BF4ExactSlabFixedSpatialCompletedIteration.lean:95` | Signed face-source probes give the pre-existing compact numerator. |
| `completedIterate_originalNumerator` | `BF4ExactSlabFixedSpatialCompletedIteration.lean:110` | Same original selected action and endpoint insertions, with width/time/face guards. |
| `headGram`, `channel`, `squareSum` | `SU2QuaternionHeadGaussianSquareCertificate.lean:132`, `:142`, `:147` | Explicit four-coordinate Gaussian Gram channels retain all tail exponents. |
| `partialGaussianHead_square_coeff` | `SU2QuaternionHeadGaussianSquareCertificate.lean:181` | Polynomial-valued square identity under every tail coefficient probe. |
| `channel_supported` | `SU2QuaternionHeadGaussianSquareCertificate.lean:235` | Each channel loses precisely the four integrated head coordinates. |
| `squareSum_certificate`, `partialGaussianHead_square_certificate` | `SU2QuaternionHeadGaussianSquareCertificate.lean:256`, `:265` | Constructive nonnegative weighted square certificates on the tail. |

At n=0 the completed power is the identity and the pairing still has one
spatial V. At arbitrary n there are n kinetic and n+1 spatial weights,
as in the original finite-chain theorem. No T1=1 law, independent layer
normalization, or omission of endpoint action factors is used. The existing
normalized scalar cutoff theorem remains about the entire finite-chain
pairing, not convergence of the completed operators or intermediate messages.

The Gaussian producer is a separate constructive algebraic branch. It
integrates four Gaussian coordinates, not Haar sphere coordinates. It
uses existing Gram weights and vectors with their proved nonnegativity;
no pointwise positivity-to-certificate rule is postulated. Turning this
into an actual partial-Haar certificate producer, or giving a direct Haar
producer, remains open at this checkpoint. Thus this result alone does not
prove original-transfer order preservation or boundary forgetting.

Both files passed focused, serialized one-worker/20 GiB checks. The final
five completed-iteration gates and eight Gaussian gates are within
{propext, Quot.sound}; the finite sum definition is axiom-free. The only
completed-iteration retry added the existing support-lemma namespace.
No old statement, canonical field, literal hole or analytic premise changed.
Two selective-root imports were added. No root/full-tree check or full
axiom audit was run. Physical OS/stationary, volume/spacing/continuum and
all-group gap obligations remain open; CI stays manual-only.

| Focused log in `/tmp/` | SHA-256 |
|---|---|
| `BF4ExactSlabFixedSpatialCompletedIteration.log` | `8d99673091077b6e0e49f3dc151c9d683334a33522fb2459707305cc9ec4d61a` |
| `SU2QuaternionHeadGaussianSquareCertificate.log` | `f1f042ec28073e9833594022fc4536ffa59a98a6b3b30b675f69b4630cab57d3` |
