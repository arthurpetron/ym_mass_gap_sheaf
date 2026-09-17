# Actual kinetic PSD and the original interacting one-step quadratic

Date: 2026-09-17. Starting commit: `718c6e4`. Three new focused Lean targets
passed. The next window/completion join below is source-level planning,
not a claimed theorem.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT axioms, isolated
vacuum and positive finite physical Hamiltonian mass gap. **OPEN.**

## Proved mathematical increment

Let P be the actual selected-pair product heat map and V the full original
spatial action weight. The new theorems prove

    H[f * P f] >= 0,
    T f = P(V*f),
    H[V*f*T f] = H[(V*f)*P(V*f)] >= 0.

The first and third inequalities hold for every supported signed f,
nonnegative rational nome and every finite cutoff. The product-kernel
theorem permits repeated selected pairs. It neither assumes normalized
marginals nor obtains operator PSD from pointwise density positivity.

The proof uses the actual all-degree representation Gram expansion. Each
heat factor inserts positively weighted a(x)*a(y) channels. Its y-channel
is the proved coordinate lift of a(x), including real AND imaginary parts.
The induction hypothesis is applied to f*a, retaining every signed term
and spectator. The empty product yields H[f]^2. Thus the finite proof needs
no distinctness of selected pairs and no density floor or small-nome guard.

All new source paths below are under `lean/YMGap/Continuum/`.

| Declaration | Source | Exact role |
| --- | --- | --- |
| `coordinateColumn_supported` | `SU2QuaternionCoordinateColumnLift.lean:138` | Original arbitrary-degree columns have the required finite support. |
| `TensorLiftImage` | `SU2QuaternionCoordinateColumnLift.lean:220` | Common-padding lower-to-upper identity on both components, not assumed Haar equality. |
| `coordinateColumn_lift` | `SU2QuaternionCoordinateColumnLift.lean:292` | Actual column at N+i is the N-head lift of that at i. |
| `haarQuadratic` | `SU2QuaternionProductHeatPositive.lean:64` | H[W*f*lift(f)] on the original two ordered halves. |
| `heat_preserves_quadratic` | `SU2QuaternionProductHeatPositive.lean:202` | Derives the Gram insertion step from the actual heat factor. The general W positivity premise is the induction hypothesis. |
| `productHeat_quadratic_nonnegative` | `SU2QuaternionProductHeatPositive.lean:229` | Supplies that premise inductively for the actual full selected-pair product. |
| `productMap_nonnegative` | `SU2QuaternionProductHeatPositive.lean:243` | Pins the result to the literal original map and its output-coordinate convention. |
| `transferStep_eq_productMap` | `BF4ExactSlabFixedSpatialTransferPositive.lean:48` | Exact T=P composed with multiplication by FULL V. |
| `original_quadratic_pin` | `BF4ExactSlabFixedSpatialTransferPositive.lean:56` | Full V stays in both kinetic PSD arguments. |
| `transferStep_quadratic_nonnegative` | `BF4ExactSlabFixedSpatialTransferPositive.lean:67` | Actual interacting one-step quadratic for arbitrary supported signed inputs, without fringe independence. |

The degree-wise input is `character_haar_gram_of_unit_radii`,
`lean/YMGap/Continuum/SU2QuaternionSymmetricPowerKernelGram.lean:189`.
The final map pin is `productMap_pairing`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:247`.
The empty-product factorization is `haar_split_pairing`,
`lean/YMGap/Continuum/SU2QuaternionHaarMarkovContraction.lean:51`.
The support checks are retained before common padding is removed; the
original quaternion products themselves are never assumed commutative.

## Scope and remaining same-object joins

These are finite kinetic and original interacting quadratic results, not
new strict contraction estimates. At arbitrary cutoff V need not have a
proved positive density; the theorem does NOT separately establish that
H[V*f^2] is a positive state norm. At the existing admissible cutoff range
the previous density certificates remain separate available inputs.
No current Wilson-completion one-step positivity is yet concluded.

The parallel backward review identified one exact missing producer:
observed-window adjointness under reversal of its slice offsets. Writing
W_L(f,p) for the existing window message and ell(r)=H[V*r], its intended
identity is

    ell(W_L(f,p)*g) = ell(f*W_L(g,rev_L(p))).

This is a target formula, NOT a new declaration or assumed certificate.
Supported f,g,p and the full original kernel/action must be retained.
The following existing inputs were inspected:

| Existing input | Declaration and source |
| --- | --- |
| Whole-window Fubini for arbitrary signed, nonfactorized probe | `windowMessage_pairing`, `lean/YMGap/Continuum/SU2QuaternionHeadWindowContraction.lean:138` |
| Explicit finite block permutation under Haar | `quaternionHaar_reindex`, `lean/YMGap/Continuum/SU2QuaternionArbitraryHaarBlockReflection.lean:534` |
| Original kinetic symmetry | `kineticWeight_swap`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticSymmetry.lean:163` |
| One-transition weighted adjointness | `transferStep_weighted_symmetric`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97` |
| Two observed windows separated by one empty transition | `windowMessage_separated`, `lean/YMGap/Continuum/SU2QuaternionHeadSeparatedWindows.lean:108` |
| Positive original denominator | `terminalPair_positive`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:149` |
| Current original scalar for any window length | `originalWindowScalar_pin`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowTimeLimit.lean:123` |
| Limit equality under unequal padding | `originalJoint_padding`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonLimitStationarity.lean:96` |
| Current spatial limit | `jointLimits_spatial_converge`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonSpatialLimit.lean:85` |

**NOT FOUND:** that general window-reversal adjointness declaration in the
window-contraction, separated-window, transfer-symmetry and Wilson
window-reflection modules searched. No new bundle assumes it.

For a current intrinsic expression e of radius R, the reviewed source
geometry puts the one-step pair at offsets j and 2R+1-j. With the actual
observed message F_t from e, the balanced odd-window numerator should be
ell(F_t*T F_t), exactly the new finite positivity consumer. The displayed
intrinsic chart has 2R+2 transitions. Its finite diagonal trims to depths
(t,t+1), not (t,t); it must NOT be asserted equal to that symmetric
quadratic. The proposed route proves positivity on the balanced odd window
first and then uses `originalJoint_padding` with (left,right)=(0,1) in the
existing limit. The observation reversal, balanced numerator identity,
spatial-limit passage and current completion lift still need proofs.

The corresponding completed pin is `completedTime_correlator`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeForm.lean:137`. The older
plaquette-carrier positivity theorem is not a current-carrier bridge.
This direction needs no new ambient odd-slab gauge-change construction,
but it still needs the exact chain identities just listed.

The primary regulator-controlled strict bound for generated interacting
Wilson observations remains OPEN, as do changing-spacing survival,
physical generator calibration, full continuum QFT and every-group
construction. Finite PSD does not discharge any of those estimates.

## Verification boundary

Three final focused checks exited zero through `scripts/safe_lean_build.py`,
one worker at a time with an explicit 20 GiB limit. The column module passed
its first check; the product and transfer drafts required missing namespace
opens/import corrections only. Their mathematical statements and arguments
were unchanged. All ten printed gates depend only on allowed axioms
{propext, Quot.sound}; no sorry introduced or discharged.

The parent inspected all three full source files. Independent mathematical
reviews checked signs, lower/upper orientation, all support guards, arbitrary
signed inputs, repeated indices and full V retention. The backward reviewer
also exposed the unequal-boundary issue before any finite stationarity claim.

| Artifact | SHA256 |
| --- | --- |
| `/tmp/ym-coordinate-column-lift-20260917.log` | `f545610f377300a6f37ba1901a86a5154377edf3e2ecee8c53acc30769a32b19` |
| `/tmp/ym-product-heat-positive-retry2-20260917.log` | `13c62881907311195705c657b252df0cb0af7a17a3c6ecf6e667e00af76548e7` |
| `/tmp/ym-original-transfer-positive-retry1-20260917.log` | `5162339c7d0779e06c7772b0105b3760013d41884ae196fc9af14b9d07f050a0` |
| `SU2QuaternionCoordinateColumnLift.lean` | `1b50038befaa46f93e20bd890128f528b06956d226dee04d81a62cb673cf2eff` |
| `SU2QuaternionProductHeatPositive.lean` | `e9742db9c6c9462a4789ef26efd3684ae12a96acff2ed21774102148319ab2c6` |
| `BF4ExactSlabFixedSpatialTransferPositive.lean` | `f21eb5dce304eb7414b51533ef0bbde635e5bfcfe2f6176e1a795f006502887d` |

Three semantic-root imports added. Full-root/full-tree build, audit, guard
and progress runs were NOT performed. No canonical statement, analytic
guard, CI setting, resource policy or whole-project goal changed.
