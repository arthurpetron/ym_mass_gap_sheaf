# All-nome original block normalizer: proof and route audit

Date: 2026-09-27 UTC. Starting commit: `e296114`.
Scope: finite original SU(2) slab, rational `0<w<1`, heat cutoff
`K>=headCutoff(w)`, finite lists of physical links. No continuum claim.

## Route correction: reuse the existing obstruction

The preceding covariance-limit theorem still requires
`heatRemainderBound w < 1`:
`lean/YMGap/Continuum/BF4ExactSlabSmallNomeChebyshevCovarianceLimit.lean:121`,
`covariance_sq_geometric_bound`. Existing declarations already exclude that
premise on the supplied AF chart; no new obstruction wrapper is needed:

- `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:51`,
  `guard_forces_small_nome`: the guard forces `w<1/4`.
- `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:91`,
  `fine_guard_fails`, and `:97`, `blocked_guard_fails`: for a supplied
  `CubicMarginLaw`, positive chart points `g<=1/2` violate the guard on both
  the fine and one-step matched blocked nome.
- `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:37`,
  `remainder_cap_ge_two`: the returned cap is at least two at `w>=1/4`.
  This concerns the CAP, not a lower bound on the actual heat remainder.

Thus the fixed-small-nome estimate cannot simply be reused on that chart.
This neither constructs an AF law nor refutes one, and is not a Yang--Mills
counterexample. The distinct hypothesis `heatRatio(w)<=1/2` does not replace
the required remainder guard.

## Constructed objects and exact original-action identities

Let S be the selected physical-link list, A its incident-collar heat product,
B the detached original heat product, F the full original weight, and E_S
the existing finite-family original-coordinate Haar projection. The new
polynomials are `D=E_S(A)` and `N_p=E_S(p*A)`; the original coordinates
are not replaced or deleted.

| Declaration | Source | Exact content |
| --- | --- | --- |
| `familyProject_certificate` | `lean/YMGap/Continuum/SU2QuaternionHaarFamilyCertificate.lean:33` | Returns a positive certificate after family integration. |
| `familyProject_interval` | `lean/YMGap/Continuum/SU2QuaternionHaarFamilyCertificate.lean:47` | Preserves the supplied rational interval as data. |
| `familyProject_selfAdjoint` | `lean/YMGap/Continuum/SU2QuaternionHaarFamilyCertificate.lean:59` | Haar self-adjointness of E_S for both arbitrary inputs. |
| `normalizer`, `insertedNormalizer` | `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:64`, `:67` | Actual D and N_p, not assumed analytic inputs. |
| `normalizer_independent`, `insertedNormalizer_independent` | `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:81`, `:86` | Independence of every selected original coordinate. |
| `full_marginal_pin` | `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:101` | Coefficient identity E_S(F)=B*D. |
| `full_inserted_marginal_pin` | `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:110` | Coefficient identity E_S(p*F)=B*N_p. |
| `full_insertion_pin` | `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:125` | Full Haar integral of p*F equals that of B*N_p. |
| `full_test_pin` | `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:136` | H((r*p)*F)=H((r*N_p)*B) for selected-coordinate-independent r. |
| `normalizer_certificate` | `lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:153` | Constructed positive certificate for D. |

Empty and repeated selected-link lists are allowed. Physical membership is
explicit in the marginal/test/certificate theorems. These identities are
unnormalized polynomial/Haar statements, not an already constructed completed
conditional expectation.

## Quantitative bounds and their scope

For s selected links, the explicit coefficients are

```
L(w,s) = min(headFloor(w),1)^(6*s)
U(w,s) = (1+prefixCap(w))^(6*s).
```

Sources: `blockLower`, `blockUpper` at
`lean/YMGap/Continuum/BF4ExactSlabBlockComparisonConstants.lean:36` and `:39`;
`localFloor`, `localCap` at
`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:42` and `:43`.
Both coefficients are positive (`blockLower_positive`, `:41`, and
`blockUpper_positive`, `:46`, in the comparison-constants module).

`normalizer_weighted_bounds` at
`lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:164` proves

```
L * H(q*B) <= H((q*D)*B) <= U * H(q*B)
```

for a supported q WITH a supplied `Certificate` of positivity. It does not
assert positivity of arbitrary supported q. Taking q to be a square covers
every supported polynomial vector, including arbitrary spectator dependence.
The proof moves E_S onto q*B using self-adjointness, preserves its certificate,
and applies `atMostBlockFaces_bounds` at
`lean/YMGap/Continuum/BF4ExactSlabBlockComparisonConstants.lean:66`.
`collar_weighted_bounds` at `:102` also compares the original full form to B.

`backgroundData` at
`lean/YMGap/Continuum/BF4ExactSlabBlockNormalizerMap.lean:43` keeps all original
coordinates but uses weight B, NOT F. On this dense background carrier,
`normalizerMap` (`:55`) multiplies by D. Its proved statements are:

- `normalizerMap_sub` (`:62`) and `normalizerMap_symmetric` (`:72`): difference
  compatibility and symmetry for the actual background form.
- `normalizerMap_form_bounds` (`:81`): `L*B(a,a)<=B(a,Ma)<=U*B(a,a)`.
- `normalizerMap_norm_upper` (`:98`) and `normalizerMap_norm_lower` (`:114`):
  `L^2*B(a,a)<=B(Ma,Ma)<=U^2*B(a,a)`.

All these bounds hold for every rational `0<w<1` and late cutoff, without the
small-nome guard. L/U has explicit nome and block-size dependence. Absence of
extent/cutoff arguments is not a coupling-uniform or scaling gap claim. These
are invertibility inputs, not a proved inter-block angle estimate.

## Reused algebra and exact remaining consumers

The existing division-free identities are not missing:
`familyWeightedResidual`, `familyProject_weightedResidual_zero`, and
`familyWeightedResidual_orthogonal` at
`lean/YMGap/Continuum/SU2QuaternionHaarFamilyProjection.lean:125`, `:151`,
and `:174`. They do not construct an inverse or completed interacting block
projection. The current interacting projection
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:220`,
`conditionalProjection`, is a one-link construction.

Next unsupplied object: an actual multi-link inverse with explicit polynomial
approximation/Cauchy moduli, followed by the block conditional projection on
the SAME original full-action completion. The existing one-link pattern is
`approximationCutoff` at
`lean/YMGap/Continuum/BF4ExactSlabStarInverseApproximation.lean:241` and
`inverseState` at
`lean/YMGap/Continuum/BF4ExactSlabStarCompletedInverse.lean:107`.
Reusable geometric-modulus data already exist in `geometricCutoff` at
`lean/YMGap/Continuum/PositiveContractionResidual.lean:119`.
The new form/norm bounds are concrete inputs to this construction, and
`full_test_pin` is the original-action identity its testing law must consume.

The essential analytic estimate remains useful signed inter-block control
outside the near-Haar guard on a justified scaling family. None of the new
declarations proves it. No analytic field assuming this conclusion was added.

The boundary/volume join remains distinct. The scalar selected-face partition
floor is `(headFloor w)^ids.length`, not a small-nome floor:
`partitionFloor` at
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetReciprocal.lean:40`.
Exact insertion identities exist (`numerator_append_face`, `partition_append_face`
at `lean/YMGap/Continuum/BF4ExactSlabFaceInsertionDeterminant.lean:44`, `:53`),
but `finite_response_bound` at
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:209` still consumes
the signed response estimate with its two partitions. Full-face clustering
alone does not supply a theorem for those intermediate selected-face measures.

## Verification and unchanged frontier

Final versions of all four new modules passed focused serialized checks through
`scripts/safe_lean_build.py`, one worker with a 20 GiB ceiling. Printed axiom
gates: family certificates 3, block constants 6, normalizer 16, normalizer map 7;
all 32 lie within `{propext, Quot.sound}`, with no `sorryAx`. Sol/Luna worked on
bounded independent proofs/reviews; compilers did not run concurrently.

No new sorry, axiom, analytic bundle, weakened canonical field or chart-marker
change. Root imports were registered, but no root/full-tree build, full audit,
guard, progress-metric run or CI was performed. The canonical chart is not
reprinted. Same-theory thermodynamic/scaling passage, nontrivial survival,
OS/QFT reconstruction, positive physical Hamiltonian mass and every compact
simple group remain open.
