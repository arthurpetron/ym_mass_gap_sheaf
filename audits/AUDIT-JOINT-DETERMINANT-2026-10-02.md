# Exact signed determinant for the original two face margin

The original interacting covariance and COMPLETE mixed temporal energy now
share one division-free signed two-copy pairing. This exactly resums the
previous signed heat/cubic/cutoff corrections. It retains those effects,
not a favorable sign or estimate. The existing finite reference margin is
the direct consumer; no positive scaling margin or continuum result follows.

Three warning-free focused checks passed. All eighteen printed axiom reports
contain only {propext,Quot.sound}. Independent Sol mathematical review passed.
Luna matched all hashes, declaration anchors and actual gate outputs, and
confirmed that every canonical chart fence is byte-identical to the prior commit.
No new analytic premise or canonical frontier field was introduced or changed.

## Mathematical argument

Let W be the ORIGINAL marginal V*g_n*g_(n+1), Z its original odd partition,
and a=P_fringe(V*g_n) the projected COMPLETE endpoint source. The latter is
the existing exact inactive-source reduction for padded observables, not an
independence assertion about the source. Let k be the FULL original product
heat kernel, f and g the two signed singleton spatial spans.

A is the actual p-face block list. B is ALL complementary slice blocks,
not just the four q-face blocks. A++B is a permutation of the complete block
range. Literal link-disjointness proves g independent of A; f is independent
of B. Neither W nor a is assumed independent of either side.

For a supported one-copy polynomial X, define the crossed determinant

```
D_X = X*R_(A++B)(X) - R_A(X)*R_B(X).
```

On the actual Haar carrier, complete coverage identifies R_(A++B)(X) with
the full upper copy. The same coverage identifies the replicated test
differences with the actual full slice jumps Δf and Δg. Partial swaps preserve
EVERY factor of k, whether its block lies in A or not. Consequently:

```
H[k*D_a*Δf*Δg] = 2*Z*E_mix
H[D_W*Δf*Δg]   = 4*Z^2*Cov_W(f,g).
```

E_mix is normalized energy([p,q]) minus the two singleton normalized energies,
all at the SAME original cutoff/depth. The Dirichlet factor two cancels the
polarization factor two. Cov_W uses BOTH original means, not means under a*a.
No Taylor truncation is used in these identities.

Set S=c*D_W-Z*k*D_a and J=Z*(2*c*Cov_W-E_mix). Exact linearity gives

```
jointPairing = H[S*Δf*Δg] = 2*Z*J
            = 2*Z^2*(referenceMargin([p,q])
                       - referenceMargin([p]) - referenceMargin([q])).
```

The final line uses the EXISTING original reference margin, coefficient
function and schedule K=headCutoff(w)+stage. It returns no successful checker
input. The source-square law, an auxiliary Haar norm, or a different operator
is never substituted for the original interacting covariance.

## Source and consumer

| Declaration | Source |
|---|---|
| `productHeat_partialSwap_mask` | `lean/YMGap/Continuum/SU2QuaternionPartialSwapHeat.lean:97` |
| `fourEnergy_full_pin` | `lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean:105` |
| `weighted_fourEnergy_pin` | `lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean:116` |
| `heat_fourEnergy_pin` | `lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean:141` |
| `covariance_fourEnergy_pin` | `lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean:222` |
| `sourceEnergy_jump_pin` | `lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean:246` |
| `sourceEnergy_mixed_pin` | `lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean:310` |
| `covariance_numerator_pin` | `lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean:345` |
| `singleton_spectator_independent` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:97` |
| `disjoint_observable_independent` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:104` |
| `original_mixed_jump_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:153` |
| `original_energy_determinant_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:195` |
| `original_covariance_determinant_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:213` |
| `signedDeterminant`, `jointPairing` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:238`, `:247` |
| `joint_pairing_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:258` |
| `reference_pairing_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean:310` |
| Existing `reference_margin_difference_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointMargin.lean:668` |

The physical energy/joint consumers retain 0<w<1, strict spatial padding,
physical face membership and the original head cutoff. The determinant
energy/joint consumers additionally require literal link-disjointness.
There is no new sufficientCutoff guard, source-factorization hypothesis,
eigenvector assumption or claim of uniformity over changing parameters.

## Verification

All commands were serialized through the monitored launcher, one 20-GiB capped
worker, unchanged 12-GiB OS reserve. All accepted commands returned EXIT 0:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/SU2QuaternionPartialSwapHeat.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionPartialSwapHeat.olean \
  --log-file /tmp/ym-partial-swap-mask-accepted-20261002.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionHeatFourCopy.olean \
  --log-file /tmp/ym-heat-four-copy-accepted-20261002.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDisjointFaceJointDeterminant.olean \
  --log-file /tmp/ym-joint-determinant-accepted-20261002.log
```

The swap module reports its existing theorem and new arbitrary-mask theorem;
the generic module reports seven public pins; the physical module reports
seven public theorems and the two computed polynomial/pairing definitions.
Every observed gate is {propext,Quot.sound}; no sorryAx, choice, native
evaluation or added axiom. Draft failures are not acceptance evidence.
Explicit local opacity removed an elaboration timeout without raising limits.

SHA256 of the accepted sources and logs:

| Artifact | SHA256 |
|---|---|
| Partial-swap source | `f8b305a15bd56406e76340fb10ec3f95e4c017d99f13670fb5f628eefb8e0bbe` |
| Generic four-copy source | `d5fdfdd93f54f8b8b76e877f6feae475e76002d85cdef28e503ff8cca4cbfe7f` |
| Physical determinant source | `fadda25fb258bc0dd6776413092e1765ab9818c6037c3902fa8a7da46282d6a3` |
| Partial-swap accepted log | `90d0db99d5ca04a1211b4758de8958d5e8fea8d65e6f272d995dd75c4ddf80ee` |
| Generic accepted log | `10523ef389e24613b9e03f50c617f73ee4937b015f00affc71a7abdde6902fdb` |
| Physical accepted log | `38fa9fd85718631fc2e44a662600fac93b9369381ab857e1c31a26bbfc25b77d` |

Preflight found no competing Lean/Lake/test/runner process. Memory-pressure
free percentage was 86 before checks and 85 after; postcheck swap usage was
zero. No heavy numerical evaluation or broad build/audit/guard/metric ran.
One root import is registered; the root aggregate and full tree were NOT
checked. CI and the canonical chart block are unchanged.

## Remaining estimate

The exact resummation replaces separate Taylor accounting with the SAME
signed determinant/jump pairing. Useful control of that pairing and diagonal
margins must still exceed the common cutoff allowance on a JUSTIFIED changing
family. Haar Cauchy--Schwarz alone supplies absolute upper control, not the
positive signed slack required by the finite checker. At fixed K, taking
w toward one retains a mode projector, not identity on an arbitrary source;
these identities assert no automatic small-h scaling estimate.

No favorable original instance, spatial/spacing rate, every-state scaling
decay, nonzero continuum survival, physical mass, full QFT or every-group
realization follows. The Clay goal remains OPEN. No exact displayed chart
claim changed; no ASCII reprint is justified.
