# Bent cube signed gain diagnostic

The complete OWN-centered signed gain has a favorable exact finite polynomial
certificate candidate on the six-face SU(2) cube at representation cutoff one
and terminal depth zero. The computed degree-68 polynomial P satisfies
P(r) >= (3/2)*r^10 for 0<r<=1/8. This is untrusted exact-arithmetic evidence,
NOT a new kernel-checked Yang--Mills theorem. The original cube matrix pin,
later-cutoff/depth passage and growing-family survival estimate remain OPEN.

## The retained finite action and center

The new producer reuses the unchanged signed Haar contractions of
`computations/cube_cutoff_one_checkpoint.py:79` (`edge_tensor`) and `:109`
(`haar_loops`). Its original spatial matrix is `spatial_matrix:144`;
`transfer:176` retains T=D*A, not a heat-bath generator. With r=w^3,
V is the product of ALL SIX factors 1+2*r*chi_face. The 32 cycle states are
not restricted to the six plaquettes.

`computations/cube_cutoff_one_signed_gain.py:159` (`bent_loop`) selects faces
0 and 2 and their six-link outer boundary F, cycle mask 318. This bent loop
is a diagnostic observable, NOT a replacement for the existing dyadic square
anchor. `insertion_matrix:170` computes the full insertion
M_F[i,j]=H[W_i*V*F*W_j]; projecting multiplication by F before retaining V
would discard channels and is not done here.

At terminal depth n=0, g_0=1. Write U=T1, and let the weighted pairing be
ell(p)=H[V*p]. `compute_pilot:226` computes

```text
Zodd = ell(U)                    Zeven = ell(U^2)
c    = ell(U*F) / Zodd           b = T(F-c)
C1   = ell(U*(F-c)*b)            C2 = ell(b^2)
a    = r^6                      G = C2-a*C1.
```

The mean belongs to the actual odd marginal V*U/Zodd. The odd and even
partitions are distinct and are never cancelled as equal. The point
w=1/2, r=1/8 gives 2^-30 < G < 2^-29 with this center; the much larger
uncentered gain is retained only as a regression check, not a substitute.
Every face factor at this point has the separate pointwise floor 1/2.

The intended ORIGINAL finite consumer is `commutatorGain`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredCommutatorGain.lean:97`),
whose centered message is defined at `:88`. The existing completed pin is
`gainLimit_completed_pin`
(`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:131`). Neither
has been instantiated with this computed matrix: that requires the source
identification and later-cutoff/depth work recorded below.

## Complete signed coefficient estimate

`polynomial_matrix:94` recomputes the rational coefficient matrices A(r) and
M_F(r) from the same guarded Haar contractions. There is no cached matrix
trust path. `compute_polynomial_pilot:137` keeps the mean numerator N and
odd partition Z as polynomials, computing

```text
U  = D*A*e0                    Z = e0^t*A*U
N  = eF^t*A*U                  bZ = Z*D*A*eF - N*U
P  = bZ^t*A*bZ - r^6*(Z*U^t*M_F*bZ - N*U^t*A*bZ)
   = Z^2*G.
```

The degree is 68, coefficients below degree ten vanish, and c_10=2.
The ENTIRE signed coefficient remainder has the exact majorant

```text
S = sum(i>10, abs(c_i)*(1/8)^(i-10))
  = 624923141201848467490810145716514015485995116321599
    / 1683649886205200161770644927289158038643634289508352
  < 1/2.
```

Thus coefficient algebra gives P(r)/r^10 >= 2-S > 3/2 throughout the stated
interval, not merely at sampled points. The leading coefficient comes from
the two lower-perimeter plaquette channels; the complete remainder and
OWN-mean corrections were computed, not dropped into an unestimated O term.
The reusable scalar interval compiler is already
`lean/YMGap/Constructive/QPolyWeightedL1.lean:42`
(`abs_eval_le_weightedL1`). No new conditional normalization or polarization
interface is needed. This turn did NOT instantiate that compiler in Lean or
prove the missing original-matrix identity.

The full exact rational coefficient list, messages, point gain and source
hashes are saved in
`audits/CHECKPOINT-CUBE-BENT-SIGNED-GAIN-2026-10-03.json`.
Read its large integer pairs without floating-point conversion.

## Original transfer boundary

Existing unguarded original-action identities support the intended bridge:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:87`,
  `original_transfer_haar_active`, gives tested ORIGINAL transfer reduction.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:69`,
  `marginal_mean_active`, retains both ORIGINAL terminal messages.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeFaceGeometry.lean:54`,
  `active_index_iff`, identifies the active indices. At width two there are
  24 active kinetic links, of which twelve belong to the cube core; the
  other twelve require an explicit independence/heat-vacuum elimination.

These declarations do NOT pin the 32-state orthonormal basis, its heat-image
closure, or the computed matrix to the original coordinate carrier. That
same open source pin was already recorded in
`audits/CHECKPOINT-01-NORMALIZED-PAIR-2026-09-18.md` and `lean/SORRY_LEDGER.md`.
No surrogate matrix has been silently substituted into a Clay-facing field.

The pilot also FAILS the existing head-cutoff guard:
`BF4ExactSlabRetainedHeatHeadComparison.headCutoff`
(`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55`) is at
least bandSize, by `bandSize_le_deficitCutoff`
(`lean/YMGap/Continuum/BF4ExactSlabJacobiDeficitInterval.lean:72`). Definitions
`bandSize:49` in that file, `tailCutoff`
(`lean/YMGap/Continuum/BF4ExactSlabAllNomeTailInterval.lean:102`),
`spacingLabelCutoff`
(`lean/YMGap/Continuum/SU2PointwiseHeatSpacingCompletion.lean:71`) and
`powBaseCutoff` (`lean/YMGap/Continuum/HeatKernelConvGen.lean:266`) give
headCutoff(1/2)>=17. K=1 cannot enter those guarded consumers. Direct finite
positivity is a different statement, not a waiver of the guard.

## Verification and next mathematical join

The focused twelve-test run passed in under one second. A separate complete
producer run took 0.860 seconds with 30,720,000 bytes peak RSS (Darwin), one
NumPy thread, 85 percent system-free memory and zero swap at preflight.
The degree cap is 80; existing degree/index/int64 and tensor intermediate
guards were unchanged. No Lean build, full audit, new axiom, sorry, canonical
field, CI or chart change occurred.

Independent review verified the stored integer data and hashes, exact tail,
floor>3/2, P(1/8)=Zodd^2*G, distinct partitions and OWN-centered messages.
The initial `/usr/bin/time -l` wrapper could not read a sandboxed clock
counter after eight tests passed; the final plain twelve-test command exited
successfully. Resource figures above use the separate producer run.

FORWARD: pin only the original messages U=T1, B=TF and their seven required
scalar moments, reusing the existing local tensor results; a complete
32-state operator model is not necessary for this gain evaluation. The
moments are Z=ell(U), N=ell(U*F), ell(B^2), ell(U*B), ell(U^2), ell(U*F*B),
ell(U*F*U). They reconstruct the same cleared polynomial directly:

```text
P = Z^2*ell(B^2) - 2*N*Z*ell(U*B) + N^2*ell(U^2)
    - a*(Z^2*ell(U*F*B) - N*Z*ell(U*B)
         - N*Z*ell(U*F*U) + N^2*ell(U^2)).
```

This proposed smaller source-identification task is not yet proved. Then
control how the favorable channels and COMPLETE signed remainder change at
later cutoffs and terminal depths. Do not iterate fixed-small-nome tests as
a substitute for that mathematical passage.
BACKWARD: retain the already checked demand for a SAME macroscopic response
ratio and relative three-norm comparison on a justified growing physical
family. This small fixed-cube bound supplies neither. Its observable, nome
range and cutoff must not be silently promoted to the dyadic square route,
continuum survival, physical mass, full QFT structure or every-group target.
