# Original conditional ratio joins the finite signed-energy split

Whole-project goal: constructive, Mathlib-free Lean continuum Yang--Mills
on R^4 for every compact simple group, with nontrivial SAME-theory QFT,
an isolated vacuum and finite positive physical mass gap. That goal is OPEN.

## New proved join

Keep the ORIGINAL transfer T, spatial action V and ell(p)=H[V*p]. Set

    A=g_(n+t), b=T^t(g_n*psi), n+t>=1, phi_k=G_k*b,
    u=A*phi_k, e=b-u, s=b+u,
    Z0=ell[A^2], Z1=ell[A*T A], B=ell[b^2],
    C=kineticCap(w,width)*ell[1], rho=mixRate(w,width).

The existing positive edge energy at g=1 gives
ell[f*T f]<=ell[(T1)*f^2]. The original upper transfer certificate at 1
then gives ell[f*T f]<=C*ell[f^2]. Product-heat Cauchy--Schwarz, with
the full V*f and V*g insertions, yields

    ell[f*T g]^2 <= C^2*ell[f^2]*ell[g^2].

No spatial floor or comparison to an unweighted norm is used. The
reciprocal multiplier square certificate constructs ell[u^2]<=B.
Together with the checked ratio reconstruction and same-weight triangle,

    ell[e^2]<=rho^(2*k)*B, ell[s^2]<=4*B.

The COMPLETE signed multiplication cost is

    M_k=Z1*ell[e*s]-Z0*ell[e*T s],
    abs(M_k)<=2*rho^k*(Z1+Z0*C)*B.

There is no assumption on the favorable sign of M_k or its individual
telescoping summands. Rational square reflection includes zero ceilings.

The existing exact split only requires support, not the exact identity
b=A*phi. Its direct application therefore gives

    abs(D(A,b)-(Z0*energy(A,phi_k)+boundaryDrift(A,phi_k)))
      <= rho^k*Cerr,
    Cerr=2*(Z1+Z0*C)*B>=0.

The explicit absolute-tolerance onset is

    geometricCutoff(rho,Cerr,epsilon).

Every k at or above it has error at most epsilon. Zero source norm,
zero contraction rate and k=0 are included. The depth guard excludes
n=t=0; t=0 with n>=1 is permitted.

## Declaration evidence

| Declaration | Source | Role |
|---|---|---|
| `transferWeightedCap` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferWeightedBound.lean:54` | Literal C=kineticCap*ell(1). |
| `transferWeightedCap_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferWeightedBound.lean:57` | Positivity from the original certificates. |
| `transferStep_weighted_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferWeightedBound.lean:82` | Original transfer bilinear form, all nonnegative nomes/cutoffs. |
| `transferStep_weighted_quadratic_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferWeightedBound.lean:130` | SAME V-weighted finite quadratic ceiling. |
| `transferStep_weighted_mixed_square_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferWeightedBound.lean:150` | SAME original mixed continuity bound. |
| `weightedMass_pair_square_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferWeightedBound.lean:178` | SAME spatial norm's sharp Cauchy--Schwarz. |
| `blockEnergyErrorCoefficient` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean:174` | Computed actual error coefficient. |
| `blockEnergyErrorCoefficient_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean:181` | No added positivity premise on this coefficient. |
| `blockConditionalRatio_signedCost_abs_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean:200` | Full original signed remainder paid. |
| `blockConditionalRatio_energy_error_abs_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean:302` | Actual ratio inserted into the original split. |
| `blockEnergyErrorCutoff` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean:332` | Computed Type-valued finite cutoff. |
| `blockConditionalRatio_energy_error_tolerance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean:339` | Actual all-later absolute tolerance. |

Inputs are `energy_nonnegative` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:308`,
`transferStepUpperCertificate` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:223`,
`kineticPair_cauchySchwarz` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatDualForm.lean:127`,
`multiplierSquareCertificate` at
`lean/YMGap/Continuum/QuaternionHaarPositiveWindowInverse.lean:186`,
`blockConditionalRatio_reconstruction` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:281`,
and `clearedRayleighCost_split` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:214`.

## Correction and remaining backward input

The preceding ratio audit erroneously claimed that `clearedRayleighCost_split`
requires b=A*phi exactly. Its actual two hypotheses are support of b and
A*phi. The old audit is explicitly corrected, not silently relied upon.

The new join is finite at original parameters. rho depends on nome and
width; C names cutoff through ell(1); Cerr also retains terminal depth,
block length, source and actual partitions/norm. The absolute cutoff is
NOT uniform on a changing family. No old chronological center is moved.

The unpaid mathematical input is a useful bound on the actual combination
Z0*energy(A,phi_k)+boundaryDrift(A,phi_k), relative to Z1*B, with this
reconstruction error paid on the justified changing family. The original
cleared angular score alone does not give that estimate. The direct
macroscopic-response alternative remains open as well. No canonical field,
guard or `sorry` was changed, and no displayed continuum/physical/OS/group
claim changed state. The canonical chart is unchanged and was not reprinted.

## Verification boundary

Two serialized focused checks, one worker, hard 20 GiB worker ceiling and
12 GiB OS reserve, after fresh process/memory/swap preflights:

- `/tmp/ym-original-transfer-weighted-bound-20261003-b.log`: exit 0,
  six public gates, each exactly `{propext, Quot.sound}`.
- `/tmp/ym-original-block-conditional-energy-20261003-b.log`: exit 0,
  six public gates, each exactly `{propext, Quot.sound}`; one harmless
  unused-private-argument warning (`ha`).

Independent Sol read-only review confirmed the twelve gates, same-object
pins, signed orientation, zero cases and parameter-dependence boundary.
No classical axiom, `sorryAx` or custom axiom is reported. No full root,
full-tree build, aggregate audit, broad test or guard suite was run.
Root imports are registration only. CI remains off.

Source SHA-256 at accepted check:

- `BF4ExactSlabFixedSpatialTransferWeightedBound.lean`:
  `b0ca2a29cd4d73da3802e77ada36797dad08e5df4261794266b4bc4bb9d1d09f`.
- `BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean`:
  `65df986b39ce86a4df71d20c773b63db694a049400fa7628e4cc7fbb616f56fe`.
