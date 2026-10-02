# Original Wilson energy with Haar cutoff control and retained gain

## Result and consequence for the proof path

The actual Haar-norm omitted-mode bound is now integrated through the COMPLETE
cancelled original energy remainder, retaining the negative completed square
and its EXISTING computed projection gain. A witness-bearing range certificate
for the OWN-centered fundamental loop eliminates the raw fourth moment with
constant sixteen, independent of perimeter. This removes that independent
moment obligation from the energy budget; it does not prove useful control of
the remaining signed debt on a physical scaling family. No Clay node closes.

Let h=1-w, rho=w^((K+1)*(K+3)), Z be the ORIGINAL positive partition,
q=P_fringe(V*g_n), psi=f-OWNmean, B=H[(q*psi)^2]=Z*OWNVar-C,
and G the EXISTING original-partition-normalized projection gain. With
0<w<1, headCutoff(w)<=K, sufficientCutoff(w)<=K and side(scale)<width,
the actual original fundamental growing-loop energy satisfies

    E <= [12*side*h + h^2/8 + 9*rho]*OWNVar
           + [h^3*(cubicMixedBudget+cubicDiagonalBudget)
              + rho*H[q^2]/2 + h^3*angularPairBudget
              - (h^2/8+9*rho)*C]/Z
           - h*OWNWard - (h^2/2)*G.

The factor 9 is exactly 16/2+1. C and the complete original Ward insertion
retain their signs; neither is assumed favorable. The two cubic costs and
the angular-pair cost are unchanged. Raw H[q^2] is NOT Z. No estimate is
claimed numerically smaller than every old budget.

## Exact declarations and causal joins

| Declaration | Source | Content |
| --- | --- | --- |
| `haarSquareCeiling` | `lean/YMGap/Continuum/SU2QuaternionCompleteRemainderHaarProjection.lean:36` | New actual cutoff-norm ceiling, retaining cubic/angular costs |
| `completeRemainder_le_haar_completedSquare` | `lean/YMGap/Continuum/SU2QuaternionCompleteRemainderHaarProjection.lean:44` | Actual error bounded before retaining the negative completed square |
| `completeRemainder_le_haar_projectionCeiling` | `lean/YMGap/Continuum/SU2QuaternionCompleteRemainderHaarProjection.lean:105` | SAME completed square pays the EXISTING regularized gain |
| `paddedSquare_mean_square_le_four` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredFourthMoment.lean:53` | Mean squared <=4 under the SAME original marginal |
| `paddedSquare_centered_squareBound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredFourthMoment.lean:76` | Type-level square certificate with cap16, independent of perimeter |
| `paddedSquare_centered_fourth_le_sixteen_second` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredFourthMoment.lean:113` | H[q^2*psi^4]<=16H[q^2*psi^2] for EVERY supported q |
| `haarVarianceRate` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:86` | Computed h^2/8+9*rho |
| `haarCenteredDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:101` | Remaining complete numerator costs and signed centering correction |
| `normalizedHaarCenteredDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:110` | Division by SAME positive original Z |
| `completeHaarCenteredDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:115` | Complete OWN Ward insertion still subtracted |
| `paddedSquare_haarCeiling_le_varianceDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:131` | Fourth moment absorbed into SAME variance with C retained once |
| `paddedSquare_remainder_haar_projection_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:214` | Original centered remainder normalized with existing gain |
| `paddedSquare_energy_haar_projection_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:254` | Actual original energy consumer displayed above |

The generic proof uses `sourceError_le_haar`
(`lean/YMGap/Continuum/SU2QuaternionCyclicOmittedOperator.lean:300`), not an
assumed comparison between the new mixed norm cap and an old absolute budget.
The literal loop cap is `paddedSquareSquareBound`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:99`).
The OWN mean uses the original marginal certificate and positive mass;
constructive variance nonnegativity bounds its square. Adding two square
certificates with cap4 constructs cap16; insertion of the supported square
(q*psi)^2 and exact coefficient recoding gives the fourth-moment inequality.
No exponentially growing monomial-L1 `polynomialCap` is used.

The exact signed B pin remains `centered_sourceSquare_pin`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:159`).
The gain is `normalizedProjectionGain`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareProjectionGain.lean:201`), not a
new gain or an eigenvector assumption. Its support proofs are propositionally
irrelevant; source, carrier, observable, OWN mean and Z are unchanged.

## Remaining analytic input

OPEN: a useful bound for raw H[q^2], complete cubic/angular/Ward debt and
SIGNED C against OWN variance, together with the retained gain, on a
physically justified changing family. G may vanish. The explicit coefficient
still depends on coupling, cutoff and growing perimeter; it is not claimed
spacing- or volume-uniform. Physical spacing/mass calibration, nonzero
continuum survival, full same-theory QFT structure, every compact simple
group and the Clay theorem remain OPEN. No frontier field is weakened.

## Verification boundary and machine safety

Three focused checks returned exit zero, warning/error-free. Their printed
gates are 3+3+7=13; all lie within {propext,Quot.sound}, and `haarVarianceRate`
is axiom-free. Independent Sol mathematics/source/log review passed. No new
sorry, axiom, classical premise or assumed analytic bound was introduced.
One downstream root import transitively includes all three new modules.
The root itself, full-tree build/audit/guard and progress metric were NOT run;
the automatic axiom baseline was not regenerated. CI remains manual-only.
Canonical chart fenced blocks are unchanged; no ASCII reprint.

Accepted checks used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20`, with serialized verification and the 12-GiB OS
reserve. Dynamic preflight found no competing compiler, runner or pytest
process; free pressure capacity was 85--86%, with zero swap. The first short
draft check inadvertently inherited the launcher's 32-GiB default and failed
on proof errors. It ended before retry; every accepted check explicitly used
20 GiB. The first run is NOT claimed to have met the 20-GiB invariant.

## Source and accepted log hashes

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionCompleteRemainderHaarProjection.lean` | `07c4e6b5d75dc09c953f05154caa40dcf80b4d09b1405cfcd048b925ee6dc18f` |
| `BF4DyadicWilsonSquareCenteredFourthMoment.lean` | `ad0358d37ea85c88fed10624871ddba0dac3cf81c3f97f1dd5bbf4ffd084262c` |
| `BF4DyadicWilsonSquareHaarProjection.lean` | `760f9c25f25642a19d98e9aa05e3545bb95c67c8171e30aa53e91151e92ac6d0` |
| `/tmp/ym-haar-projection-20261002-accepted.log` | `a9f7b623a5615f0019fd08bd8f9471e090ca8003884a5a30d6e2229c560a5f1f` |
| `/tmp/ym-centered-fourth-20261002-initial.log` | `14d05c8ed356c2cdab5dddb2d88c57689aafd8aab7e792ab7efae483cbf8ecfb` |
| `/tmp/ym-original-haar-projection-20261002-accepted.log` | `f1ccb2de0b151b900f950ebbbe802c6277d317fd03b538a5b9fbaad3ae197b52` |
