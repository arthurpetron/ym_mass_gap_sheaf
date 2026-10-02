# Counted original Jacobi products and completed theta height

Date: 2026-10-02 UTC. The actual original Jacobi products now have a finite
cross-normalized comparison with a computed nome-gap-squared coefficient.
The original completed theta products also have a height comparison for
every strict nome. These are new estimates, not assumed analytic inputs.
The full heat-profile limit join, original Haar certificate and continuum
survival remain OPEN; the Clay target is not closed.

## Computed original factor count

For 16/17<=q<1, let h=1-q=p/d using its ACTUAL rational numerator and
denominator. `activeFactorStart` and `activeFactorCount` at
`lean/YMGap/Continuum/SU2HeatJacobiActiveFactorCount.lean:30` and line 34 compute

    start = floor((d+2p)/(4p))
    stop  = floor((3d+4p)/(8p))
    N     = stop-start.

Division with remainder proves that every retained ORIGINAL exponent
m=2(start+j)+1 satisfies 1/2<=m*h<=3/4. Lower and multiplicative Bernoulli
estimates use the original powers, not a replacement RG power. They give
1/4<=q^m<=2/3<=3/4. No counting or amplitude hypothesis is supplied.

| Declaration | Source | Checked estimate |
| --- | --- | --- |
| `activeFactorCount_two` | `lean/YMGap/Continuum/SU2HeatJacobiActiveFactorCount.lean:125` | N>=2. |
| `activeFactorCount_mass` | `lean/YMGap/Continuum/SU2HeatJacobiActiveFactorCount.lean:131` | N*(1-q)>=1/16. |
| `activeFactor_amplitude_bounds` | `lean/YMGap/Continuum/SU2HeatJacobiActiveFactorCount.lean:222` | Every actual retained geoAmp lies in [1/4,3/4]. |

The nome endpoint 16/17 is included. The endpoint 1 is excluded: the
construction requires the positive numerator of 1-q. The start and count
are data even outside that guard, but no block theorem is claimed there.

## Every original product factor is retained

Write P_q(x,M)=ThetaConv.Ppart q x M and A(x)=1+(1-x)/512. Both original
Euler prefactors are retained in each cross multiplication. The index count
is exactly min N(M-start), including empty and partly covered blocks.

`Ppart_partial_block_amplification` and `Ppart_block_amplification`,
`lean/YMGap/Continuum/SU2HeatJacobiProductAmplification.lean:237` and line 249,
prove, once M includes the whole block,

    [P_q(x,M)*P_(q*q)(1,M)]*A(x)^N
      <= P_q(1,M)*P_(q*q)(x,M).

These general block lemmas take finite amplitude bounds, not a global
product estimate. The next theorem supplies those bounds from the computed
original block. The spatial endpoints x=-1 and x=1 are included.

The literal quadratic multiplier is [floor(N/2)*(1-x)/512]^2.
`quadraticAmplification_le_power` at
`lean/YMGap/Continuum/SU2HeatJacobiProductAmplification.lean:291` proves it
is at most A(x)^N. For N>=2, N<=3*floor(N/2), hence the actual half-count
times 1-q is at least 1/48. This is `activeFactorHalfCount_mass`,
`lean/YMGap/Continuum/SU2HeatJacobiNearOneProductBound.lean:39`.

`Ppart_nome_gap_bound`,
`lean/YMGap/Continuum/SU2HeatJacobiNearOneProductBound.lean:69`, therefore proves

    (1-x)^2*P_q(x,M)*P_(q*q)(1,M)
      <= 24576^2*(1-q)^2*P_q(1,M)*P_(q*q)(x,M).

Its only parameter guards are 16/17<=q<1, -1<=x<=1 and
M>=activeFactorStart(q)+activeFactorCount(q). There is no supplied count,
global profile, heat-floor reciprocal or original-source assumption. The
coefficient 24576=48*512 is explicit; it is not uniform after deleting
the displayed nome-gap factor or replacing it by a physical mass.

## Original completed theta height

`bareTheta_doubled_height`,
`lean/YMGap/Continuum/SU2HeatJacobiHeightComparison.lean:159`, proves

    bareTheta(q,1,2N) <= 2*bareTheta(q*q,1,N)

for 0<=q<=1, including N=0 and the central term. The first pair is paid
by q<=1/2+q^2 and q^4<=q^2; for n>=1, both Gaussian exponents are at least
2(n+1)^2. The bound does not require a near-one nome.

`thetaProduct_squared_nome_height`,
`lean/YMGap/Continuum/SU2HeatJacobiHeightComparison.lean:188`, gives
Theta_q(1)<=2*Theta_(q*q)(1) for the EXISTING completed theta products,
for ALL 0<q<1. It uses the existing original Jacobi series/product equality
and Cauchy modulus to compare indices N and 2N. The order is the sound
eventual `CReal.leEv`, not the nontransitive one-slack approximation order.
This is a completed theta height, not the completed heat-profile bound.

## Remaining causal joins

Pass the actual finite cross-normalized product bound and the already
proved paired S bound through the ORIGINAL completions. Join the proved
height and the existing differentiated Jacobi identity to the SAME original
heat series. These limit/profile joins are not asserted by this milestone.

Even a pointwise heat bound is not the witness-bearing ORIGINAL Haar
`Certificate`. The algebraic square witness and explicit representation
cutoff error remain required by `affine_original_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHeatNomeComparison.lean:135`.
Its positive original source does not authorize using a signed centered
endpoint source. Whole-word cross-link cancellation and alignment relative
to OWN interacting variance remain separate inputs.

Backward from continuum survival, the original scalar sample estimates
still need useful changing-family costs and geometry/width control. Physical
mass calibration, the full SAME-theory OS/QFT construction, an acceptable
surviving Yang--Mills field and every compact simple group remain OPEN.
No displayed canonical chart claim changes.

## Verification

Four final focused checks passed, serialized through the monitored launcher
with one worker, a 20-GiB hard ceiling and 12-GiB OS reserve. All 14 public
axiom gates lie within {propext,Quot.sound}; the two executable count data
definitions use no axioms. Final logs have no errors, warnings or sorryAx.
Dynamic preflights had 82--85 percent pressure-free memory and zero swap.
No resource ceiling was raised; no broad root/tree/guard/audit was run.
Four aggregate root imports were registered, not aggregate-checked.

Earlier rejected checks included elaboration mistakes and a disallowed
`Classical.choice` dependency from arithmetic on a negated conjunction.
Two separate constructive Nat decisions remove that dependency while
preserving the theorem types. The repaired product and its downstream
nome-gap bound were independently rechecked. No rejected log is evidence.

Accepted logs:

- `/tmp/ym-jacobi-active-count-20261002-second.log`
- `/tmp/ym-jacobi-amplification-20261002-fourth.log`
- `/tmp/ym-jacobi-nearone-product-20261002-second.log`
- `/tmp/ym-jacobi-height-20261002-second.log`

| Artifact | SHA256 |
| --- | --- |
| Count source | `9a0649aaa317b88dc44430c6342b6df2482791c72d68655d1537d5d69f17d205` |
| Amplification source | `0589b4affb361b1dc0a6b5a5741ce9ffb7dbd55e951583a24c4cb62cf25091d5` |
| Nome-gap source | `c013cb79a6a3ba777434a03f5d54727780c87fca270fedeee99668c4dc319097` |
| Height source | `951942b162512055a27f4e56c0c1ab5bf7eaa41f83144d10ef92d28155e1e215` |
| Count log | `133a45b8213e90dd870b5ad791ac1ed5262680a7c211865464d8d5ac24f46718` |
| Amplification log | `5c214ebf32dca1bce69058bf1e0b984839b26cc2b5d0da90014b63312d1c4f6c` |
| Nome-gap log | `3f7b209ef3422f9c0e1d2568e7255da23e815de3407a51b68b63abe33130aa24` |
| Height log | `39bd8a5d46b513b7f1ccad27b2854866a6495386bd6ccc2e966c54199c2ae76d` |

Independent mathematical reviews passed count, product amplification,
the actual nome-gap join and the completed height. No new sorry, axiom,
classical dependency, weakened field, surrogate action or CI change remains
in the accepted increment. The canonical chart block is unchanged.
