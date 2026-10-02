# Both chord moments paid in the original filtered variance ceiling

The complete original signed-source ceiling now has both chord moments
bounded explicitly against its SAME even partition. Its OWN finite odd
variance, original odd mean and three retained corrections remain.
This is a quantitative finite estimate, not the useful relative budget
and reserve required along a justified continuum scaling family.

## Constructed whole word interval

For the actual supported Haar-unit words p,q, let r=|p-q|^2. The exact
parallelogram identity gives 4-r=|p+q|^2 under every Haar insertion.
Together with the positive four-square norm of p-q, this constructs

    Interval r 4.

This is `chord_interval`,
`lean/YMGap/Continuum/QuaternionHaarChordalInterval.lean:103`.
The witness is Type-valued and uses the actual Haar-unit equality at BOTH
ends, not a pointwise substitution. The cap is independent of word length.
`wordChordal_interval`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMixedDepthChordalInsertion.lean:73`,
instantiates it for the literal original lower and upper ordered words.

## Original mixed chord producer

The existing matched quadratic estimate bounds the actual chord in
window(n,1,n) by a0=6*(1-w)*length^2 after its kinetic onset. The cap-four
interval transports it to window(n,1,n+1) through the existing original
right common-tail comparison. Clearing only the latter's positive mass gives

    L <= [a0+8*mixRate(w,width)^n]*E,

where L=mixedChordMoment and E=evenPartition. This is
`mixedChordMoment_nome_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMixedDepthChordalInsertion.lean:117`.

The theorem explicitly requires headCutoff(w)<=K, 1<=K,
sufficientCutoff(w)<=K, and the actual links to be active. The old matched
API uses cutoff K0+1; the proof uses K0=K-1 and proves K-1+1=K. No
kinetic onset is inferred from a quartic onset, and no same-source
quadratic order inequality is applied to different terminal sources.

The SAME mixedQuarticDepthCutoff already pays 32*mixRate^n<=epsilon,
so it also pays this smaller error. Thus

    L <= [a0+epsilon]*E.

This is `mixedChordMoment_nome_tolerance_bound` at line 148. Its
coefficient has explicit nome and length dependence. The depth onset
depends on nome/width/tolerance, not on K or the selected loop; no
uniform onset along a changing physical family is asserted.

## Complete original signed source

Keep the notation of the checked OWN-variance join:
S is the literal radius-two signed numerator, V is OWN oddVariance,
c is its SAME finite original odd mean, U is the radial centered square,
Y is the Young square, and D is the original drift square. Put

    a = 6*(1-w)*length^2+epsilon,
    b = 16*length^4*(40*24576^2*(1-w)^2+2*epsilon).

`filtered_loop_own_young_fully_paid`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMixedDepthChordalInsertion.lean:169`,
proves, for t>=0,

    t*S + 2*t*U + 2*Y + 2*t*D
      <= 2*E*[t^2*(V+epsilon)+(t+c^2)*b+t*(4-c^2)*a].

It first proves t*(4-c^2)>=0 using the EXISTING bound c^2<=4 for that
SAME mean, before replacing L. The source, center, all original weights
and even partition stay fixed. All three corrections stay on the left.
The required guards include 16/17<=w<1, epsilon>0, the explicit
kinetic/head guards above, quarticCutoff(w,epsilon)<=K and the SAME
computed mixedQuarticDepthCutoff<=n.

This contracts the two unestimated positive chord moments to explicit
costs while preserving the actual signed corrections. It does not show
that these costs are useful relative to V or lag-one reserve. In
particular the length^2 and length^4 factors have not become uniform.

NEXT is mathematical control of this COMPLETE retained cost on a
justified changing family, not another absolute-cap or normalization
wrapper. The original lag-one reserve and fixed finite relative budget
remain missing inputs to
`BF4WilsonAllNomeDyadicFilteredGeometricSurvival.dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`.

## Verification and boundary

Both final SECOND focused checks exited zero. Their one and four public
gates use only {propext,Quot.sound}; accepted logs contain no errors,
warnings or sorryAx. Independent mathematical source review and independent
source/log/gate/hash review passed. Preliminary failures were explicit
carrier-equality operations, unfolding order and a dependent cutoff rewrite;
no mathematical statement or guard was weakened.

| Artifact | SHA256 |
| --- | --- |
| `QuaternionHaarChordalInterval.lean` | `fb7a699d8cf6a60580fd3b70a4f55ad227dbdc8d42d3e0e52fb0fced1ec6e209` |
| `/tmp/ym-chordal-interval-20261002-second.log` | `b6393fb8717feaed5f1d6da8b7f727d5d766ba800da9082fce8d373dd23e3667` |
| `BF4ExactSlabFixedSpatialMixedDepthChordalInsertion.lean` | `74dc03ccf7baaef071df65ed2f233c526c1440f73ede3adf042fd5ff2edd5a0d` |
| `/tmp/ym-mixed-chordal-insertion-20261002-second.log` | `f7560bccb7a45f2730275dc601cc8470bf14ebd1b908abe4156492ab5c8a1157` |

Every launch used a fresh dynamic preflight, one worker, a 20-GiB ceiling
and 12-GiB OS reserve. All preflights showed 85 percent pressure-free memory
and zero swap. Root imports are registered, NOT aggregate-checked;
root/tree, broad audit/guard and progress metric were NOT run. No new sorry,
axiom, classical shortcut, weakened field, surrogate source or CI change.
The documentation skill kept the explicit finite costs distinct from their
missing physical-family calibration. The exact canonical chart remains
unchanged, so there is no ASCII reprint. Spatial/spacing control, continuum
survival, physical mass calibration, full SAME QFT, every compact simple
group and the Clay target remain OPEN.
