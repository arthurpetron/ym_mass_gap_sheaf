# Whole-word signed covariance and paid finite mean residue

The ORIGINAL growing Wilson square now has a quantitative whole-word
covariance bound, retaining its negative spin-two moment. The actual finite
OWN-mean correction has an explicit geometric depth modulus. These are
constructively checked finite estimates, not a changing-family survival
budget, continuum construction or physical mass-gap theorem.

## Same objects and retained signed estimate

Let P be the original selected product heat, q the entire lower source,
R a certified upper weight, and f the fundamental trace of an ordered word
of P links whose mapped indices are distinct and selected. Set

    a = w^(3*P), d = w^(8*P), C = P(q*f)-a*(Pq)*f,
    L = H[R*(P(q^2)-(Pq)^2)],
    Q2 = H[R*b^2], Q2f2 = H[R*b^2*f^2].

`fullSourceLoss`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonCovariance.lean:52`,
defines the literal loss inside L. `fullSourceLoss_retained_nonnegative`
at line 206 proves L>=0 under the original product kernel and retained R;
no independence of R from the output links is required.

`fundamental_word_covariance_pair_retained_bound`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonCovariance.lean:321`,
proves

    H[R*b*C]^2 <= L * [(1-d)*Q2 - (a^2-d)*Q2f2].

The proof centers q and f conditionally on the original doubled carrier,
applies weighted Cauchy--Schwarz to the entire scalar word, and computes
the test norm from the actual first and second character images. It keeps
the signed subtraction instead of summing coordinate absolute costs.
The upper test costs its SAME weighted square, not a raw Haar norm.
Its explicit guards are 0<w<1, K>=headCutoff(w), K>=2, source/test/weight
support, a weight certificate, distinct selected indices and distinct mapped
word indices. No derivative inverse, source eigenpin, covariance conclusion
or interacting-variance comparison is input.

`fundamental_word_covariance_pair_bound` at line 426 is the coarser corollary
obtained by discarding the proved nonpositive correction:

    H[R*b*C]^2 <= (1-w^(8*P))*Q2*L.

The explicit rate depends on w and perimeter. Neither estimate gives a
spacing/volume-uniform physical rate. The existing one-link scalar
`radialRate_factorization`,
`lean/YMGap/Continuum/SU2QuaternionHeatCovarianceRates.lean:36`,
and `radialRate_le_twentyFour_quadratic` at line 113 do not supply a bound
on this interacting Q2f2 or on L relative to the completed response.

## Actual BF4 square consumer

`originalSourceHeatLoss`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainCovariance.lean:73`,
uses q=V*g_n and the ORIGINAL output action V. `centeredMessageSquare`
at line 78 is ell(b^2), and `centeredMessageCharacterSquare` at line 84
is ell(b^2*f^2), for b=T(g_n*(f-c)). No terminal or spectator factor is removed.

`paddedSquare_fullSourceDefectPair_retained_square_bound` at line 226
constructs the actual padded-square geometry, active indices, distinctness,
source-word recoding and perimeter4*side. It specializes the bound above
with a=w^(12*side), d=w^(32*side), R=V and the same original b.
`paddedSquare_commutatorGain_retained_covariance_bound` at line 294 proves

    [G2-(a-1)*c*ell(A*b)]^2
      <= originalSourceHeatLoss * [(1-d)*ell(b^2)-(a^2-d)*ell(b^2*f^2)].

Here A=Tg_n. `paddedSquare_own_commutatorGain_retained_covariance_bound`
at line 321 substitutes the actual finite OWN odd mean, at the SAME depth
and with the SAME source, upper action, transfer and square. Coarser
counterparts at lines 116, 182 and 208 retain the same mean correction.
No finite stationarity, odd/even partition equality or favorable gain sign
is assumed or proved.

## Finite moving-mean error paid

For any original fundamental source loop and E=the SAME even partition,
`own_centeredMeanPair_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredMeanResidueBound.lean:138`,
proves abs(ell(A*b))<=4*mixRate(w,width)^n*E at its actual OWN mean.
It compares mixed window(n,1,n+1) with matched window(n,1,n), using an
actual sharp trace interval of cap2. It does not set the mixed mean to zero.

`own_meanResidue_bound` at line 195 uses the proved abs(c)<=2 and a<=1:

    abs((a-1)*c*ell(A*b)) <= 8*(1-a)*mixRate(w,width)^n*E.

`meanResidueDepthCutoff` at line 235 computes
geometricCutoff(mixRate(w,width),8,epsilon).
`own_meanResidue_tolerance_bound` at line 241 proves, for every depth
at or beyond that cutoff and epsilon>0,

    abs((a-1)*c*ell(A*b)) <= (1-a)*epsilon*E.

The onset is independent of heat cutoff and loop size, but NOT nome or
spatial width. No reciprocal variance or changing-family uniformity is used.

## Backward requirement still open

`dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`,
still requires both the actual reserve R1>=gamma0>0 and the relative budget
m*(R1-R2)<=C*R1 on the SAME completed unit state. It gives
Rm>=gamma0*(1/4)^(2*C) for Nat C>=1 and m>=4*C.

The new finite inequalities do not identify originalSourceHeatLoss with
OWN variance or this lag-one reserve. They do not prove a useful bound on
the complete retained cost, or a favorable signed G2, with fixed constants
on a justified changing family. That quantitative join, positive reserve,
nontrivial continuum survival, physical mass calibration, full same-theory
QFT structure and every compact simple group remain OPEN. No canonical
displayed status node changed and no chart is reprinted.

## Verification and evidence

Three final focused checks passed 18 printed gates (5+9+4). Every dependency
set is contained in {propext, Quot.sound}; wordCovarianceRate is axiom-free.
Independent mathematical reviews and source/log QA passed. Root imports
are registered, NOT aggregate-checked. No new sorry, axiom, classical
shortcut, CI change or resource-limit increase was introduced.

Each launch used scripts/safe_lean_build.py with one worker, an explicit
20-GiB worker cap and 12-GiB system reserve. Fresh preflights showed no
competing proof compiler, 86% available memory and no swap pressure.

| Source | Accepted log | Gates |
| --- | --- | --- |
| SU2QuaternionProductHeatWilsonCovariance.lean | /tmp/ym-whole-word-covariance-20261003-second.log | 5 |
| BF4DyadicWilsonSquareFilteredGainCovariance.lean | /tmp/ym-square-gain-covariance-20261003-first.log | 9 |
| BF4ExactSlabFixedSpatialFilteredMeanResidueBound.lean | /tmp/ym-filtered-mean-residue-20261003-fourth.log | 4 |

SHA256 source/log pairs in the same order:

    f267c71c22601df66c8e6f1e9903a8604c7d46b0b1d7b5fd38996721a33ddd0b
    66d66994029ba617b861fd6a2a52258f4d4d4db036f1cb0613b446e209245f55
    0768383802df9e1fb637bb6c3ef8a3b20acd84e5faca6799b4efd7cf0c964325
    62b89b4452e0593ab2cd60aa085e1297b8b21dada110328ef4bf8d0463da4d09
    d7d62df8c2fde8ae255890b0c4cd949c8077a085b41041ba894d8837996dcfdf
    a92243dc1796514140acc3cc35e991abe227296e3944fa7f4d251bed94f3e8ff

Earlier draft failures are not proof evidence. The accepted frozen source
and log pairs above are the scope of this verification, not the whole repo.
