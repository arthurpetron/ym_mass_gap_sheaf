# Original strict prefix margin and exact normalized coefficients

Date: 2026-10-02 UTC. Both next forward/backward producers are checked.
They remain short of the ORIGINAL Haar certificate and continuum survival.

## Forward: one original inclusive cutoff

Put c(q)=40*24576^2*(1-q)^2,
T(w,K)=spacingClosedTail(w,K+1-spacingLabelCutoff(w)), and
H(w,K,x)=standardPointwiseHeatPartial(w,x,K+1). For 16/17<=q<1,
-1<=x<=1, and K+1 at least BOTH original spacing label cutoffs,
`inclusivePrefix_chord_quartic_bound`,
`lean/YMGap/Continuum/SU2HeatJacobiFinitePrefixMargin.lean:113`, proves

    [2(1-x)]^2 H(q,K,x) <= c(q) H(q*q,K,x)+16*T(q,K)+c(q)*T(q*q,K).

The coefficient 16 bounds the squared chord on the entire closed interval.
The SAME K is inclusive: the original heatPrefix contains K+1 labels.
The sound completed-profile order and the original finite tail corridors
are composed at a common later approximation; rational order eliminates
the arbitrary positive approximation slack.

`eval_heatPrefix` and `quarticMarginPolynomial_eval`,
`lean/YMGap/Continuum/SU2HeatJacobiFinitePrefixMargin.lean:179` and line 210,
pin the ACTUAL original RatPoly to those inclusive character prefixes.
`eta_le_quarticMarginPolynomial` at line 234 gives evaluation >=eta>0
for an explicit eta>0 throughout the closed scalar interval. Its polynomial
is `quarticMarginPolynomial` at line 192, with error
`quarticPrefixError` at line 57 plus eta. No Haar certificate is inferred.

`inclusiveTailCutoff` at line 272 is an actual Nat function.
`inclusivePrefixTail_small` at line 277 proves T(q,K)<=epsilon at EVERY
later K for every strict nome and positive rational epsilon, using the
existing original geometric rescaling data. No unspecified tail estimate
is supplied. A combined error-tolerance cutoff is not asserted here.

## Backward: exact coefficient identification

`elevatedMonoCoeff_mul_falling`,
`lean/YMGap/Continuum/BernsteinNormalizedMonomialCoefficient.lean:38`, proves

    elevatedMonoCoeff(N,r,j)*(N)_r = binom(N,j)*(j)_r

for r,j<=N. The r<=j branch clears positive factorial tails; j<r gives
zero on both sides. `elevatedMonoCoeff_eqv_normalizedProduct` at line 71
then identifies the ACTUAL original elevated coefficient with binom(N,j)
times the normalized falling quotient at its computed denominator cutoff.
It retains the SAME invSucc(n)^r on both original products and cancels
only the constructed positive top product.

`normalizedProduct_reconstruction` at line 108 transports this identity
through the full original Bernstein row and returns w^r for EVERY rational
w. This is exact monomial reconstruction, not positivity of the target
heat-margin polynomial or a rational full-polynomial Haar certificate.

## Remaining join and project boundary

Compile the ACTUAL rational margin polynomial into a nonnegative rational
Bernstein row with a computed degree, then construct its original scalar
square witness. The meeting target remains the Type-valued `Certificate`
required by `affine_original_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHeatNomeComparison.lean:135`.
Pointwise positivity does not inhabit it. Signed whole-word cancellation,
OWN interacting variance alignment and useful changing-family costs remain
OPEN, as do continuum survival, physical calibration, full SAME-theory
OS/QFT and every compact simple group. No canonical chart claim changes.

## Verification

Both FIRST focused checks passed under the monitored one-worker launcher,
explicit 20-GiB hard ceiling and 12-GiB OS reserve. Dynamic preflights had
85 percent pressure-free memory and zero swap. All 15 gates are allowed
within {propext,Quot.sound}; the five prefix data functions are axiom-free.
Final logs have no errors, warnings, sorryAx or classical dependency.
Independent mathematical reviews passed both modules.

| Artifact | SHA256 |
| --- | --- |
| Prefix source | `7de5049707656f0e14b03ab34c39966cde19c24db7fad9507ee714065b604e1a` |
| Coefficient source | `e1c98e7d6618ea893c1544f54d042419729fb3331ea553a6bc865dcca258d0f8` |
| `/tmp/ym-jacobi-finite-margin-20261002-first.log` | `98f894e4b6b67605ae162ccc46cd6b7cefd75945c0b37754ff7590b0d99e7080` |
| `/tmp/ym-bernstein-normalized-monomial-20261002-first.log` | `fc3e8e6ece4459e30bf36bb076494b14db4be6bd146e882a56a1d8bf1dea5dac` |

Two root imports are registered, not aggregate-checked. No broad root/tree,
guard or audit was run. No new sorry, axiom, classical shortcut, weakened
frontier, surrogate action, resource ceiling or CI change was introduced.
The canonical chart fence is unchanged and is not reprinted.
