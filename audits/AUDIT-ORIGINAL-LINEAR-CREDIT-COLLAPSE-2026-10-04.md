# Original linear credit: a proved scaling obstruction

The whole-project goal remains OPEN: nontrivial continuum Yang--Mills on
R^4 for EVERY compact simple group, SAME-theory full QFT axioms and finite
positive physical mass. This is an obstruction to a particular computed
coefficient, not to the actual Yang--Mills theory or its mass gap.

## The short mathematical argument

The improved coefficient is `channelObservableSquareLinearVarianceCredit`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSquareCredit.lean:370`.
At footprint size n it is rho=l/u, where

```
l = headFloor(w)^(28*n),     u = prefixCap(w)^(28*n).
```

These are the original `localLower` and `localUpper`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`
and `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:47`.
The already-proved `headFloor_le_oneThirtySecond`,
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`, and
`prefixCap_ge_one`,
`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`, imply
l<=headFloor(w)^n<=4^(-n) and 1<=u. Only the positive scalar u is inverted.
Consequently, for EVERY 0<w<1,

```
0 < rho(w,n) <= 4^(-n).
```

The new proof then uses the existing explicit
`PolynomialGeometricDecay.polynomialCutoff` and `polynomial_bound`,
`lean/YMGap/Continuum/PolynomialGeometricDecay.lean:95`
and `lean/YMGap/Continuum/PolynomialGeometricDecay.lean:99`, at rate 1/4.
For fixed C>=0 and degree p, the computed onset is independent of nome:

```
n >= creditCutoff(C,p,epsilon)
    -> rho(w,n)*C*(n+1)^p <= epsilon.
```

Choosing n=max(eventualOnset,creditCutoff(C,p,delta/2)) constructively
rejects an eventual positive floor delta for that rescaled coefficient.
The theorem allows ANY changing strict nome w(n), with no regularity or
physical-trajectory premise. Size zero, C=0 and p=0 are included.

New declarations are in
`lean/YMGap/Continuum/BF4OriginalChannelLinearCreditCollapse.lean`:

| Declaration | Line | Checked scope |
| --- | --- | --- |
| `linearCredit_geometric_ceiling` | 45 | Actual computed rho<=4^(-size), every strict nome. |
| `creditCutoff` | 75 | Explicit nome-independent modulus. |
| `polynomialCredit_small` | 80 | Fixed amplitude/degree rescaling still vanishes. |
| `no_eventual_polynomial_credit_floor` | 97 | No eventual positive floor, even for arbitrary nome schedules. |

This does NOT upper-bound Q/(Z*OWNVar), an actual response, transfer margin
or physical mass. The actual ratio can be much larger than its certified
lower coefficient rho. It does not exclude super-polynomial rescaling.
No physical spacing family is constructed or assumed. Earlier finite
positivity and improvement over the squared credit remain valid.

## Repointed proof work

Do not spend another branch trying to obtain a useful growing-footprint
floor by adjusting nome while retaining THIS absolute floor/cap coefficient.
It is unavailable even after any fixed polynomial rescaling. Retain the
actual source-dependent moments and signed cancellations instead.

Independent source review also rejects a composition-only next step:
`original_signed_window_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSignedMultiplicationWindow.lean:87`,
and `originalOwnBlockCost_energy_split`,
`lean/YMGap/Continuum/BF4WilsonAllNomeChronologicalExactChannelCost.lean:149`,
give Signed=Cost-(energy+drift). Substitution into the chronological payment
cancels Cost/drift and recovers the endpoint payment, not a new filtered-norm
estimate. This is source analysis, not an additional checked theorem.

The actual forward/backward gap is still a source-specific JOINT estimate
against the SAME surviving filtered-start variance consumed by
`original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
Actual mass-loss and signed cross-minus-mismatch identities offer a rho-free
comparison target; no favorable relative-loss power is assumed. Justified
scaling, survival, physical mass, SAME OS/full QFT/continuum/every-group/Clay
remain OPEN. Canonical displayed claims unchanged; no ASCII or paper list.

The selected NEXT proposition is unproved here: with Q the actual
`squareChannelMoment`, U the original raw second moment and L=M-Z, prove
`(Q-U)^2<=4*L*Q` and `Z*OWNVar<=2*Q+L`. This uses the existing moment-defect
and cap-four certificates, not a new small-loss premise. It would replace
the exponential band credit by an additive computed-loss error in the exact
energy consumer. The subsequent useful loss/window comparison remains open.

## Verification boundary

First focused attempt passed, exit 0 without warnings/errors. FOUR new
public gates: `creditCutoff` axiom-free; three theorems use only
{propext, Quot.sound}. Accepted log:
`/private/tmp/ym-linear-credit-collapse-20261004-1.log`.
Log SHA256:
`0a01b54fbd5a451d88b2afcd7e3e65fea9a5edc4473eed29e46bb01af38fe53d`.
Frozen source SHA256:
`780cd0b0a8c1098d70419d0942ef3c47a6894652e55d585200bb825b321d9fe6`.
Independent semantic review passed. ONE monitored worker, 20-GiB cap,
12-GiB reserve; fresh process/pressure/swap preflight, no competing compiler,
76% free memory and zero swap. No new sorry/axiom/analytic budget, weakened
frontier, CI/resource change or claimed physical closure. Root import is
registration only; no full/root build, broad audit, guard or metrics run.
CI stays off.
