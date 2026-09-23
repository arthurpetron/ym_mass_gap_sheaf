# Original relative-heat mixed curvature: constructed local producer

## Outcome

For the ACTUAL relative quaternion heat `h = heatAt a b w K`, any two
supported within-block angular generators A,B (overlap allowed), and
`0 < w < 1`, the new producer bounds the actual mixed derivative at EVERY
finite cutoff in the original Haar polynomial order:

```text
|A(B h)| <= C2(w)
C2(w) = 4096 * prefixBudget(w,6) + 128 * prefixBudget(w,4).
```

Here `prefixBudget` is the new explicit polynomial-Gaussian sum budget.
For `relativeCutoff w 32 <= K`, the local curvature consumer constructs
both polynomial positivity certificates expressing

```text
-C(w)*h^2 <= h*A(B h) - (A h)*(B h) <= C(w)*h^2
C(w) = C2(w)/headFloor(w) + relativeCap(w,32)^2.
```

The positive rational reciprocal of `headFloor` is computed with its existing
positivity proof. Neither a logarithm nor a reciprocal heat density is assumed
or constructed. These statements mean ORIGINAL Haar-order certificates,
not a separately postulated pointwise analytic model. They retain both mixed
derivatives and the first-derivative product. The constants have no ambient
block-count or representation-cutoff dependence; their nome dependence is
explicit and is NOT claimed uniform or scaling-sufficient as w approaches one.

## Mathematical proof

1. Differentiate the existing positive parity recurrence for the derivative
   character polynomial. Its actual angular derivative has cap at most
   `4*(n+1)^5*d`, where d is the supplied scalar derivative cap. Leibniz then
   gives the actual mixed character derivative, retaining the mixed derivative
   of the scalar.
2. Multiply by the original heat coefficient, including representation
   dimension. The resulting two budgets are degree-six and degree-four
   Gaussian sums. For arbitrary fixed degree m, choose a computed label
   threshold with `2^m*w^(2*threshold+3) <= 1/2`; a finite head plus geometric
   tail bounds every prefix.
3. Coordinate derivatives on the original Haar carrier have caps 2 and 4.
   Four products in the actual relative scalar give mixed cap 64. The existing
   first scalar cap is 32. Substitution yields C2 above without a supplied
   analytic bound or a changed carrier.
4. Put delta=`headFloor(w)` and b=C2/delta. The actual certificates
   `h-delta >= 0` and `C2 +/- A(Bh) >= 0` give `b*h +/- A(Bh) >= 0`.
   Multiplication by the certified positive h gives
   `b*h^2 +/- h*A(Bh) >= 0`.
5. Existing relative first-derivative bounds give `r*h +/- Ah >= 0` and
   `r*h +/- Bh >= 0`, r=`relativeCap(w,32)`. Half-sums of the two signed
   product pairs give `r^2*h^2 +/- (Ah)*(Bh) >= 0`. Adding the appropriate
   signs proves BOTH curvature certificates. No cross term is discarded.

## Source map

| Declaration | File:line | Role |
| --- | --- | --- |
| `gainTarget`, `labelCutoff` | `lean/YMGap/Continuum/SU2HeatPolynomialPrefixBound.lean:28`, `:30` | Computed arbitrary-degree Gaussian tail onset |
| `prefixBudget`, `prefix_bound` | `lean/YMGap/Continuum/SU2HeatPolynomialPrefixBound.lean:88`, `:105` | Actual finite head plus geometric tail bound |
| `derivativeAngularCap_le_quintic` | `lean/YMGap/Continuum/QuaternionHaarCharacterSecondDerivative.lean:59` | Closed polynomial growth of the derivative recurrence |
| `derivativePolynomialAngularIntervalAt` | `lean/YMGap/Continuum/QuaternionHaarCharacterSecondDerivative.lean:113` | Actual derivative-polynomial interval |
| `angularSecondDerivativeCharacterIntervalAt` | `lean/YMGap/Continuum/QuaternionHaarCharacterSecondDerivative.lean:151` | Mixed character derivative, not a surrogate polynomial |
| `heatSecondDerivativeCap`, `heatPrefixSecondAngularIntervalAt` | `lean/YMGap/Continuum/QuaternionHaarHeatSecondAngularDerivative.lean:73`, `:102` | Explicit cutoff-independent heat derivative bound |
| `scalarAt_mixedAngularInterval` | `lean/YMGap/Continuum/SU2QuaternionRelativeHeatSecondAngularBound.lean:195` | Actual relative scalar cap 64 |
| `heatSecondAngularInterval` | `lean/YMGap/Continuum/SU2QuaternionRelativeHeatSecondAngularBound.lean:221` | Actual relative heat consumer |
| `logHessianNumerator` | `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:103` | Complete mixed numerator |
| `secondRelativeCap`, `logCurvatureCap` | `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:143`, `:148` | Computed nome-dependent relative costs |
| `heatLogHessianBounds` | `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:153` | Both signs, actual heat, explicit cutoff guard |

## Verification boundary

Five serialized monitored leaf checks, one worker with an 8 GiB hard limit,
each exited 0. Their twenty-one public print sites reported only permitted
axioms `{propext, Quot.sound}` (some definitions are axiom-free). Accepted
logs contain no warning, error, `sorryAx` or `Classical.choice`.

| Leaf | Accepted log in `/tmp/` | Gates |
| --- | --- | ---: |
| `SU2HeatPolynomialPrefixBound` | `ym-gap-polynomial-prefix-check-3.log` | 11 |
| `QuaternionHaarCharacterSecondDerivative` | `ym-gap-character-second-check-2.log` | 3 |
| `QuaternionHaarHeatSecondAngularDerivative` | `ym-gap-heat-second-check-2.log` | 2 |
| `SU2QuaternionRelativeHeatSecondAngularBound` | `ym-gap-relative-heat-second-check-2.log` | 2 |
| `SU2QuaternionHeatLogCurvature` | `ym-gap-heat-log-curvature-check-2.log` | 3 |

Earlier failed draft checks are not verification evidence. No new hole, axiom,
classical quarantine or weakened frontier field. The final leaf is imported
by `lean/YMGap.lean`, but that root was NOT rebuilt. No full-root build,
full-tree audit, guard or progress-metric script was run; the latter invokes
the guard and therefore needs separate run approval. CI remains off.
Sol supplied bounded drafts; root repaired the proofs, constructed the heat
sum and curvature consumer, and ran all checks. A separate read-only reviewer
confirmed same-heat scope and the remaining normalized-score boundary.

## Actual consumer and remaining joins

This removes the missing local mixed log-Hessian numerator producer in the
route combining local curvature with the checked whole product-kernel
Hessian sign (`SU2QuaternionProductHeatAngularHessian.lean:177`,
`productHeat_upperHessian_nonpositive`). It does NOT yet compose that route.

The remaining joins are:

- Construct the factorwise reciprocal/score through existing positive-window
  polynomial approximants, with an explicit error modulus. Clearing a product
  denominator and then integrating adds an extra W to `H[aa*D^2 W]`; the
  existing Hessian-sign theorem does not justify that replacement.
- Assemble the signed local matrix costs with coefficient-square control.
  Repeated directions must be grouped; arbitrary repeated list entries do not
  satisfy a coefficient-square estimate merely by being a list.
- Retain the certified nonnegative complete source a=V*g and the SAME original
  edge normalization. The older Hessian identity allows signed a, but that
  alone does not permit multiplying a positivity certificate by aa.
- Establish the actual Wilson-jump comparison, SAME centered variance, and
  quantitatively sufficient behavior on a justified spatial/spacing family.
  The displayed conservative C(w) is not asserted to supply that behavior.

The finite-P source correction has not been controlled or equated to an angular
Laplacian. No physical spectral gap, thermodynamic/continuum construction,
nontrivial continuum survival, finite positive physical mass, full same-theory
OS/QFT/YM local-field/UV identification, or every-group Clay obligation closes.
