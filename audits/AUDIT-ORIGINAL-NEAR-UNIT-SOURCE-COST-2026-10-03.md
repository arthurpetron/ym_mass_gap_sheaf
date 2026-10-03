# Original near-unit source derivative in the complete signed cost

## Mathematical increment

The former permanent factor two in the leading source derivative came from
combining it with a vanishing reciprocal correction. It is not necessary.
For any positive rational sigma, the checked ORIGINAL consumer replaces
that factor by 1+sigma, at a computed tighter correction onset. It does
not estimate the genuine source/action or conditional-variance debt.

The SAME-weight asymmetric inequality is

```text
H[W*(p+e)^2] <= (1+sigma)*H[W*p^2] + (1+1/sigma)*H[W*e^2].
```

`QuaternionHaarAsymmetricSquareTriangle.weighted_square_add_le`,
`lean/YMGap/Continuum/QuaternionHaarAsymmetricSquareTriangle.lean:83`,
uses the existing certified square `(sigma*p-e)^2` through
`QuaternionHaarRelativePredictionFloor.weighted_square_young`. Its rational
upper-budget consumer is `weighted_square_add_bound` at the same path:109.
Only positive rational sigma is inverted. The original weight may share
variables with both signed inputs; neither independence nor a weight floor
is assumed.

## Original-action join

All declarations below are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.lean`.

The unchanged objects are

```text
a = g_(n+r), c = T^r(g_n*psi), A = T a, b = T c,
G = the actual finite reciprocal polynomial for A,
q = P_fringe(V*A) = Vbar*A,
phi = G*b, B = ell(b^2), Z0 = ell(A^2), Z1 = ell(A*T A).
Y = lift(A)*D(V*c) - lift(b)*D(V*a), kept UNSPLIT.
L0 = sum_active,six H[Vbar^2*G^2*(I K)*I(K*Y^2)].
```

`sourceDerivativeAngularBudget` (:181) is literally `(1+sigma)*L0`.
`sourceDerivativeAngularBudget_scale` (:198) kernel-checks the exact
coefficient against its undoubled algebraic value. The sigma-zero value
is just this polynomial budget; there is NO zero-tolerance estimate.

`asymmetricCorrectionTolerance` (:140) computes

```text
tau(sigma,epsilon) = 2*epsilon/(1+1/sigma).
```

`asymmetricCorrectionTolerance_positive` (:145) proves positivity and
`asymmetricCorrectionTolerance_payment` (:150) proves
`(1+1/sigma)*tau = 2*epsilon`. The existing allocation over all links and
six planes already pays two copies of a correction square. This equality
pays the new coefficient with exactly the same final epsilon*B budget.
There is no source, terminal mass or surviving-norm inverse.

`asymmetricCorrectionCutoff` (:169) feeds tau to the existing computed
correction cutoff. `asymmetricCorrectionCostCutoff` (:174) first uses
the existing `correctionBulkTolerance` to pay the actual partition factor.
These onsets explicitly depend on sigma, tolerance, nome and spatial width.
They do NOT give a spacing- or changing-family-uniform estimate.

`original_block_sourceDerivative_angular_le` (:273) constructs

```text
weightedAngularEnergy(q,phi_(k+1)) <= (1+sigma)*L0_(k+1) + epsilon*B.
```

It uses the original projected-source pin and the actual inactive-link zero
identity. Every active link and all six planes are included. A signed psi
and zero B are allowed.

`sourceDerivativeSignedBulk` (:359) retains BOTH signed Taylor remainders:

```text
AsymBulk = Z0*[ (1-w)*(1+sigma)*L0 + Rmixed - Rdiagonal ].
```

`original_block_sourceDerivative_energy_le` (:373) pays the correction
in SAME Z1*B currency. `original_block_sourceDerivative_cost_relative_tolerance`
(:448) composes it with the existing independent depth-drift and
reconstruction onsets:

```text
D <= AsymBulk_(k+1) + (zeta+delta+epsilon)*Z1*B.
```

Only the reciprocal-correction onset changes. The source derivative still
includes DV*X. The positive conditional determinant
`lastStep_sourceDerivative_certificate` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:177`
is still a genuine, unpaid Jensen debt. No Ward cancellation of that debt,
the finite score-correction cross terms, or the Taylor difference is claimed.

## Backward consumer and remaining input

The existing sufficient aggregate consumer is
`BF4WilsonAllNomeWindowSignedCost.original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
Its `originalOwnBlockCost` is the same cleared cost divided by its own
Z0*Z1, defined by `BF4WilsonAllNomeDyadicOriginalRayleighLimit.originalOwnBlockCost`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:98`.
The useful eventual JOINT budget relative to the original window-start
variance is still NOT constructed. Every lag must keep its own partitions
and the common original stage center. Source/Taylor terms are not asserted
to telescope. Earlier reconstructed-square payment remains available;
this checkpoint does not construct a scaling-small payment cap.

The live next analytic target uses the tighter leading coefficient while
retaining the complete signed window. Justified scaling, physical mass
calibration, nontrivial continuum survival, full QFT axioms, every compact
simple group and the Clay theorem remain OPEN. No exact displayed chart
claim changes, so the canonical chart is not reprinted.

## Verification boundary

Two serialized focused checks passed 13 printed gates, all within
`{propext, Quot.sound}`. No root aggregate build or full audit is claimed.
The root imports are registration only. Independent semantic review passed.
No sorry was introduced/discharged, and no axiom, classical shortcut,
canonical field weakening, CI change or external computation was used.
Each launch rechecked dynamic capacity: 76--77% free memory, zero swap and
no other Lean worker. One worker, 20-GiB worker cap and 12-GiB reserve.

Accepted evidence and SHA-256:

```text
QuaternionHaarAsymmetricSquareTriangle.lean
e9296a0a51d15cbbf56eef9a79c29ea03a93fef195b0dc5a9e29921cc5004256
/tmp/ym-asymmetric-square-20261003-2.log
f7caf8ea227f160f7229e4acb6827ece1802d88ec5dfd4a949b33e759df5f4ba
BF4ExactSlabFixedSpatialLastStepAsymmetricEnergy.lean
7a6c73b5fca96f9b5a58957fc8c91ef854a777f39d0020b36ccefe16ef1c04e4
/tmp/ym-asymmetric-source-cost-20261003-3.log
40826697507aad6766a06833cffed5d77ff34a7c18ef777084edd8be31ea9025
```

Earlier attempts had namespace/parser or explicit positivity-elaboration
errors. Those rejected logs are NOT proof evidence; only the accepted
logs above are counted.
