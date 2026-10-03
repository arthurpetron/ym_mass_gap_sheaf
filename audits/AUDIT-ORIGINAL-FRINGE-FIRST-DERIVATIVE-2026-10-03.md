# Original fringe-first derivative and smaller complete signed cost

## Mathematical increment

Average the COMPLETE incoming source derivative over the unheated lower
fringe BEFORE squaring. This preserves the original score and removes an
exact nonnegative weighted residual square from its previous upper budget.
The result reaches the complete original signed cost, not merely a free
polynomial identity. No useful changing-family rate or continuum claim closes.

In the original doubled carrier, write

```text
a=g_(n+r), c=T^r(g_n*psi), A=T a, b=T c,
Y=lift(A)*D(V*c)-lift(b)*D(V*a), kept UNSPLIT,
Q=P_lowerFringe(Y), R=Y-Q,
P=the original kinetic kernel, I=original lower-head Haar integration,
M=I(P), S=the original conditional score,
Bold=M*I(P*Y^2), Bproj=M*I(P*Q^2), Bfringe=M*I(P*R^2).
```

The projected derivative still contains the integrated original action
derivatives; no surrogate action is substituted. K below denotes the heat
cutoff, not the kernel P.

## Exact weighted proof

`familyProject_weighted_mean`,
`lean/YMGap/Continuum/SU2QuaternionHaarFamilyWeightedPythagoras.lean:48`,
preserves the weighted mean when the weight is independent of the projected
slots. `familyResidual_weighted_orthogonal` at the same path:73 proves
orthogonality under every similarly independent test.
`family_weighted_square_decomposition` at the same path:94 gives

```text
H[E*Y^2] = H[E*Q^2] + H[E*R^2].
```

The equality permits signed E. `familyResidual_weighted_square_nonnegative`
at the same path:128 and `familyProject_weighted_square_le` at :137 use an
actual positivity certificate for E to construct coefficient-one contraction.
Support is required for positivity, not silently for the algebraic equality.
The existing family projection/residual and original Haar functional are used.

## Original score and removed debt

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lean`.

`lastStepProjectedDerivative` (:72), `lastStepProjectedDerivativeBudget`
(:76) and `lastStepProjectedDerivativeFringeDebt` (:83) define Q, Bproj and
Bfringe literally as above. The kinetic mass M is retained, not canceled.
`lastStepProjectedDerivative_supported` (:119) constructs the doubled support.

`kinetic_fringe_independent` (:127) uses the actual active-block kinetic
product. `fringe_head_carrier` (:137) proves that I(P*Y) and I(P*Q) agree
under EVERY surviving insertion. Its insertion is arbitrary: the boundary
lift is absent from the lower fringe, just as P is. No fringe locality
assumption on the input a,c is needed.

`lastStep_projectedDerivative_carrier` (:168) composes this with the original
angular-IBP score pin to recover S. `lastStep_projectedDerivative_certificate`
(:187) constructs the remaining conditional determinant Bproj-S^2 >= 0.
This active conditional Jensen debt is NOT removed.
`lastStep_projectedDerivative_weighted_multiplier_square_le` (:209) bounds
the original score with arbitrary certified output W and supported multiplier.

`lastStep_projectedDerivative_weighted_budget_decomposition` (:274) proves

```text
H[W*Bold] = H[W*Bproj] + H[W*Bfringe].
```

Here E=P*lift(W*M) retains P, W and M. W is arbitrary even in the exact
identity; lower-fringe independence follows from its upper boundary lift.
`lastStep_projectedDerivative_weighted_budget_le` (:298) constructs
H[W*Bproj] <= H[W*Bold] for certified W, the existing cutoff positivity
guard and supported sources. It requires no positive lower floor or inverse.
Zero W is included. No strictly positive size of the improvement is claimed.

## Complete signed-cost join

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean`.
Let Vbar=P_fringe(V), G be the actual finite reciprocal polynomial,
phi=G*b, q=P_fringe(V*A)=Vbar*A, B=ell(b^2),
Z0=ell(A^2) and Z1=ell(A*T A).

`projectedDerivativeAngularBudget` (:146) sums

```text
(1+sigma)*H[Vbar^2*G^2*Bproj]
```

over every active link and six planes. Its exact algebraic scaling is
`projectedDerivativeAngularBudget_scale` (:163). Sigma zero denotes only
the undoubled algebraic budget, NOT a zero-tolerance approximation theorem.
`projectedDerivativeAngularBudget_le_source` (:182) proves this budget is
no larger than the previous asymmetric source budget for sigma>=0, with
the actual certified W=Vbar^2*G^2.

`original_block_projectedDerivative_angular_le` (:276) bounds the full
original angular energy by the projected budget plus epsilon*B, at the
EXISTING `asymmetricCorrectionCutoff`. Inactive links vanish by their actual
post-transfer independence; no action weight is discarded.

`projectedDerivativeSignedBulk` (:362) defines

```text
ProjectedBulk = Z0*[ (1-w)*ProjectedAngular + Rmixed-Rdiagonal ].
```

`projectedDerivativeSignedBulk_le_source` (:376) proves this COMPLETE bulk
is no larger than the old one. BOTH signed Taylor remainders are identical.
`original_block_projectedDerivative_energy_le` (:397) pays the correction
in the same Z1*B currency.
`original_block_projectedDerivative_cost_relative_tolerance` (:472) gives

```text
D <= ProjectedBulk_(k+1) + (zeta+delta+epsilon)*Z1*B.
```

The existing correction/depth/reconstruction onsets and k+1 convention are
unchanged. Sigma>0, nome, width and tolerance dependencies remain explicit.
Signed sources and zero surviving norm are included; no source, terminal
mass or norm is inverted. Fixed-parameter moduli are NOT scaling-uniform.

## Backward endpoint and remaining producer

The existing eventual aggregate consumer remains
`original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
It requires the COMPLETE normalized original window cost, each lag's own
partitions and common stage OWN center, relative to the original window-start
variance. The new projected upper bound does not supply that analytic budget.
Individual raw source or Taylor terms do not inherit the response telescope.

The live next producer must address the remaining ACTIVE conditional
variance of Q under the original kernel and actual upper weight, together
with the signed Taylor difference. Source/math review found no existing
arbitrary-Q/upper-W conditional angular upper bound: the closest
`productMap_full_defect_le_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSharpAngularDefect.lean:164`,
is an UNWEIGHTED pairing-defect estimate, not this conditional variance.
The positive `determinant_certificate`,
`lean/YMGap/Continuum/SU2QuaternionMultiHeadVarianceReplica.lean:439`,
constructs nonnegativity, not an angular ceiling.

A semigroup approach cannot silently start the finite spectral cutoff at
the identity or use its original positivity guard at every intermediate
nome. `productHeatCertificate`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatContraction.lean:85`,
explicitly requires `headCutoff w <= K` at the nome being used. Endpoint
projection defects and their payment remain analytic review obligations,
not a newly formalized obstruction or counterexample.

Justified scaling, positive physical mass calibration, nontrivial continuum
survival, full same-theory QFT axioms, every compact simple group and the
Clay theorem remain OPEN. Exact displayed chart claims do not change;
the canonical ASCII block is not reprinted.

## Verification boundary

Three serialized focused checks passed 22 printed gates (5+9+8), all
within {propext, Quot.sound}. No sorry was introduced/discharged, and no
new axiom, classical shortcut, canonical-field weakening, CI change or
external computation was used. Root imports register the modules only;
no root aggregate build or full-tree audit is claimed. Independent source/
mathematical review passed; it is separate from the focused Lean checks.
Capacity was checked before every launch: 76% available memory, zero swap,
no competing Lean worker. One worker, 20-GiB worker cap, 12-GiB reserve.

Accepted source/log SHA-256 evidence:

```text
SU2QuaternionHaarFamilyWeightedPythagoras.lean
c0d158d6fe28752328d9ba4de00b699825c7f913ec7850536d51948c54360705
/tmp/ym-weighted-fringe-pythagoras-20261003-1.log
3c227e036e34b224fcd0ae0dd75443b7e3f9f3c78d147d8833a9f9f3854fca02
BF4ExactSlabFixedSpatialLastStepProjectedDerivative.lean
aff59330a9f7b236de490766ec1c9733564e17bcfb154a12685cd294721c32bc
/tmp/ym-projected-source-derivative-20261003-2.log
d99711697a9a3b46097756f04f6a390a09097dbd97b9c06bc77ee0c01ebe9f31
BF4ExactSlabFixedSpatialLastStepProjectedDerivativeEnergy.lean
2732d3e338cf065c465bdf7a10c10c2fe63632ba91c4fe5ff7d78d73706f8a74
/tmp/ym-projected-source-energy-20261003-1.log
0b13e2df2e4ef5ab7e4ab1ac7e0d862047cd35832d8e63047c0b2d17f3a03869
```

The first projected-source attempt failed because the defining namespace
of two independence helpers was not opened. Its error-generated sorryAx
output is rejected evidence; only the clean accepted second log is counted.
