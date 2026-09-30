# What a finite-feature certificate must actually control

Date: 2026-09-30 UTC. Parent source baseline: `cb25792`.

This report separates source-checked identities, a mathematical derivation
not yet formalized in Lean, and the quantitative test recorded below.
It does not produce the missing original-action collective margin.

## Source boundary

The original two-link law factors as `L(x,e)*R(y,e)*K(x,y,e)`, where `e`
denotes all exterior links. Its shared polynomial has a finite expansion
`K=sum_s u_s(x,e)*v_s(y,e)`. These are signed monomial features; positivity
of individual coefficients is not assumed.

- `term_factorization`,
  `lean/YMGap/Continuum/SU2QuaternionBlockMonomialFeatures.lean:85`,
  retains coefficients and exterior coordinates in the left feature.
- `weighted_moment`,
  `lean/YMGap/Continuum/SU2QuaternionSeparableConditionalMoments.lean:84`,
  proves the exact finite-feature formula for arbitrary-degree,
  opposite-block-independent tests, with both one-sided weights.
- `normalizer_feature_pin` and `covarianceVector_feature_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabTwoLinkFeatureMoments.lean:75` and
  `:129`, identify the actual normalizer and signed numerator.
- `covariance_normalizer_projection`,
  `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:151`,
  divides that numerator by the ACTUAL completed normalizer on the
  detached background. Its `inverseState` is constructed in
  `lean/YMGap/Continuum/BF4ExactSlabBlockCompletedInverse.lean:105`.
  This is an L2 construction, not an exported pointwise fiber inverse.
- `inverse_covariance_bound`,
  `lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceCertificate.lean:58`,
  verifies a supplied polynomial square certificate. It does not construct
  one. Neither does `weightedGramQuadratic_nonnegative`,
  `lean/YMGap/Continuum/FiniteWeightedGramSOS.lean:251`, identify a new
  physical signed expression with its nonnegative weighted Gram form.

Consequently the finite list has polynomial-valued exterior entries, not
entries in a single numerical matrix. Its length is not a bound on the
dimension of the full original observable space.

## Exact normalization needed for a degree-free reduction

The following is a paper derivation, not a new Lean theorem. Fix an exterior
configuration at which the displayed density and marginal denominators
are positive. Existence and quantitative control of this pointwise
realization are NOT inferred from the completed inverse above.
Assume the normalized features below have finite squared marginal
integrals. All integrals in this section are over the selected links only.

Write

```
alpha_s = integral L*u_s       beta_s = integral R*v_s
D = sum_s alpha_s*beta_s
A(x) = sum_s beta_s*u_s(x)     B(y) = sum_s alpha_s*v_s(y)
mu_x(dx) = L(x)*A(x)/D dx     mu_y(dy) = R(y)*B(y)/D dy.
```

For arbitrary tests `f(x), g(y)`, set `F_s=integral L*f*u_s` and
`G_s=integral R*g*v_s`. The connected numerator is exactly
`F^T*(D I-beta alpha^T)*G`. The middle matrix kills `beta` on the
right and `alpha^T` on the left. Thus test-degree modes invisible to
these full symbolic moments cannot contribute to the mixed numerator.
This does NOT discard their original diagonal variance.

The correct centered Riesz features in the ORIGINAL marginals are

```
U_s(x) = u_s(x)/A(x) - alpha_s/D
V_s(y) = v_s(y)/B(y) - beta_s/D.
```

Their means vanish, and the connected density kernel is

```
h(x,y) = D*K(x,y)/(A(x)*B(y)) - 1 = D*sum_s U_s(x)*V_s(y).
```

Using the raw monomials instead of these normalized features changes the
inner product and does not establish a bound in the required variances.
As the exterior varies, these spans form a module over exterior functions;
fiberwise finite rank is not global finite-dimensionality.

## A matrix criterion without a Gram inverse

Still a paper derivation, not an implemented certificate or useful bound.
Let `Gx, Gy` be the Gram matrices of `U, V` in `mu_x, mu_y` respectively.
Let `U` and `V` also denote the synthesis maps from finite coefficient
vectors to these functions. The connected conditional operator is
`T=D*U*V*`, where the final star denotes the adjoint.

For `rho>=0`, the finite quadratic-form inequality

```
rho^2*Gx - D^2*Gx*Gy*Gx >= 0
```

is sufficient for `||Tg||^2 <= rho^2*||g||^2` for EVERY test `g`,
not just chosen monomials. To see this without choosing a basis of a
possibly singular Gram matrix, put `z=Tg`, which lies in the written
range of `U`. The matrix inequality gives
`||T* z||^2 <= rho^2*||z||^2`. Since
`<g,T* z>=||z||^2`, Cauchy--Schwarz gives
`||z||^4 <= rho^2*||g||^2*||z||^2`. The nonnegative scalar implication
then gives the claimed estimate, including `||z||=0`.

This criterion does not require a Gram inverse, a rank decision or a
positive smallest eigenvalue for the feature Gram. Its entries still
involve the ORIGINAL normalized marginal integrals, for example

```
Gx_st = (1/D)*integral L*u_s*u_t/A - alpha_s*alpha_t/D^2.
```

It has not been joined to the repository's completed operators or supplied
with verified entries. All exterior fibers would need control, or an
appropriate jointly integrated operator-valued replacement. A numerical
exterior sample or a finite principal matrix of arbitrary test monomials
does not meet that condition.

The unavoidable relations `sum_s beta_s U_s=0` and
`sum_s alpha_s V_s=0` also explain why an absolute numerical error
`epsilon*I` is unsuitable near the feature kernel. Any approximate matrix
certificate needs exact kernel handling or an error bound relative to its
actual Gram form, not just entrywise accuracy.

## Why not replace the operator bound by total Hilbert--Schmidt mass?

Under the same fiber hypotheses, direct expansion gives

```
integral h(x,y)^2 dmu_x dmu_y
  = D^2*trace(Gx*Gy)
  = integral L(x)*R(y)*K(x,y)^2/(A(x)*B(y)) dx dy - 1.
```

Bounding this total square by `rho^2` is a sufficient Cauchy--Schwarz
test, but is stronger than an operator-norm bound. The distinction is
quantitatively important, not just a missing implementation detail.
For the isolated SU(2) heat packet with `L=R=1`, take the polynomial
`s(x,y)=4*relativeScalar(x,y)`. Ordinary product Haar gives
`integral s=0`, `integral s^2=4`, and the existing exact transmission
identity gives `integral (relativeHeat-1)*s=4*w^3` for every `K>=1`.
Cauchy--Schwarz therefore forces

```
integral (relativeHeat(w,K)-1)^2 >= 4*w^6.
4*(7/8)^6 = 117649/65536 > 1.
```

This part IS now kernel-checked in
`lean/YMGap/Continuum/SU2QuaternionSharedHeatHilbertSchmidtObstruction.lean`:

| Declaration | Line | Exact claim |
| --- | --- | --- |
| `centeredHeat` | 35 | Actual packet minus its unit marginal. |
| `fourChannels` | 39 | The explicit four-channel test `4*relativeScalar`. |
| `fourChannels_coordinates` | 44 | Literal identification with the four coordinate products. |
| `fourChannels_mean` | 68 | Test mean zero in ordinary product Haar. |
| `fourChannels_square` | 72 | Test squared norm four. |
| `heat_channels_pair` | 76 | Exact pairing `4*w^3`, all `K>=1`. |
| `centered_channels_pair` | 86 | The same pairing after removing the vacuum kernel. |
| `centeredHeat_square_lower` | 107 | Centered kernel square at least `4*(qpow w 3)^2`. |
| `test_centeredHeat_square_gt_one` | 160 | That square exceeds one at the existing explicit test nome and late cutoff. |

The input `relative_scalar_moment`,
`lean/YMGap/Continuum/SU2QuaternionSharedHeatLoopMoments.lean:102`,
retains every cutoff spin. `testWeightCertificate`,
`lean/YMGap/Continuum/SU2QuaternionSharedHeatCorrelationObstruction.lean:129`,
supplies positivity of the same test packet; the example is not based on
an indefinite early truncation. The new inequality itself needs no nome
positivity guard, because it is an ordinary-Haar square estimate.

This screen concerns the actual centered polynomial kernel's Haar square,
not the separate legacy character-diagonal HS object. The displayed
factor four counts the four fundamental coordinate channels. It is not
the coefficient of a differently normalized plaquette-gluing formula.

Nevertheless the same isolated heat has a strictly contracting ordinary
Haar map on all centered supported polynomials: `heatMap_centered_square_bound`
and `squaredHeatRate_lt_one`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatContraction.lean:112` and
`:104`. Thus total kernel-square smallness is not necessary for strict
operator contraction. Do not use it as the general producer at the
weak-coupling end of this route. This does not refute the normalized Gram
criterion, the full slab with its one-sided actions, a restricted-sector
compression, or a defect-retaining collective estimate.

## Execution decision and actual consumer

Do not launch a finite test-matrix SDP or exterior grid as if finite feature
count eliminated omitted modes. Do not implement a new conditional
certificate wrapper before identifying a useful producer. The normalized
Gram criterion is an admissible design target, not a new prerequisite for
the whole project and not an inhabitant of an existing open bundle.

A pairwise absolute estimate is only a sufficient route. The earlier
`test_degree_budget_obstruction`,
`lean/YMGap/Continuum/SU2QuaternionSharedHeatCorrelationObstruction.lean:142`,
already excludes the shared-factor-only degree budget at the positive
late-cutoff test nome. Keep both one-sided actions, positive prediction
defects and signed collective cancellation when seeking an improvement.

The immediate collective consumer remains
`conditionalGenerator_square_polynomial_lower`,
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:189`.
It needs a useful lower estimate for the SAME signed rational value versus
the SAME conditional energy; neither the feature identity nor this report
supplies it. The operator is conditional-link dynamics, not physical OS
time. A03 and every same-theory continuum/Clay obligation remain open.

Sol reviewed the feature/normalizer source boundary. Luna searched the
existing harmonic, Gram and certificate APIs and independently checked
the centered normalization and singular-Gram matrix argument. No full
build, numerical search or routine literature scan was needed for this review.

## Verification boundary

Sol implemented the isolated-kernel obstruction; the parent integrated and
checked it. The final focused run completed in about four seconds:

```
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/SU2QuaternionSharedHeatHilbertSchmidtObstruction.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionSharedHeatHilbertSchmidtObstruction.olean
```

All nine printed declaration gates are subsets of `{propext, Quot.sound}`;
the two definitions have empty axiom sets. The initial focused run exposed
only a missing `liftHead` namespace, repaired by opening its defining
namespace. No new sorry, axiom, native oracle or analytic premise.
The symbolic cutoff was not expanded. Preflight found 80% memory free and
no competing compiler/runner; the mandatory one-worker/20 GiB check used
continuous automatic safety monitoring. No full-root build or broad audit
was run. The normalized Gram criterion remains paper mathematics, not a
kernel-checked bridge or a constructed useful matrix certificate. No
canonical chart state changed.
