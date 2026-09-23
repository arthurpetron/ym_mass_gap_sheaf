# Lossless integrated cancellation and the actual local normalized heat score

## Outcome and scope

For the ACTUAL selected relative heat
`h = heatAt i (n+i) w K`, an upper-block angular generator D, and
`R = a(x)*a(y)`, the new theorem constructs

```text
H[R*(D h)*f]^2 <= C(w) * H[R*h*f^2] * H[R*h].
```

Here a is any supported n-block polynomial carrying an original-Haar
nonnegative certificate, f is any supported signed two-slice polynomial,
`0 < w < 1`, and `relativeCutoff w 32 <= K`. The source may depend on its
ENTIRE slice; f may depend on both slices. The theorem concerns ONE selected
relative-heat factor, not the full interacting product kernel.

With `Z=H[R*h]>0`, the checked normalized consequence is

```text
(H[R*(D h)*f]/Z)^2 <= C(w) * H[R*h*f^2]/Z.
```

Both occurrences of Z are literally the same original edge mass. Its
positivity is explicit; the homogeneous theorem also permits zero source.
No positivity of f, centering of f, or supplied curvature/score estimate is
required. The curvature and integrated Hessian sign are constructed from
the actual heat. C(w) is the previously computed `logCurvatureCap`: it retains
its inverse-head-floor and nome dependence. Cancellation introduces NO
ADDITIONAL floor cost. No scaling-sufficient asymptotics are asserted.

## Mathematical contraction

Let W be a supported polynomial with certified `0<ell<=W<=u`, R have a
nonnegative certificate, and suppose the actual polynomials d,dd satisfy

```text
Certificate(lambda*W^2 + W*dd - d^2),   H[R*dd] <= 0.
```

For rational s,t and any supported signed f put

```text
Q = s^2*W*f^2 - 2*s*t*d*f + t^2*(dd + lambda*W).
W*Q = (s*W*f-t*d)^2 + t^2*(lambda*W^2 + W*dd-d^2).
```

The second line constructs a certificate for W*Q. It does NOT justify
discarding an extra W from a weighted Hessian sign. Instead:

1. The existing finite geometric reciprocal polynomials G_k are proved
   certificate-positive, and `W*G_k-1` has a computed uniform error cutoff.
2. The corrected insertion `R*G_k*(W*Q)` is certificate-positive. Its
   difference from R*Q has integrated absolute value bounded by
   `epsilon * polynomialCap(Q) * H[R]`.
3. A computed inner tolerance pays that finite cost. The constructive
   rational Archimedean lemma removes the vanishing error, giving
   `H[R*Q]>=0`. This is integrated order reflection, NOT certificate-level
   division or construction of a completed reciprocal observable.
4. The ORIGINAL sign `H[R*dd]<=0` gives a nonnegative rational quadratic
   with coefficients `A=H[R*W*f^2]`, `B=H[R*d*f]`, `C=lambda*H[R*W]`.
   The constructive discriminant, including zero-diagonal cases, yields
   `B^2<=A*C`. A positive Z is then canceled exactly by its rational reciprocal.

For the concrete relative heat, `heatLogHessianBounds` supplies the local
curvature certificate. The singleton specialization of
`productHeat_upperHessian_nonpositive` supplies the sign, retaining both
copies of the same source. Existing lower/upper heat certificates give a
positive window; enlarging the upper cap by the positive floor avoids an
unnecessary comparison theorem. These window constants disappear from the
dual estimate except for dependence already present in C(w).

## Parallel product input, also checked

For factor jets `(p,dp,ddp)` and `(q,dq,ddq)`, multiplying their curvature
certificates by the opposite squares and adding cancels both cross terms.
The resulting product cost is r+s, not a product of floors or caps.
The checked signed-direction first and second Leibniz rules identify these
jets with the ACTUAL derivatives of p*q; their certificate consumer is
`signedAngular_productLogCurvatureLower`.

This proves two-factor composition, NOT the yet-missing localization of a
whole signed direction onto every actual relative-heat factor. Repeated
generators must be grouped and repeated heat factors counted. Separate local
dual bounds must not be summed as if their mixed terms vanished.

## Declaration map

All paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `reflectionCutoff`, `reflection_with_error` | `QuaternionHaarPositiveWindowOrderReflection.lean:68`, `:73` | Explicit finite reciprocal/error construction |
| `haar_nonnegative_of_positive_multiplier` | `QuaternionHaarPositiveWindowOrderReflection.lean:131` | Lossless same-integral multiplier cancellation |
| `nonnegative_quadratic_discriminant` | `RationalQuadraticDiscriminant.lean:21` | Constructive discriminant, including degeneracy |
| `normalize_squared_bound` | `RationalQuadraticDiscriminant.lean:100` | Exact same-positive-mass cancellation |
| `curvature_dual_bound` | `QuaternionHaarCurvatureDualBound.lean:148` | General square-completion consumer |
| `productLogCurvatureLower` | `QuaternionHaarProductLogCurvature.lean:30` | Exact two-factor jet curvature composition |
| `signedAngularDirection_second_mul` | `SU2QuaternionSignedAngularAlgebra.lean:112` | Actual signed second derivative product rule |
| `signedAngular_productLogCurvatureLower` | `SU2QuaternionSignedAngularAlgebra.lean:147` | Composition pinned to actual derivatives |
| `heatAt_upperAngularHessian_nonpositive` | `SU2QuaternionSingleHeatHessian.lean:61` | Actual local heat Hessian sign, arbitrary supported source |
| `relativeHeat_dual_score_bound` | `SU2QuaternionRelativeHeatDualScore.lean:50` | Constructed homogeneous actual-heat instance |
| `relativeHeat_normalized_dual_score_bound` | `SU2QuaternionRelativeHeatDualScore.lean:99` | Same-Z normalized actual-heat instance |

## Verification boundary

Seven serialized monitored leaf checks, one worker, 8 GiB hard limit. All
accepted commands exited 0. Their twenty public print sites report only
`{propext, Quot.sound}`; accepted logs contain no warning, error, `sorryAx`
or `Classical.choice`. Earlier failed drafts are NOT evidence of verification.
The cancellation check was completed during the preceding proof work; its
unchanged source and accepted log were inspected again for this checkpoint.

| Leaf | Accepted log under `/tmp/` | Gates |
| --- | --- | ---: |
| `QuaternionHaarPositiveWindowOrderReflection` | `ym-gap-window-order-reflection-check-1.log` | 8 |
| `RationalQuadraticDiscriminant` | `ym-gap-quadratic-discriminant-check-5.log` | 2 |
| `QuaternionHaarCurvatureDualBound` | `ym-gap-curvature-dual-check-4.log` | 1 |
| `QuaternionHaarProductLogCurvature` | `ym-gap-product-log-curvature-check-3.log` | 1 |
| `SU2QuaternionSignedAngularAlgebra` | `ym-gap-signed-angular-algebra-check-5.log` | 5 |
| `SU2QuaternionSingleHeatHessian` | `ym-gap-single-heat-hessian-check-3.log` | 1 |
| `SU2QuaternionRelativeHeatDualScore` | `ym-gap-relative-heat-dual-score-check-3.log` | 2 |

Sol/Luna supplied bounded drafts and an independent scope review; root
repaired, composed and checked the accepted proofs. No new hole, axiom,
classical quarantine, weakened frontier field or canonical atom closure.
The semantic root imports the new leaves, but was NOT rebuilt. No full-root
build, full-tree audit, guard or progress-metric script was run. CI stays off.

## Remaining causal frontier

Construct the actual full-product curvature cost from grouped local angular
coefficients, retaining generator/factor multiplicities, then consume it with
the full original-kernel Hessian sign and the general dual theorem. Prove the
Wilson-jump comparison against the SAME centered variance and quantitatively
sufficient bounds on a justified spatial/spacing family. The finite-P source
correction has not been bounded or identified with an angular Laplacian.

No physical spectral-gap lower bound, physical-time identification,
thermodynamic/continuum limit, nontrivial continuum survival, finite positive
physical mass, full same-theory OS/QFT/YM local-field/UV identification, or
every-compact-simple-group Clay obligation is closed by this checkpoint.
