# Adaptive directions at the original conditional-score frontier

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms,
and a finite strictly positive physical Hamiltonian mass gap.

## Mathematical selection before implementation

The previous checkpoint proves an unweighted whole-product norm-loss law
and refutes arbitrary positive output weighting. Do not reopen that shortcut.
The exact original terminal variance balance already exists, so no new
stationarity wrapper is needed.

The remaining joint-score step needs direction coefficients that depend on
the output, not just a fixed rational vector. For the six rotations at ONE
block, set Mij=h*Di(Dj h)-(Di h)*(Dj h), U=C(w)*h^2. The existing ORIGINAL
heat certificates give both U+Mij and U-Mij. The missing finite construction
is a certificate for

    6*U*sum_i ui^2 + sum_ij ui*uj*Mij,

for supported POLYNOMIAL ui. Every ordered mixed entry is retained. The
square identity

    U*(v^2+z^2)+2*M*v*z
      = ((U+M)*(v+z)^2+(U-M)*(v-z)^2)/2

constructs each pair; half-summing all ordered pairs gives the desired
six-column envelope. No coefficient is differentiated. This is the FROZEN
Hessian, not D_u(D_u h), which would add derivative-of-ui terms.

Inputs: `lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:152`,
`heatLogHessianBounds`, and the supported square/product/transport
constructors in `QuaternionHaarSquareCertificate.lean`. Existing
`SU2QuaternionProductHeatSignedLogCurvature.productHeat_signedCurvature`
uses rational constant coefficients and is not this substitution theorem.

Downstream consumer: the missing adaptive whole-product/conditional Gram
estimate for S_i=A*Di b-b*Di A. **No declaration currently implements that
complete adaptive join.** The local certificate is one needed input, not
the joint-score theorem itself. The complete original V source, paired
residual, output weight and terminal mismatch must survive the eventual
join. Do not use the equal-endpoint integrated Hessian sign on a conditional
law, and do not turn a qMax/A upper comparison into a useful spatially
uniform constant by omitting its denominator dependence.

Decisive tests: zero coefficients, signed/cross coefficients, and coefficients
depending on the differentiated output coordinate. The frozen definition
must remain valid without derivative-of-coefficient terms. m=6 is the local
number of rotations, NOT an active-block or volume count. C(w) retains its
genuine nome dependence; it is not AF-uniform.

Verification budget: root alone runs serialized narrow safe-launcher checks,
one 20-GiB worker, 12-GiB OS reserve, fresh live capacity preflights. Sol owns
only the finite envelope; root owns the actual-heat instance. Stop/revise if
the proof assumes a Hessian sign, discards action factors, imports another
carrier, requires limit raises or expands into unneeded generic scaffolding.

## Observed evidence

Three serialized focused checks PASS, with four printed declarations
depending only on {propext, Quot.sound}:

| Declaration | Source | Passing log |
| --- | --- | --- |
| `two_polynomial_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:74` | `/private/tmp/ym-oct7-six-polynomial-matrix3.log` |
| `six_polynomial_matrix_envelope_certificate` | `lean/YMGap/Continuum/QuaternionHaarSixPolynomialMatrixEnvelope.lean:134` | Same matrix log |
| `heat_frozen_six_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionFrozenSixHeatCurvature.lean:58` | `/private/tmp/ym-oct7-frozen-six-heat2.log` |
| `lastStep_frozen_six_score_curvature_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreCurvature.lean:64` | `/private/tmp/ym-oct7-frozen-six-original-score.log` |

Log SHA256, in the three-log order above:

```text
7bd0e0e6892d80a6068934434af5d4f10a77abdb330f092cdb9b70a47c931a9c
f47dfd9f2d640368cdea9eb97e14c5bbc48ca17d955dbc23eab0c4a75a1c9604
67a5f852735f6f92699c2ede3aef0c887f7f68f83f75db66ff48193daed5b1a4
```

Earlier elaboration failures were a pre-import module-comment form, a missing
parenthesis and defining namespace opens; they are not proof evidence.
No limits were raised. Root and Sol inspected the finite producer; independent
read-only review found no mathematical defect in its ordered-pair identity
or the actual factor/score instance. No new sorry, axiom, classical input,
canonical field change or scorecard closure. Root import registration only;
no full-root/tree audit or hashed-baseline refresh.

Observed capacity before the last two launches: 87--88% memory free, zero swap,
no competing compiler. Every check used one 20-GiB worker and 12-GiB reserve.
The universal polynomial-coefficient type includes zero, signed and
output-coordinate-dependent coefficients; the resulting expression is
explicitly frozen, with no differentiated coefficients. No separate numerical
test or original conditional-score inequality is claimed.

## Interpretation and next decision

CONTINUE at the whole-product frozen-Hessian/conditional Gram join. The local
adaptive restriction is removed; a global estimate is NOT supplied. Preserve
cross-block terms, the original interacting source/action and output weight,
actual normalization and terminal mismatch. Do not sum copies of a global
loss at every block or infer a conditional integrated Hessian sign.

The next finite algebraic target uses frozen jets d_p=sum(u_i*Di p),
e_p=sum(u_i*u_j*Di(Dj p)), with polynomial costs R_p,R_q:

```text
d_pq = d_p*q+p*d_q
e_pq = e_p*q+2*d_p*d_q+p*e_q
(R_p+R_q)*(p*q)^2+(p*q)*e_pq-d_pq^2
  = q^2*(R_p*p^2+p*e_p-d_p^2)+p^2*(R_q*q^2+q*e_q-d_q^2).
```

This is the proposed tensorization identity, NOT a newly checked declaration.
`lean/YMGap/Continuum/QuaternionHaarProductLogCurvature.lean:30`,
`productLogCurvatureLower`, has the scalar-cost version; the required
polynomial-cost and actual frozen-derivative pins remain missing.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:118`,
`kineticWeight_eq_indexedProduct`, is the SAME-kernel consumer pin.
Local costs should add as 6*C(w)*sum_s sum_i u_(s,i)^2; product cross terms
cancel in the log-Hessian numerator, not by claiming cross derivatives vanish.

The user's lattice-measurement note is already incorporated in
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and the live plan.
It changes no proof premise: fitted-channel masses are not every-state gaps,
and an exact discrete transfer logarithm does not bypass physical-clock or
limiting-theory identification. The SAME completed comparison, justified
scaling family, nontrivial survival and limiting QFT remain open. This local
certificate closes no broad chart node or Clay obligation.

## Next experiment: polynomial-cost tensorization

Selected target: construct the displayed product-jet identity, then instantiate
it with local frozen heat jets on the literal original product. The adaptive
coefficient restriction is already removed. The missing input here is additive
polynomial-cost assembly, not another scalar smoothing estimate.

Available inputs are the local six envelope, supported opposite-square
multiplication and the existing scalar product identity. Predicted result:
local costs add, cross products cancel exactly and no active-count multiplier
appears. Decisive tests: empty product, duplicate factors, arbitrary signed
and output-dependent coefficients. Differentiate only the heat factors, never
the coefficients. A recursive formal jet is not yet a direct differential
or conditional integral pin; keep that boundary explicit.

Verification budget remains serialized focused checks with one 20-GiB worker,
12-GiB reserve and fresh dynamic process/memory preflights. Root verifies;
Sol supplies only the finite product identity; an independent reviewer inspects
the actual join. Stop/revise if an integrated log-Hessian sign is assumed,
cross-block derivatives are dropped, source/action/output weights change or
the proposed consumer needs a missing derivative pin.

### Observed tensorization evidence

Three serialized focused checks PASS; six printed declarations use only
{propext, Quot.sound}:

| Declaration | Source | Passing log |
| --- | --- | --- |
| `polynomialJet_product_curvature_certificate` | `lean/YMGap/Continuum/QuaternionHaarPolynomialJetCurvature.lean:49` | `/private/tmp/ym-oct7-polynomial-jet-curvature.log` |
| `frozenSixHeatEnvelope_jet_pin` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:95` | `/private/tmp/ym-oct7-product-frozen-jets3.log` |
| `heat_frozen_six_jet_certificate` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:109` | Same product log |
| `productHeat_frozenJet_curvature_certificate` | `lean/YMGap/Continuum/SU2QuaternionProductHeatFrozenJetCurvature.lean:153` | Same product log |
| `lastStepScoreCoefficients_supported` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.lean:53` | `/private/tmp/ym-oct7-original-frozen-score-product.log` |
| `original_kinetic_frozenScoreJet_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFrozenScoreProductCurvature.lean:70` | Same original-score log |

Log SHA256 in the three-log order above:

```text
f9f1ae8b3fc81457d7eef94ad58958ea6932ac3648746edfc0cbbd155afd78be
7a7368679cfa73d66192262f51560fdd47fe9654aa3f743717638a693f1f4e40
079c9ac6e4340329594c57e1bdd727dfdfa99b523fc56af411bac47d662c8730
```

The first product attempt failed on a defining namespace; the second failed
because a constant-zero polynomial is not definitionally the empty zero list.
The repaired empty-product transport uses `RatPolyCoeffEqv.zero_smul`, not a
limit raise or changed claim. Those failed logs are not proof evidence.
Each launch had a fresh capacity/process preflight: 87--88% free, zero swap,
no competing compiler. No new source sorry/axiom/classical input or canonical
field change; root import registration only, no full-root/tree audit or
hashed-baseline refresh. Empty and duplicate-factor cases are in the universal
recursive theorem, not separate numerical claims.

### Interpretation and remaining exact joins

CONTINUE. The local matrix-to-heat-jet pin and additive polynomial-cost product
construction are checked, including the original kinetic base and actual
transfer-score coefficients. They do NOT yet assert that the recursive jets
equal a direct whole-kernel frozen angular sum. The missing differential pins
are precisely the first/second frozen Leibniz rules and factor localization;
coefficients must not be differentiated.

The subsequent conditional target retains the Hessian:
S_u^2 <= Noise*(R*A^2+A*F2(A)-F1(A)^2), with A=T a, and only under the
genuine positive conditional law and a justified source factorization/error
join. For arbitrary original c, do not silently set phi=c/a. The existing
incoming reciprocal/error construction remains required where appropriate.
Output coefficients must pull through head integration before this target is
an actual original-score statement. `partialHaarHeads_mul_lift` in
`lean/YMGap/Continuum/SU2QuaternionHeadChainComposition.lean:51` and
`angularDerivative_partialHaarHeads` in
`lean/YMGap/Continuum/SU2QuaternionHaarTailDerivative.lean:171` are the existing
pin inputs. Polynomial-column Gram alone does not supply the score column
F1(K)/K; a cleared square/order-reflection join is still missing.

Do NOT assume an integrated log-Hessian vanishes: free marginal cancellation
is only integral DD K=0. With full unweighted Haar and a constant angular
generator, H[h*D^2h-(Dh)^2]=-2*H[(Dh)^2]; conditional/action/output insertions
retain their own derivatives. No such sign or cancellation is imported here.

The nome cap still includes `heatSecondDerivativeCap/headFloor+relativeCap^2`
(`lean/YMGap/Continuum/SU2QuaternionHeatLogCurvature.lean:143`,
`secondRelativeCap`, and `:148`, `logCurvatureCap`). No useful near-one-nome
or physical scaling control is supplied by additive tensorization.
The broad chart and Clay status remain OPEN and unchanged.

## Decisive parameter screen selected before further derivative scaffolding

Independent source review identified a cap issue: the current entrywise bound
uses the reciprocal global heat floor. Before investing in more differential
joins, test the conservative cleared proposition

    4224 <= (1-w)^2 * logCurvatureCap(w).

Available inputs: the EXISTING `headFloor_le_nome_defect_square`,
`lean/YMGap/Continuum/BF4ExactSlabHeadFloorNomeCeiling.lean:61`; the zeroth-term
`prefix_bound`, `lean/YMGap/Continuum/SU2HeatPolynomialPrefixBound.lean:105`;
and the literal cap formulas. This screen concerns the chosen bound only,
NOT the true optimal curvature, any noise, retained signed Hessian or YM gap.

Predicted outcome: the screen passes; additive product algebra cannot make
this cap bounded or inverse-linear in the nome defect. If confirmed, prioritize
a sharper ONE-SIDED lower-curvature producer or the complete signed-cost route
over further wrappers around this entrywise cap. Cancellation/noise estimates
are not refuted and must not be dropped. The screen is a rational theorem
with the same gate/single-worker budget, not a numerical parameter sweep.
Observed evidence: focused check PASS, three declarations within
{propext, Quot.sound}:

- `prefixBudget_one_le`,
  `lean/YMGap/Continuum/SU2QuaternionLogCurvatureCapObstruction.lean:37`;
- `heatSecondDerivativeCap_ge_4224`, same source `:46`;
- `logCurvatureCap_nome_defect_square_lower`, same source `:59`.

Accepted log `/private/tmp/ym-oct7-log-curvature-cap-obstruction2.log`, SHA256
`71baf4d2702ff7f2426971442fecaa270a8d1985f7964acff9a7e508bdf80c95`.
An earlier failed check omitted the explicit reciprocal positivity proof;
the repair supplies the existing `headFloor_positive`, with no limit raise
or changed statement. No new source sorry/axiom/classical input or canonical
field change. The same fresh preflight/single-worker limits apply; no full
audit or root rebuild.

Decision: REVISE the analytic priority toward the one-sided producer or
complete retained signed-cost estimate. Bounded direct derivative pins remain
useful algebra, but do not treat this entrywise cap alone as a scaling
producer. Do not infer a theorem about noise or surviving variance from
a theorem about the cap. Independent review confirms this distinction and
the accurate recursive-versus-direct jet boundary.

### One-sided research benchmark, not a formal input

Hamilton's original *A Matrix Harnack Estimate for the Heat Equation*,
Corollary 4.4 (pp. 125--126), bounds the covariant log Hessian of a positive
heat-equation solution below by -g/(2*t) on compact manifolds with nonnegative
sectional curvature and parallel Ricci tensor; it explicitly includes spheres.
This is a possible one-sided benchmark, not a Lean theorem or finite-prefix
certificate. Root checked the original-paper transcription; direct publisher
PDF requests returned 403.
[Original paper transcription, Corollary 4.4](https://doczz.net/doc/7681685/a-matrix-harnack-estimate-for-the-heat-equation),
[publisher record](https://doi.org/10.4310/CAG.1993.v1.n1.a6).

Our inference for a possible route: prove the constructive kernel/heat-time
identification and one-sided lower-curvature estimate, then transfer it to
the original finite prefix using an explicit value/derivative deficit and
positivity margin. None of these joins is supplied by citing the paper.

There is a frame distinction: for a frozen ambient rotation field X(x)=B*x
on the unit sphere, its tangent acceleration is B^2*x+|B*x|^2*x. Consequently
D_X^2(log h) includes the covariant Hessian AND the log-gradient paired with
this acceleration. That term must be controlled or removed by a justified
frame change, not silently omitted. Constant left-invariant SU(2) directions
are a candidate geodesic frame in a bi-invariant metric, but their exact
comparison with the existing six-rotation jets is unproved here.

Do not confuse this desired LOWER bound with the stronger Ricci-two UPPER
curvature expression already refuted at the original antipode; see
`audits/AUDIT-ORIGINAL-ANTIPODAL-CURVATURE-2026-10-03.md`. Do not claim
any curvature method succeeds or fails from this benchmark. The actual
conditional Hessian, original source/action, output weight, normalization,
nontrivial survival and all-vector limiting-theory joins remain required.

## Next selected experiment: exact paired-score frame join

Target: write the SAME coupled-score energy in three paired directions,
without changing its action, source, terminal messages or output multiplier.
For Sij=A*Dij(b)-b*Dij(A), the first-jet pin Sij=xi*Fj-xj*Fi,
Fj=A*partial_j(b)-b*partial_j(A), implies the coefficient-exact identity
S01*S23-S02*S13+S03*S12=0. Consequently

    (S01+S23)^2+(S02-S13)^2+(S03+S12)^2 = sum_(i<j) Sij^2.

The opposite-sign triple has the same energy. Available inputs are literal
angular differentiation, `conditionalScore` and polynomial ring reflection.
The actual consumer is `exactScoreAngularBudget`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreBudget.lean:112`:
retain its A=g_(n+r+1), b=T^(r+1)(g_n*psi), Vbar^2*G^2, sigma and active list.
Predicted outcome: exact equality for arbitrary supported or unsupported
polynomial A,b and arbitrary multiplier, including zero scores; no inverse,
conditional-law restriction or stationary measure is needed. This removes
the energy-conversion obstruction to trying a three-direction producer, NOT
the missing producer, geometric frame identification or conditional join.

Verification budget: two narrow serialized checks, fresh dynamic preflights,
one 20-GiB worker and 12-GiB OS reserve. Sol implements finite algebra only;
root checks it and the original consumer. Revise if a sphere/unit-radius
hypothesis is needed for the coefficient identity, weights change, or an
unproved geodesicity/heat-time/Harnack claim is used as a premise.

### Independent Jacobi test (research calculation, not kernel evidence)

The SAME positive Jacobi derivative has a better hemisphere-local estimate:
with r_k=2*w^(2k+1)/(1+2*w^(2k+1)*x+w^(4k+2)), its positive-mixture
log Hessian retains E(r_k^2)+Var(r_k). For x>=0, sum r_k and sum r_k^2
are bounded respectively by 2*w/(1-w^2) and 4*w^2/(1-w^4), with no global
Euler-floor reciprocal. Original K(V*source) is not hemisphere-supported;
there is NO supplied global sector/payment join.

The proposed all-finite-Jacobi global inverse-linear bound fails its N=2
diagnostic: the polynomial is proportional to x+a, where
a=(w+w^-1+w^3+w^-3)/4. For 1<a<=2, at x=a-2/a its invariant radial log
Hessian is -a^2/(4*(a^2-1)); a-1 is quadratic in 1-w. This is a rational
research calculation, NOT a new Lean obstruction. It does not refute a
cutoff-dependent Jacobi route or the original guarded character prefix:
their exact value/derivative deficits must be paid. Do not import this
diagnostic as a theorem about the original transfer or its physical gap.

### Observed paired-score evidence

Both final focused targets PASS, with all eight printed public dependencies
within {propext, Quot.sound}:

| Declaration | Source |
| --- | --- |
| `decomposable_plucker` | `lean/YMGap/Continuum/QuaternionHaarConditionalScorePairedFrame.lean:54` |
| `conditionalScore_firstJet_pin` | Same source `:70` |
| `conditionalScore_plucker` | Same source `:103` |
| `plusSquare_eq_sixScoreSquare` | Same source `:192` |
| `minusSquare_eq_sixScoreSquare` | Same source `:204` |
| `plusSquare_weighted_pin` | Same source `:216` |
| `minusSquare_weighted_pin` | Same source `:222` |
| `pairedScoreAngularBudget_eq_exact` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepPairedScoreBudget.lean:66` |

Accepted logs, in this order:

```text
/private/tmp/ym-oct7-paired-score-frame-clean.log
ae6df76315d15b00b6d229ab0e9559cb037ab7633be643cd063bb5733e6fa4f0
/private/tmp/ym-oct7-original-paired-score-budget-clean.log
a1dc372e913053121744f42baa37fc4ebadb92626b2812e3b6014f0a16403007
```

The first frame compilation passed elaboration but FAILED the axiom gate:
private dependent finite-index congruences brought `Classical.choice` into
the energy identities. Intermediate axiom prints localized the dependency;
direct congruences at literal slots 0,1,2 removed it. The old and localization
logs are NOT accepted proof evidence. The initial original consumer also
failed on a missing defining namespace, subsequently supplied without changing
the statement. No new source sorry/axiom/classical input or limits change.
Fresh preflights before every launch showed no competing compiler, 87--88%
free and zero swap; checks ran sequentially with one 20-GiB worker and 12-GiB
reserve. Root registration only; no full-root/tree audit or baseline refresh.

Decision: CONTINUE with the exact three-score currency, NOT a geometric or
Harnack claim. The energy conversion is now proved for the original budget,
including zero/arbitrary sources and signed multipliers. Constructive frame/
heat identification, the genuine one-sided bound, actual conditional law,
normalization, retained signed cost and all scaling/Clay joins remain OPEN.
The user's lattice-measurement note remains incorporated in the existing
`audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md` and work-plan priority;
it supplies no numerical premise for this proof. No routine listing scan or
duplicated literature review was needed. The canonical broad chart is unchanged.

Independent read-only source review found no semantic issue: each triple
alone retains the original six-score energy without a radius/factor-two
correction, and the actual consumer adds no source-support, nonzero-source
or positive-sigma premise. It confirms the algebra-versus-geometric-curvature/
conditional/scaling boundary; the review itself is not compilation evidence.
