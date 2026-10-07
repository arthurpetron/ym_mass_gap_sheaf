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

## Next experiment: actual paired scalar jets and global transverse producer

The previous checkpoint is PROGRESS: `71419b7c` supplies checked original
score/budget equalities and is pushed to main. This continuation preserves the
unchanged Clay objective and the original action. Two bounded mathematical
tasks meet at the relative scalar, rather than growing cap-only wrappers.

1. Prove actual paired second scalar jets on blocks 0/1: Ji^2(x)=-x and
   JiJj(x)+JjJi(x)=0 for distinct directions, hence the frozen polynomial
   contraction is -(sum ui^2)*x. Available inputs: the literal relative scalar,
   supported angular carrier differentiation and finite canonical checks.
   Coefficients ui must not be differentiated. Arbitrary-block recoding and
   a geometric heat/PDE identification are separate, not implied by this pin.
2. Construct a GLOBAL one-sided transverse polynomial certificate for the
   literal Jacobi heat h and its ACTUAL formal scalar derivative h_x:

       C_T*h^2-x*h*h_x >= 0,   C_T=2*w/(1-w^2).

   No density-floor reciprocal belongs in C_T. The full interval is covered
   by the exact affine identity, with c=w^(2k+1):

       f-x = ((c^2+2c)*(1+x)+((c-1)^2+1)*(1-x))/2,
       f=1+2*c*x+c^2.

   Retain the Euler factor. Simultaneous positive product/derivative
   induction adds 2*c at each factor; the finite geometric sum is bounded by
   C_T. Use the actual QPoly formal derivative and coefficient identities,
   not merely a recursively defined jet. Initial empty/constant heat cases,
   x=+/-1, full signed x and the normalization are decisive checks.

The second target is an actual partial curvature producer, NOT a global
matrix lower bound: the negative-hemisphere radial mixing inequality remains
unsupplied. The scalar certificate's angular/substitution pin, exact weighted
character join, and transport to the original UNWEIGHTED prefix must be
proved before an original transfer estimate is claimed. Existing absolute
deficits may use the heat floor in their tighter CUT OFF tolerance without
placing its reciprocal in the final curvature cost; the current cutoff alone
does not supply that transport. No global hemisphere assumption is allowed.

Sol implements the bounded leaves; root serializes focused verification,
using one 20-GiB worker, 12-GiB reserve and a fresh dynamic preflight at every
launch. Revise if the actual derivative pin is absent, finite cutoffs or
unit-radius endpoints are dropped, or a full radial/matrix result is inferred
from the transverse leg. No new hypothesis bundle, canonical field change,
routine literature scan or chart reprint is planned.

### Observed scalar-jet and transverse evidence

Both final focused targets PASS. All fourteen printed public dependencies
are exactly {propext, Quot.sound}; no new source sorry/axiom/classical input.

| Declaration | Source |
| --- | --- |
| `pairedScorePlus_zero_derivative_pin` | `lean/YMGap/Continuum/SU2QuaternionPairedFrameScalarJets.lean:54` |
| `pairedDerivative_carrier` | Same source `:90` |
| `relativeScalar_supported` | Same source `:105` |
| `relativeScalar_second_jet` | Same source `:129` |
| `relativeScalar_mixed_jet` | Same source `:139` |
| `frozenScalarSecondJet_pin` | Same source `:212` |
| `frozenScalarSecondJet_weighted_pin` | Same source `:243` |
| `product_formal_derivative_pin` | `lean/YMGap/Continuum/JacobiHeatTransverseCurvature.lean:112` |
| `factor_transverse_certificate` | Same source `:185` |
| `productDerivative_transverse_certificates` | Same source `:234` |
| `transverseCap_denominator_pin` | Same source `:289` |
| `transverseCap_nome_defect_le_one` | Same source `:301` |
| `transversePrefixCost_le_cap` | Same source `:319` |
| `heat_transverse_curvature_certificate` | Same source `:334` |

Accepted logs and SHA-256:

```text
/private/tmp/ym-oct7-paired-scalar-jets-final.log
a1af551a8ae2d384203dd16b7411f9128c2de5af78a6384bf48e7a816f984b5e
/private/tmp/ym-oct7-jacobi-transverse3.log
6dbf688f5c492008d7f0bc43ff312f27415bade37d5ab1e2696318af0ebab4d6
```

The earlier transverse logs are FAILED elaboration, not accepted evidence.
Repairs used named coefficient negation, explicit polynomial/constant
arguments and exact finite-sum normalization; no mathematical hypothesis
changed. Fresh preflights before each launch showed no competing compiler,
87--88% free and zero swap. Verification was serialized with one 20-GiB
worker and 12-GiB reserve. Root import registration only; no full-root/tree
build, full axiom audit or baseline refresh was run.

Independent read-only source review found no material issue: actual second
jets precede multiplication by frozen u, interval certificates retain both
1+x and 1-x, and the formal derivative/Euler/normalization pins are literal.
Its review was not compilation evidence. No geometric group flow, covariant
matrix Hessian, original unweighted heat, OS norm or physical gap is claimed.

Decision: CONTINUE. The transverse coefficient has the desired inverse-linear
nome-defect scale, unlike the prior constructed entrywise cap. The negative-
hemisphere RADIAL mixture is the substantive missing estimate. With
r_k=2*c_k/(1+2*c_k*x+c_k^2), c_k=w^(2*k+1), S_m=sum r_k^m, the still-unproved
denominator-cleared radial target is

```text
C*S1^2 >= (1-x^2)*(S2*S1^2-2*S3*S1+S2^2)
              + x*(S1^3-S1*S2),   C=O(1/(1-w)), N>=N0(w).
```

This is a research target, not a new Lean premise or assertion of an available
cutoff N0. The N=2 diagnostic above prevents claiming it for all finite N.
Scalar substitution/angular heat pins, arbitrary-block recoding, exact
weighted-character derivative transport and the original unweighted cutoff
join must also be established before an original conditional matrix estimate.
Complete signed cost, normalization, independent survival, completed
comparison, physical/volume control, SAME limiting QFT and every-group/Clay
requirements remain OPEN. Supporting proofs change none of the canonical
chart's displayed broad claims; no chart is reprinted.

The current pasted note
`/Users/darthur/.codex/attachments/cf965d8e-085c-42c2-a303-16f0ae70d860/Pasted text.txt`
was read against the existing lattice-mass research audit and work-plan
priority. Its useful numerical-channel versus physical-generator distinction
is already incorporated there, together with finite-spacing and regularity
corrections. No measured mass, transfer/Hamiltonian identification or continuum
regularity hypothesis was imported into these certificates; no duplicate
paper review or routine listing scan was performed.

### Radial experiment selection: retain the product/mixture cancellation

Independent bounded mathematical review supplies a decisive endpoint screen,
checked algebraically by root but NOT yet a Lean theorem. At x=-1 and N>=1,
set r0=2*w/(1-w)^2. Pairing the terms of the finite geometric sum gives

```text
1-w^(2k+1) >= (2k+1)*w^k*(1-w),
r_k(-1) <= r0/(2k+1)^2,
sum_(k=1)^(N-1) 1/(2k+1)^2 <= sum 1/[4k(k+1)] <= 1/4.
```

Thus S1<=5*r0/4 and S2>=r0^2, so S2/S1>=4*r0/5. The COMPLETE radial
endpoint is S1-S2/S1>=0 since S1^2>=S2; however the isolated mixture
contribution is -S2/S1, necessarily of inverse-quadratic nome-defect size.
This persists at arbitrarily large finite cutoffs. Separately imposing
inverse-linear floors on product and mixture therefore cannot prove the
desired joined bound. PRUNE that split, NOT the full radial/onset target,
the original action, or Yang--Mills. The next producer must retain their
cancellation (and the radial positive-mixture variance); no premise or
canonical frontier field changes. This screen is mathematical research
evidence, kept distinct from the fourteen kernel-checked gates above.

## Next bounded experiment: contract radial mixture to product curvature

Root verified the exact scalar cancellation, but no Lean result is yet claimed
in this section. Put a=1-x^2, D=a*S2+x*S1, with S_j the finite r-power sums.
The cleared radial numerator is exactly

```text
Lnum = -(S1^2-S2)*D + 2*a*(S1*S3-S2^2).
C*S1^2+Lnum = (C-D)*(S1^2-S2)+C*S2+2*a*(S1*S3-S2^2).
```

Available constructive finite inputs: r_i>=0, so S1^2-S2>=0 and
S1*S3-S2^2>=0, the latter by weighted squared pair differences. Thus a>=0,
C>=0 and the PRODUCT bound D<=C suffice. No reciprocal S1 or heat floor is
needed, and the empty prefix is included. The direct consumer is the radial
research target above; this is a strictly sharper mathematical reduction,
not an assumed original gap or new frontier bundle.

Sol implements the finite rational identities/positivity; root alone runs the
focused 20-GiB check after a fresh preflight. An independent read-only review
locates the exact remaining same-product Gaussian/second-derivative input.
Predicted outcome: finite cancellation contracts; the Poisson/curvature input
remains open. Revise if any moment is not the actual finite prefix, positivity
is silently assumed instead of proved, a division excludes zero prefixes, or
a Poisson equality/physical time is inferred from the algebra. Auxiliary
circle time t_theta=-log(w) must not be identified with the carrier time
-4*log(w) or standard g^2=-8*log(w). No geometric or continuum closure.

### Narrow analytic route, without importing a classical premise

The underlying P(w,cos(theta)) is the theta3 product at angle theta/2, not
the SU(2) derivative heat itself. The product normalization and modular
transformation are classical benchmarks in
[NIST DLMF 20.5.3](https://dlmf.nist.gov/20.5.E3) and
[20.7.32](https://dlmf.nist.gov/20.7.E32). Root's inference from those formulas:
for auxiliary circle time t_theta=-log(w), P is proportional to the positive
wrapped Gaussian sum G=sum_j exp(-(theta-2*pi*j)^2/(4*t_theta)). Its cleared
log-Hessian is -G^2/(2*t_theta) plus a nonnegative weighted variance. This
suggests D_infinity<=1/(2*t_theta), NOT an imported constructive theorem.

For a cutoff with w^(2*N+1)<=1/8, the negative product tail costs at most
sum_(k>=N) r_k<=8*w^(2*N+1)/(1-w^2)<=1/(1-w). Together with
t_theta>=1-w this suggests C=3/[2*(1-w)] for the finite joined radial
expression. These are research estimates pending actual derivative, tail
and limit proofs, not an available physical bound or established Lean cutoff.

The needed analytic join is specifically the SAME theta3 PRODUCT's Gaussian
identity and first/second angular derivative control with explicit moduli.
Do not unnecessarily demand a full SU(2)/Faraut image formula or its sine-
denominator endpoint removal: h is reached through finite algebra instead.
Existing `JacobiTripleProductOnBox.thetaProduct_eq_fullThetaSeries`
(`lean/YMGap/Continuum/JacobiTripleProductOnBox.lean:91`) already identifies
the all-nome on-box product with the normalized cosine series. It does not
prove the Poisson/Gaussian or second-derivative join. `JacobiModularCReal`
explicitly withholds modular inversion, and the Faraut image formulas remain
supplied inputs. No classical source is added as a Lean axiom or hypothesis;
angle/carrier, finite-to-limit and physical-time identifications stay OPEN.

### Observed finite radial cancellation evidence

The final focused target PASSes all seven gates within {propext, Quot.sound}.
The first three moment nonnegativity theorems use propext only.

| Declaration | Source |
| --- | --- |
| `M1_nonneg` | `lean/YMGap/Continuum/JacobiHeatRadialMixtureCancellation.lean:50` |
| `M2_nonneg` | Same source `:54` |
| `M3_nonneg` | Same source `:57` |
| `first_square_gap_nonneg` | Same source `:63` |
| `moment_variance_nonneg` | Same source `:112` |
| `radialNumerator_cancellation` | Same source `:157` |
| `radialMixture_payment_nonneg` | Same source `:177` |

Accepted log and SHA-256:

```text
/private/tmp/ym-oct7-radial-mixture2.log
0abeaf288548027f0a0b4267a1c4bde6a26a75dfa1be4382f716ca65c07d7f0d
```

Initial elaboration failed on a missing convenience congruence, unreduced
empty-prefix goals and a function-pattern layout. Root used the core rational
congruences and explicit empty reduction; no hypotheses changed. No source
sorry/axiom/classical input. Both preflights showed no competing compiler,
87--88% free and zero swap; one 20-GiB worker, 12-GiB reserve. No full-root/tree
build/audit or baseline refresh. This is finite rational algebra, not yet an
actual angular heat inequality.

Independent read-only review confirmed the actual moment sums, constructed
variance/pair positivity, empty case and full signed numerator/payment. It
also confirmed the narrower missing theta3 circle-Gaussian bridge: no full
SU(2) Faraut sine-denominator formula is needed for this route. The review
itself is not compilation evidence.

Decision: CONTINUE from the PROVED finite reduction to a genuine product
curvature producer and SAME heat-jet/cutoff/conditional joins. No separated
mixture floor, global density-floor cost, or classical Poisson premise is
introduced. The finite derivative/moment identifications, Gaussian derivative
limits, useful original signed cost, scaling, independent survival, completed
comparison and all physical/continuum/Clay obligations remain OPEN. Together
this continuation checks three focused leaves and twenty-one public gates,
without changing any canonical displayed broad claim. No chart reprint.
