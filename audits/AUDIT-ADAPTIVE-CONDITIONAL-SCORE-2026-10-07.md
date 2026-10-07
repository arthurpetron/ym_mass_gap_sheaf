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
