# SAME-source normalization and polynomial nome cost

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS. Four focused module checks passed, with 20
printed gates within {propext, Quot.sound}. Canonical chart unchanged.

## Actual mathematical increment

On the existing literal Wilson completion, retain the centered plaquette
v, the original physical-time transfer T, and y=(I-T)v. The preceding
original-action Ward argument supplied <v,y> >= s(w)/2. Completed
Cauchy--Schwarz and the existing ||v||^2<=4 now give

    ||y||^2 >= s(w)^2/16 > 0.

This is the actual source norm, not its preimage's norm. Combining this
floor with ||T^n y||^2<=4/(n+1)^2 gives an explicit relative tolerance
modulus: orbitModulus(epsilon*s(w)^2/16). It remains nome dependent.

We also expose that dependence without the global heat-product minimum.
Put delta=1-w, r=delta^3, F(C)=(5+2*C^2)*(2+3*C^2), and
C(w)=6*relativeCap(w,2048). Exact cancellation of the rational Jacobi
budget against D=(1-w)^2*(1-w^2), together with r<=D<=1, gives

    relativeCap(w,2048)*r <= 4097,
    C(w)*r <= 24582.

For 0<=r<=1, C*r<=A implies F(C)*r^4<=F(A), by separately bounding
(5+2*C^2)*r^2 and (2+3*C^2)*r^2. Taking the explicit positive reciprocal
and using s(w)=1/F(C(w)) gives

    delta^12 <= F(24582)*s(w).

Consequently, with the supplied constant K0=16*F(24582)^2,

    delta^24 <= K0*||y||^2,
    delta^24*||T^n y||^2 <= 4*K0/(n+1)^2*||y||^2.

The final consumer proves ||T^n y||^2<=epsilon*||y||^2 whenever the
explicit rational inequality 4*K0/(n+1)^2<=epsilon*delta^24 is supplied.
It does not assert that a physical scaling schedule satisfies that condition.

## Declaration path

Paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | Source | Exact role |
| --- | --- | --- |
| `budget_denominator_pin` | `BF4RelativePredictionNomeBudget.lean:56` | Cancels the actual Jacobi budget against D, yielding 2w |
| `denominator_ge_cubic`, `denominator_le_one` | `BF4RelativePredictionNomeBudget.lean:73`, `:86` | Bound D between delta cubed and one |
| `relativeCap_cubic_bound`, `selectedScore_cubic_bound` | `BF4RelativePredictionNomeBudget.lean:95`, `:119` | Supply 4097 and 24582 for the original coefficients |
| `predictionFactor_fourth_scale` | `RationalRelativePredictionScaling.lean:72` | Generic fourth-power coefficient estimate |
| `fourth_le_factor_times_floor` | `RationalRelativePredictionScaling.lean:114` | Positive reciprocal gives a denominator-cleared lower floor |
| `relativeDefectNormFloor` | `BF4WilsonAllNomeRelativeDefectNormalization.lean:45` | Explicit rational s(w)^2/16 |
| `plaquette_relative_defect_norm_floor` | `BF4WilsonAllNomeRelativeDefectNormalization.lean:81` | Applies completed Cauchy--Schwarz to the actual original source |
| `plaquette_defect_orbit_relative_small` | `BF4WilsonAllNomeRelativeDefectNormalization.lean:114` | Relative decay with the explicit existing orbit modulus |
| `polynomialNormBudget`, `normWeight` | `BF4WilsonAllNomePolynomialDefectBudget.lean:42`, `:45` | Supply K0 and delta^24 as rational data |
| `prediction_polynomial_floor`, `polynomial_norm_floor` | `BF4WilsonAllNomePolynomialDefectBudget.lean:59`, `:69` | Instantiate the actual nome-dependent floors |
| `plaquette_defect_polynomial_norm_floor` | `BF4WilsonAllNomePolynomialDefectBudget.lean:117` | Clears denominators against the SAME completed source norm |
| `plaquette_defect_polynomial_orbit_bound` | `BF4WilsonAllNomePolynomialDefectBudget.lean:126` | Original physical-time orbit with explicit nome/time budget |
| `plaquette_defect_polynomial_relative_small` | `BF4WilsonAllNomePolynomialDefectBudget.lean:146` | Cancels positive delta^24 under the displayed scalar condition |

All completed estimates quantify every rational 0<w<1, every width, and
every supplied physical spatial plaquette at that width. No active-link
guard is added. The existing source, action, inner product and time operator
are retained. This does not generalize the SU(2) inputs to every group.

## Scaling boundary and next test

K0 is nome and width independent, but the relative estimate costs
delta^(-24). There is no spacing parameter in these declarations, hence
no asserted uniformity in physical spacing. The original heat-cutoff
modulus still depends on the heat minimum; this result does not change it.

The actual existing upper bound on the unnormalized source is
`BF4WilsonAllNomePlaquetteDefectOrbit.plaquette_defect_nome_bound`:
||y||^2<=192*(1-w), with its explicit active-link guard. The new lower
floor is compatible with that vanishing bound, not a contradiction to it.

The separately inspected `BF4PhysicalChangingNomeDynamicFamily.lean`
defines `changingNome` as 1/(scale+3) at line 40, `changingSpacing` as
1/(scale+2) at line 63, and `changingNomeDynamicFamily` at line 76.
That bundle uses the legacy cutoff vacuum-sector completion. No pin to
the literal Wilson completion was found in that module. Its schedule
must not be silently used as physical calibration of these new estimates.

NEXT: use the visible budget to test a justified SAME-object trajectory
at matched physical time. A surviving candidate also needs a positive-time
lower response, which none of these upper estimates supplies. If the local
defect fails that test, reconsider the observable and its physical support
before building further survival interfaces. No actual scaling family has
been ruled out by the new declarations alone.

The every-state gap, spatial/scaling passage, nontrivial continuum survival,
finite positive physical mass, full same-theory QFT and every-group fields
remain OPEN. No canonical frontier field was altered or discharged.

## Verification boundary

The main agent serialized all four checks through the safe launcher: one
worker, hard 20 GiB worker cap, 12 GiB OS reserve, dynamic pressure/swap
monitoring. Sol supplied the generic scaling and completed normalization
proofs; Luna performed read-only API and scaling-source checks. A separate
Sol review confirmed the powers, factors, source and operator scope.

| Focused module | Gates | Final log under `/tmp/` |
| --- | ---: | --- |
| BF4RelativePredictionNomeBudget | 7 | ym-relative-nome-budget-20260930.log |
| RationalRelativePredictionScaling | 2 | ym-relative-prediction-scaling-20260930.log |
| BF4WilsonAllNomeRelativeDefectNormalization | 4 | ym-relative-defect-normalization-20260930.log |
| BF4WilsonAllNomePolynomialDefectBudget | 7 | ym-polynomial-defect-budget-20260930.log |

All 20 printed gates are within {propext, Quot.sound}; no sorryAx.
Failed draft checks are not counted. Root imports are registered, but no
aggregate-root build, broad audit or guard was run. CI remains disabled.
No new sorry, custom axiom, unsupplied analytic bound, surrogate carrier or
weakened frontier was introduced; no old ledgered sorry was discharged.
