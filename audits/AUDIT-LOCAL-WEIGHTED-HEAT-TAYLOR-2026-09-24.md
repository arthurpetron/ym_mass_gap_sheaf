# Finite local weighted heat: first-order cancellation and explicit remainder

2026-09-24 UTC, following `f34a875`. New finite Lean mathematics, not a
continuum, physical-Hamiltonian, or Clay closure.

## Exact object and result

Use the ORIGINAL `heatPair` with shared spectators at
`lean/YMGap/Continuum/SU2QuaternionHeadHeatDiagonal.lean:52`.
Write H for the original Haar integral on `tail+1` quaternion blocks,
epsilon=1-w, and c_d=d(d+2). For the computed complete harmonic-degree
groups p_d of p, define

    B(p,q) = sum_d c_d^2 * abs(H[p_d*q]),
    R(p,q) = sum_d (attenuation(w,K,d)-1+epsilon*c_d)*H[p_d*q].

These are explicit finite rational data, not existential constants:
`pairBudget` at
`lean/YMGap/Continuum/SU2QuaternionHeadHeatWeightedTaylor.lean:59` and
`pairRemainder` at the same path, line 52. Grouping retains all signed
contributions within each degree before taking absolute values.

`heatPair_taylor` at
`lean/YMGap/Continuum/SU2QuaternionHeadHeatWeightedTaylor.lean:103` proves

    heatPair(p,q) = H[p*q] + epsilon*H[(L p)*q] + R(p,q),

for arbitrary rational w, cutoff K, supported p and arbitrary q. This is a
setoid equality, with no positivity, low-degree, or eigenvector premise.
L is the existing six-plane angular Laplacian, not an identified physical
Hamiltonian.

For `0<=w<1` and `sufficientCutoff w<=K`, `pairRemainder_le` at line 147
proves `R(p,q)<=epsilon^2*B(p,q)`. The final actual weighted local energy
and its upper bound are `weightedEnergy` and
`weightedEnergy_le_angular_add_quadratic`, respectively at lines 155 and 162:

    E(a,f) = heatPair(a,a*f^2) - heatPair(a*f,a*f),
    E(a,f) <= epsilon*H[a^2*Gamma(f)] + epsilon^2*B(a,a*f^2).

Both a and f are supported on the same `tail+1` blocks. They may be signed;
in particular positive physical sources are not excluded. This is an
UNNORMALIZED local energy, not an OS norm-relative estimate.

## Why the cancellation is genuine

`polynomial_pair_decomposition` and `polynomial_generator_pair` at
`lean/YMGap/Continuum/SU2QuaternionHeadAngularPair.lean:63` and line 194
identify the zeroth-order and Casimir-weighted mixed sums with the SAME
original polynomial Haar pairings. No head-independent multiplier is assumed.

The scalar input is
`cutoffRemainder_bounds_of_sufficientCutoff` at
`lean/YMGap/Continuum/SU2HeatCutoffTaylorRemainder.lean:159`. It reuses
`secondOrder_qpow` at `lean/YMGap/Continuum/BondMovingQuadratic.lean:137`
for retained degrees. For omitted
degrees, the existing cutoff guard implies epsilon*c_d>=1, and hence
`0<=epsilon*c_d-1<=epsilon^2*c_d^2`. There is NO requirement that the
polynomial/source degree be below K.

The final proof combines the mixed Taylor identity with
`polynomial_defect_le_angular` at
`lean/YMGap/Continuum/SU2QuaternionHeadHeatDiagonal.lean:234`, applied to a*f,
and `weighted_angular_cancellation` at
`lean/YMGap/Continuum/QuaternionHaarWeightedAngularCancellation.lean:123`:

    H[Gamma(a*f)] + H[a*f^2*L a] = H[a^2*Gamma(f)].

Thus source derivatives disappear at FIRST order. The diagonal defect is
bounded as a whole; no separate absolute remainder for a*f is charged.
The mixed source remainder is still explicit and generally signed.

## Precise missing consumers

1. **Full product.** `productMap_range_cycle_carrier` at
   `lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicFold.lean:144`
   uses successive fresh-output cyclic steps. `cycleReturn_step_carrier`
   and `cycleStep_rotated_defect_le_head_energy` at
   `lean/YMGap/Continuum/SU2QuaternionProductHeatCyclicRotation.lean:144`
   and line 168 retain the coordinate rotation/conjugation. They do not
   identify the full endpoint-weighted product energy with one fixed
   shared-spectator `weightedEnergy`. The new theorem supplies a LOCAL
   estimate; transporting sources, observables and budgets through the
   actual product remains unproved here. Likewise
   `productHeat_selected_expansion` at
   `lean/YMGap/Continuum/SU2QuaternionProductHeatHarmonicExpansion.lean:119`
   retains other heat factors inside a doubled-carrier insertion.
2. **Quantitative usefulness.** B has no explicit w or K argument only
   because its complete input polynomials carry that dependence. For
   a=a(w,K,width,depth), its size may grow with ALL these parameters.
   An epsilon-squared prefactor alone is not a scaling-small error.
   SAME normalization/variance control must be established for an actual
   justified family before promoting this estimate as a survival producer.
3. **Completed/physical target.** The intended eventual consumer remains
   `centered_relative_energy` at
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`.
   No antecedent for a useful changing-scale family is supplied here.
   The separate all-vector gap, spatial/continuum passage, same-theory
   Hilbert/OS/QFT and Hamiltonian identification, and every-group target
   remain open. No canonical frontier field is changed or inhabited.

## Verification and review

Final serialized direct checks passed with one worker and a 4 GiB ceiling:

- `/tmp/ym-gap-cutoff-taylor-check-4.log`: 3 printed gates.
- `/tmp/ym-gap-head-angular-pair-check-3.log`: 2 printed gates.
- `/tmp/ym-gap-head-weighted-taylor-check-1.log`: 6 printed gates.

All eleven printed dependencies are within `{propext, Quot.sound}`; no
`sorryAx` or warnings in these final logs. Earlier failed drafts are not
verification evidence. The weighted file's subsequent change corrected only
a docstring about bounding the diagonal defect. A semantic-root import was
added, but no full-root build, full axiom audit, guard, or progress metric ran.

Sol supplied scalar and mixed-generator drafts and independently reviewed
the upper-bound sign and the shared-spectator/full-product boundary. Root
assembled and proved the weighted estimate, corrected and checked the leaves,
and preserved the open scaling and same-object obligations.

## Error-free full-product alignment follow-up

2026-09-24 UTC. This is a different, exact finite fusion argument for a
particular four-coordinate multiplet. It does NOT transport the general local
Taylor energy estimate through the full product or bound its source budget.

Write c_j=(j+1)*w^(j*(j+2)), 0<=w<1. At K>=sufficientCutoff(w), the
denominator cutoff gives K*(1-w)>=1. Cleared reciprocal Bernoulli then gives
`2*(K+1)*w^(2*K+4)<=K`, hence `c_1*c_K<=c_(K-1)`.
The public producer is `SU2HeatFusionCutoffPositive.endpoint_coeff_le` in
`lean/YMGap/Continuum/SU2HeatFusionCutoffPositive.lean`.

At prefix length K+1, combine the last bulk coefficient with the negative
boundary BEFORE estimating either. Its coefficient becomes
`c_K-c_1*c_(K+1)>=0`; the remaining upper boundary coefficient is positive.
Existing SU(2) dimension/Casimir convexity handles all interior coefficients.
`prefix_alignment_no_error` at
`lean/YMGap/Continuum/SU2QuaternionHeatFusionCutoffPositive.lean:79`
uses actual character-quadratic positivity, not pointwise residual positivity.

The complete original product P, any supported signed source a, and the SAME
mass Z=H[P*a(x)*a(y)] satisfy, for every selected link i,

    c_1*Z <= H[P*a(x)*a(y)*chi_1(y_i*conj(x_i))],
    H[P*a(x)*a(y)*||x_i-y_i||^2] <= (2-c_1)*Z <= 6*(1-w)*Z.

These are `product_alignment_no_error`, `product_displacement_bound`, and
`product_displacement_nome_bound` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatExactAlignment.lean:59`,
`:115`, and `:141`. They retain every factor, allow repeated selected links,
and need no pointwise source certificate or source-degree/cutoff comparison.
The upper inequality for signed a does NOT assert that the left quadratic
form is nonnegative. Cauchy--Schwarz for that form does not follow; the
proved positive form is the upper-bound residual, not the displacement form.

The actual slab consumers are `exact_alignment_cleared`,
`exact_alignment_normalized`, `exact_alignment_normalized_of_cutoff`, and
`exact_link_displacement_nome_bound` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialExactKineticAlignment.lean:59`,
`:81`, `:95`, and `:106`. They use a=spatialWeight*terminalMessage, literal
edgeDensity and original oddMass. Normalization uses the existing positive
mass and alignmentMean; `exactCutoff` at line 93 computes the maximum of
headCutoff and sufficientCutoff. Both coefficient and onset are independent
of width, depth and source; neither is claimed independent of nome.

**Remaining analytic join:** for a bilinear product form B, the actual
weighted temporal energy involves `B(a,a*f^2)-B(a*f,a*f)`. The new diagonal
source inequality alone gives no useful comparison of this difference with
the SAME centered Wilson variance. Individual coordinate insertions are not
gauge-invariant Wilson observables. The previous plaquette increment/floor
obstruction is not removed, nor is continuum survival, spatial/scaling gap
control, physical mass, full QFT/YM identification or every group supplied.

Four serialized one-worker 4 GiB checks passed, with twelve printed gates:

- `/tmp/ym-gap-heat-fusion-cutoff-positive-check-2.log`: three gates.
- `/tmp/ym-gap-quaternion-fusion-cutoff-positive-check-4.log`: one gate.
- `/tmp/ym-gap-product-heat-exact-alignment-check-1.log`: three gates.
- `/tmp/ym-gap-slab-exact-kinetic-alignment-check-3.log`: five gates.

All accepted logs have terminal success, no errors/warnings/sorryAx, and only
permitted dependencies (or no axioms). No full-root build/audit/guard ran.
Sol supplied scalar/prefix/physical drafts and a parallel scope review;
root corrected, composed and kernel-checked the chain. No new hole, axiom,
frontier-field weakening or canonical closure. The semantic root imports
the physical consumer; that aggregation itself was not rebuilt.

## SAME odd-marginal centered Ward follow-up

`QuaternionHaarCenteredLinearWard.centered_linear_ward` applies angular
integration by parts to `W*(f-c)*D f`, retaining both product-rule terms.
For exact head degree one, the six-plane angular Laplacian is `-3*f`.
The computed own-mean specialization `centered_linear_ward_own_mean` gives

    H[W*Gamma(f)] + sum_(i<j) H[(f-c)*(D_ij W)*(D_ij f)]
      = 3*H[W]*Var_W(f),    c=H[W*f]/H[W].

W may depend on the selected block. The raw identity uses no positivity
assumption; the normalized version supplies an explicit positive mass.
Neither result bounds the signed sum or asserts it is nonnegative.

`BF4ExactSlabFixedSpatialPlaquetteDegree.plaquette_degree` counts actual
incident oriented links in the literal fixed-spatial word. Each selected
incident link has multiplicity one. `plaquette_character_degree` uses the
exact spin-1 polynomial `2*scalar`, not a parity/center-charge surrogate.
`plaquette_character_head_degree` moves the selected slot by the existing
explicit block involution.

`BF4ExactSlabFixedSpatialCenteredWard.plaquette_centered_ward` is the concrete
consumer. Its W is only a reindexing of
`BF4ExactSlabFixedSpatialActualMarginalDual.marginalWeight`, namely
`(V*g_n)*g_(n+1)`. `frameMass_pin` returns the Haar mass to `oddMass`;
`frameMoment_pin` and `frameVariance_pin` return the normalized moments to
the pre-existing `middleRatio (n+1) n`. Both messages, spatial weight,
partition, observable and center therefore agree with the original chain.
The derivative of `g_(n+1)` remains in the residual. No equation replacing
consecutive messages by a stationary source is introduced.

### Remaining analytic input

This is an exact identity, not an improvement of the temporal-energy bound.
For this route, a lower signed estimate `R >= -rho*Z*Var` would yield
`H[W*Gamma(f)] <= (3+rho)*Z*Var`. It does not require `rho<3`; it does require
parameter dependence adequate for a justified changing-scale family, plus
the still-missing comparison to the full original temporal energy. The local
Taylor estimate above carries `a^2`, not this marginal W. Changing weights
would change the variance/partition and needs its own proved comparison.

Source review found local Ward-response/score-cost bounds, not an estimate
of this complete odd-marginal residual with useful scaling. In particular
`BF4ExactSlabLocalWardVariance.normalizedResponse_squared_le_variance_cost`
concerns its displayed full-slab score response and actual score cost; it
does not furnish the needed bound on this fixed-spatial residual. No new
conditional wrapper is introduced around that missing estimate. Spatial/
spacing control, continuum survival, physical Hamiltonian calibration,
same-theory QFT/YM identification and every-group closure remain open.

### Verification of the Ward join

Three serialized one-worker 4 GiB checks passed:

- `/tmp/ym-gap-centered-linear-ward-check-3.log`: four gates.
- `/tmp/ym-gap-fixed-spatial-plaquette-degree-check-5.log`: four gates.
- `/tmp/ym-gap-fixed-spatial-centered-ward-check-3.log`: six gates.

All accepted checks terminated successfully with only {propext, Quot.sound}
and no errors/warnings/sorryAx. Sol and Luna supplied independent drafts;
root corrected the algebra/incidence proofs, composed the actual marginal
consumer and serialized verification. A parallel source review checked its
same-object and signed-residual boundaries. No new hole, axiom, frontier-field
change or full-root build/audit/guard; the added semantic import was not
itself rebuilt.

## Positive heat-law angular/variance obstruction

The comparison now has a constructive diagnostic on an actual positive heat
functional. Let x be the scalar part of `exposedFourWord r0 r1 r2 r3`,
f=`characterPolynomial x 1`, and h=`heatPrefix w K x`. The carrier contains
the four quaternion blocks (3<blocks). This is one central heat prefix on
the composite holonomy, NOT four independent link-heat factors and NOT the
interacting odd marginal `(V*g_n)*g_(n+1)`.

The exact identities for K>=2 are:

    H[h]=1,  E_h[f]=2*w^3,  E_h[f^2]=1+3*w^8,
    Var_h(f)=1+3*w^8-4*w^6,
    E_h[Gamma(f)]=3*(1-w^8).

Here Gamma sums the six angular planes at ONE selected/head link.
`heat_mass`, `heat_fundamental_moment` and `heat_fundamental_square_moment`
are at `lean/YMGap/Continuum/QuaternionHaarExposedHeatMoments.lean:233`,
`:246` and `:264`. Fusion leaves only heat labels zero, one and two in
these moments. `exposedFundamental_angularSquare` at
`lean/YMGap/Continuum/QuaternionHaarExposedFundamentalEnergy.lean:235`
proves Gamma(f)=4-f^2 with every Haar insertion retained, by the angular
Leibniz rule and the first two Casimir identities. `normalized_mean`,
`normalized_variance` and `normalized_angular` at
`lean/YMGap/Continuum/QuaternionHaarHeatAngularVarianceObstruction.lean:73`,
`:81` and `:100` use the SAME density, mass and centered mean.

`radialRate_le_eight_scaled_angular` at
`lean/YMGap/Continuum/SU2QuaternionHeatCovarianceRates.lean:149` and its
normalized consumer `variance_le_eight_scaled_angular` at
`lean/YMGap/Continuum/QuaternionHaarHeatAngularVarianceObstruction.lean:136`
give `Var_h(f) <= 8*(1-w)*E_h[Gamma(f)]`. Thus the bare first-order angular
budget is not a vanishing relative-loss certificate for this observable.
It is an upper-bound BUDGET, not actual temporal energy: the inequality
does not give a temporal-energy lower bound or refute actual survival.

For any proposed C>=0, `obstructionNome` at
`lean/YMGap/Continuum/SU2QuaternionHeatCovarianceRates.lean:213` computes
w=1-1/(24*(C+1)), with 0<w<1 and 24*C*(1-w)<3. The quadratic upper bound
on variance and linear lower bound on angular energy refute
E_h[Gamma(f)]<=C*Var_h(f). `positiveCounterexample` at
`lean/YMGap/Continuum/QuaternionHaarHeatAngularVarianceObstruction.lean:170`
returns K=max(onset,max(2,headCutoff w)), a certificate for this exact h,
and the failed inequality. Hence the witness survives ANY requested late
cutoff onset. The positivity producer is `exposedHeatPrefixCertificate` at
`lean/YMGap/Continuum/QuaternionHaarExposedHeatPositive.lean:81`.

### Route consequence and remaining input

A generic nome-uniform angular/variance constant is unavailable even on this
positive heat family. This does not settle the actual odd-marginal residual:
its sources and weight are different. Nome-dependent/source-specific control,
signed cancellations and another justified changing-scale observable family
are not excluded. The next producer remains direct SAME temporal-form/
centered-variance control for one compatible original family, or a positive
sampled-response construction. No further Ward wrapper is warranted without
a concrete residual bound and a proved original-weight/time join. The
separate all-vector spatial/spacing estimate and the full nontrivial
continuum/QFT/YM-field, physical-mass and all-group obligations remain open.

### Verification of the heat-law diagnostic

Five serialized one-worker 4 GiB checks terminated successfully:

- `/tmp/ym-gap-heat-angular-radial-rates-check-5.log`: 21 gates.
- `/tmp/ym-gap-exposed-fundamental-energy-check-5.log`: 4 gates.
- `/tmp/ym-gap-exposed-heat-moments-check-6.log`: 5 gates.
- `/tmp/ym-gap-exposed-heat-positive-check-2.log`: 3 gates.
- `/tmp/ym-gap-heat-angular-variance-obstruction-check-4.log`: 7 gates.

All forty printed gates are within {propext, Quot.sound} (some axiom-free),
with no error/warning/sorryAx in the accepted logs. Sol supplied the moment/
angular/scalar drafts and an independent same-law scope review; Luna supplied
the positivity draft. Root corrected the algebra/namespaces, constructed the
normalized consumer and explicit certified counterexample, and serialized
verification. No new hole/axiom or canonical frontier-field change. The
semantic root imports the consumer; no full-root build/audit/guard ran.
