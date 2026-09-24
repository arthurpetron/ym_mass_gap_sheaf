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
