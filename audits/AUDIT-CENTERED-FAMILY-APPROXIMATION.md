# Actual corrected-family approximation and the remaining signed cost

Date: 2026-09-17 UTC. Parent checkpoint: `69458b3`.

Whole-project goal: for every compact simple group, construct a nontrivial
continuum Yang--Mills theory on R^4 with the required same-theory QFT axioms,
isolated vacuum, and strictly positive finite physical Hamiltonian mass gap.
The constructive Lean axiom gate and that goal are unchanged.

## New proved result

For the actual finite SU(2) odd marginal nu=(V*T^n1)*T^(n+1)1, let
Z=H[nu] and Phi=Z*f-H[nu*f]. For every supported original polynomial f
and rational epsilon>0, the new construction returns degrees (k,l) with

    H[nu*(S(k,l)-Phi)^2] <= epsilon.

S is precisely the corrected sum in the existing temporal-energy bound.
The construction requires 0<w<1 and headCutoff(w)<=K and retains width,
cutoff, nome and boundary-depth dependence. No approximation-budget,
conditional-centering or stable-decomposition hypothesis is supplied by
the caller. The result is an unnormalized squared-norm approximation,
not a uniform spectral gap or a physical-time estimate.

## Source map

All source paths are relative to the repository root.

| Result | Declaration and source |
| --- | --- |
| All active and fringe coordinates, without duplication | `labels_perm_range`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamily.lean:57` |
| Computed finite square cap and exact homogeneity | `sumCap`, `lean/YMGap/Continuum/QuaternionHaarFiniteSquareBudget.lean:32`; `sumCap_scale`, same file:55 |
| Certificate for the finite polynomial sum | `sumSquareBound`, `lean/YMGap/Continuum/QuaternionHaarFiniteSquareBudget.lean:71` |
| Sum of actual defects equals density times aggregate error under Haar insertions | `density_error_pin`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamily.lean:150` |
| Equality of density-multiplied error squares | `density_error_square`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamily.lean:178` |
| Certificate for the total defect square | `defectSumSquareBound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamilyApproximation.lean:74` |
| Same-nu raw family bound after positive-floor cancellation | `rawError_weighted_square_bound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamilyApproximation.lean:95` |
| Computed raw-family degree and error theorem | `approximationCutoff`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeedFamilyApproximation.lean:124`; `rawError_weighted_square_le`, same file:128 |
| Actual per-coordinate correction-error certificate | `correctionDefectSquareBound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCorrectionApproximation.lean:111` |
| Aggregate correction square certificate | `correctionErrorSquareBound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.lean:129` |
| Same-nu correction error, retaining the original density | `correctionError_weighted_square_bound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.lean:147` |
| Computed correction degree and error theorem | `approximationCutoff`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCorrectionFamilyApproximation.lean:177`; `correctionError_weighted_square_le`, same file:180 |
| Computed sequential pair of degrees | `approximationDegrees`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:86` |
| Original-observable error bound and returned witness | `approximation_bound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:94`; `approximationCertificate`, same file:118 |
| Same tests in the original temporal-energy inequality | `approximant_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredFamilyApproximation.lean:129` |

## Why the finite approximation closes

The existing per-piece certificates control D_i,k=nu*q_i,k-tau_i by
rho^(2*k)*C_i, with C_i=4*u^2*B_i^2/ell^2 and rho=1-ell^2/u^2<1.
The new sum cap is computed recursively by 2*a+2*b and is homogeneous.
It may grow rapidly with the number of coordinates; no spatial uniformity
is claimed or needed for this finite approximation step.

The exact telescope endpoint is Haar-carrier equality, not raw coefficient
equality. `density_error_pin` respects that boundary. Positivity yields
ell*H[nu*e^2]<=H[(nu*e)^2] for e=sum_i q_i,k-Phi. Thus the aggregate bound
loses one additional ell^(-1), not an omitted partition factor.

At active coordinates the correction error is (d_i*G_i,l-1)*q_i,k;
at fringe coordinates it is coefficient-zero. Its cap uses the actual
q_i,k, so the correction degree is chosen after k. Each of the raw and
correction squared errors is made <=epsilon/4; the same-weight square
triangle bound then gives the requested epsilon. The degree pair is
returned as a subtype witness, not hidden in propositional existence.

`approximant_energy` instantiates `actualResidual_corrected_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294`, with
these actual seeds and corrections. It keeps the original temporal energy
and the exact signed D+2h*R remainder. No auxiliary dynamics is substituted.

## Audit-directed next mathematical target

OPEN: control D+2h*R on this particular constructed family by the centered
observable norm, with the spatial/depth/cutoff dependence required by the
limiting route. Increasing k or l only improves approximation. It does not
supply a uniform cost budget. The existing component-norm ceiling is not
a uniform bound by the squared norm of the family sum.

The parallel review gave the following **unformalized algebraic diagnostic**.
Writing a=V*T^n1 and t=T^(n+1)1, the ideal expressions q_i=tau_i/nu and
G_i=1/d_i turn the complete cost into

    sum_i H[tau_i^2/(a*d_i)]
      + 2*h*sum_(i<j) H[d_ij*tau_i*tau_j/(a*d_i*d_j)].

Here d_i=t on fringe, with the existing mixed-erasure conventions.
These quotients are explanatory notation, not new polynomial observables
or a proved limit theorem. The source identities behind this diagnostic
are `diagonal_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDiagonalCost.lean:89`, and
`dualTest_cross_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean:179`.
Ordinary unweighted Haar Pythagoras does not control these inverse
interacting-density weights. A crude finite-window comparison retains
regulator-dependent conditioning.

An actual simplification is available at fringe coordinates:
`terminal_inactive_independent`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeDual.lean:65`, removes
that coordinate from the terminal messages. The spatial potential remains:
`spatialWeight`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSliceHeat.lean:70`.
The existing pull-through theorem is `project_mul_of_independent`,
`lean/YMGap/Continuum/SU2QuaternionHaarBlockConditionalAlgebra.lean:64`.
This suggests examining the actual inverse spatial-star conditional pairing;
it does not prove that pairing is zero or bounded uniformly.

For active coordinates, `conditionalMessage_independent`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:71`,
removes a message's own erased coordinate, not all other active coordinates.
No general active cross cancellation follows. The exact existing fringe
cancellation, `determinant_zero_if_either_inactive`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeCross.lean:104`, removes
determinant corrections only; ordinary cross pairings remain.

Uniform cost control for the chosen weighted Haar increments was NOT FOUND
in the reviewed FamilyCost, DiagonalCost, TwoLinkDual, ConditionalMessage,
FringeDual, FringeCross, telescope and conditional-projection modules.
The review neither proves this family uniformly stable nor refutes it.
The physical calibration, continuum/QFT and every-group joins remain open.

## Verification and independent review

Seven final focused checks passed, serialized through the monitored launcher
with one worker and the unchanged 20 GiB ceiling. All 52 printed axiom gates
use only {propext, Quot.sound}; final logs have no errors, warnings, sorryAx
or classical dependencies. Seven root imports were added. Root/full-tree/
full-audit/guard checks were NOT run. No existing sorry, canonical frontier,
CI configuration, or safety limit was changed.

An independent read-only source review found no mathematical defect in the
same-density identity, Haar-level telescope transport, floor powers,
sequential degrees, epsilon allocation or actual energy instantiation.
The separate signed-cost review is a mathematical diagnostic, not a proof.

Final local logs under `/tmp/` (not repository artifacts), with SHA-256:

| Log | Gates | SHA-256 |
| --- | ---: | --- |
| ym-finite-square-budget-20260917.log | 5 | `973ed27346f7eca42e4aba012d789867d41931aa2d984dbcba454b25dd1588e9` |
| ym-weighted-square-triangle-20260917.log | 2 | `72fed11d170736154dfe34730332f78ee9bde08614ca990714f6acbfff2945ec` |
| ym-seed-family-20260917.log | 11 | `e43ff17f3a0da31ecb6c6fdcffb188ec015e2f73f9ee34241eabb4e5cfa99050` |
| ym-seed-family-approximation-20260917.log | 9 | `5eda67c321b078abf0508477fe3a38f3596bae455da464f019db4e503cd7eb1d` |
| ym-correction-approximation-20260917.log | 5 | `0e6473c009dd79164713107f887335076fb061840b8eea42c35025698baf5f8e` |
| ym-correction-family-approximation-20260917.log | 13 | `56f11f8de31004dc90adf684a4fdbed99b2c362637667c4c378fb16eb697157a` |
| ym-centered-family-approximation-20260917.log | 7 | `6e6efe34402c54c9490ae5ac39aebf512a6b94dfd78d38623137f96a893dcdea` |
