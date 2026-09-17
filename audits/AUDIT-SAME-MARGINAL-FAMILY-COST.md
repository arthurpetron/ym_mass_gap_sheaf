# Finite-degree same-marginal flow and signed cost

Date: 2026-09-17 UTC. Base revision: `0635779c70d29e0c2bbd9334f4b69a09fa7b2e01`.

Whole-project goal remains: every compact simple G, nontrivial continuum
Yang--Mills on R^4, same-theory QFT axioms, isolated vacuum and positive
finite physical Hamiltonian mass gap, constructively in Lean. This finite
SU(2) checkpoint closes none of the remaining global/continuum Clay joins.

## Exact result

Write g=T^n1, a=Vg, t=Tg, nu=a*t, h=headFloor(w), U=prefixCap(w).
For q_i=weightedResidual i nu seed_i and explicit finite degrees k_i, use

    active: r_i=t*q_i*G_i,k_i,  v_i=d_i*G_i,k_i*q_i;
    fringe: r_i=q_i,            v_i=q_i;
    S=sum_i v_i.

The complete erased-marginal flow is exactly H[nu*f*S]. Its cost is exactly

    C = h*H[nu*S^2] + D + 2h*R,
    D = sum_active H[nu*d_i*(t-h*d_i)*(q_i*G_i)^2]
          +(1-h)*sum_fringe H[nu*q_i^2],
    R = sum_active i<j H[nu*(t*d_ij-d_i*d_j)*q_i*q_j*G_i*G_j].

Consequently the checked shared-energy estimate is

    h*H[nu*f*S]^2 <= energy(g,f)*(h*H[nu*S^2]+D+2h*R).

The exact diagonal bounds are

    0 <= D <= (U-h)*sum_active H[nu*v_i^2]
                       +(1-h)*sum_fringe H[nu*q_i^2].

This is a sum of COMPONENT norms, not a uniform bound by H[nu*S^2] or
the centered observable's norm. R remains signed and unbounded by this
checkpoint. No division, reciprocal limit, different weight, changed energy,
fictitious fringe heat factor, or assumed test centering is inserted.

## Checked declarations

| Declaration | Source | Content |
|---|---|---|
| `sumSquare_expansion` | `lean/YMGap/Continuum/QuaternionHaarFamilySquare.lean:102` | Square of the actual sum equals its positional diagonal plus twice its signed pair sum. |
| `haar_weighted_sum_indexed` | `lean/YMGap/Continuum/QuaternionHaarFamilySquare.lean:175` | Exact Haar linearity for the same signed weight. |
| `correctedTest` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDiagonalCost.lean:47` | Literal d_i*G_i*q_i polynomial. |
| `diagonal_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDiagonalCost.lean:89` | Erased norm equals h times corrected norm plus diagonal cost. |
| `diagonalCertificate`, `diagonalCost_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDiagonalCost.lean:120`, `:131` | Positive nu*d*(t-h*d)*(q*G)^2 certificate and Haar bound. |
| `diagonalUpperCertificate`, `diagonalCost_upper` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDiagonalCost.lean:137`, `:175` | Upper defect is nu*d*(U*d-t)*(q*G)^2; coefficient U-h. |
| `conditionalMessage_inactive` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeCross.lean:59` | Inactive erasure leaves exactly t. |
| `twiceErasedMessage_inactive_right`, `twiceErasedMessage_inactive_left` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeCross.lean:66`, `:73` | An inactive erasure leaves the other one-erasure message. |
| `determinant_zero_if_either_inactive` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeCross.lean:104` | Only the fringe determinant correction is zero. |
| `dualTest_fringe_cross_pin`, `fringe_dualTest_cross_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeCross.lean:113`, `:135` | Both mixed orientations retain their actual corrected marginal pairing. |
| `fringe_fringe_cross_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeCross.lean:157` | Ordinary fringe cross pairing, not zero. |
| `finiteTests`, `corrected`, `correctedSum` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:63`, `:67`, `:70` | All coordinates and independent explicit finite degrees. |
| `diagonalRemainder`, `determinantRemainder` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:78`, `:88` | Exact D and signed active--active R. |
| `flow_actual_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:178` | Flow is exactly the actual-nu pairing with S. |
| `cost_actual_split` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:206` | C=h*H[nu*S^2]+D+2h*R. |
| `diagonalBudget`, `diagonalRemainder_bounds` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:256`, `:264` | Explicit component-norm cap and nonnegative D. |
| `actualResidual_corrected_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCost.lean:294` | Concrete residual-family shared-energy inequality on the SAME nu. |

The active diagonal certificates use the existing actual message bounds,
`conditionalMessage_lowerCertificate` and `conditionalMessage_capCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:103`,
`:117`. There is no detached pointwise-positivity oracle. The active pair
split consumes `dualTest_cross_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean:179`.

The family square identity uses positional occurrences, so polynomial tests
may repeat. The previous checked physical label list is duplicate-free.
Finite tests are instantiated by actual-nu residuals through
`actualResidual_family_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:374`;
this avoids introducing a new conditional-centering hypothesis.

## Remaining analytic task and source audit

The next required input is a controlled choice of seeds/degrees producing
S_m -> Phi=Z*f-H[nu*f], Z=H[nu], with explicit moduli and a proved estimate

    D_m+2h*R_m <= B_0(w)*H[nu*Phi^2] + epsilon_m,

with B_0>=0, nonnegative epsilon_m tending to zero with an explicit modulus,
and the required width/depth/late-cutoff dependence. Neither the choice nor
this estimate is supplied. A universal bound for arbitrary decompositions
is not asserted. Positive D must not be discarded in an upper estimate.
The unchanged consumer is `clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`,
including the original mean correction and partition factors. The candidate
h/(h+B_0) after justified approximation/order closure is not a proved gap.

A stable admissible decomposition for this actual nu was **NOT FOUND** in
the bounded review of the following closest source families:

- `square_decomposition`, `lean/YMGap/Continuum/SU2QuaternionHaarBlockProjection.lean:240`,
  is unweighted Haar Pythagoras. `productMap_centered_square_bound`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatTensorization.lean:115`,
  uses that Haar geometry, not a stable decomposition in this interacting nu.
- `weightedResidual`, `lean/YMGap/Continuum/SU2QuaternionWeightedBlockCentering.lean:33`,
  and `project_weightedResidual_zero` (:57) give individual conditionally
  centered polynomials, not a controlled decomposition of Phi.
- `conditionalProjection_orthogonal`,
  `lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:284`,
  concerns the full-slab `fullData` weight, not (Vg)Tg; see `fullData`,
  `lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`.
- Also searched the related `StarCompletedInverse`, `StarInverseApproximation`,
  `FixedSpatialFamilyMarginals`, `FixedSpatialActualMarginalDual`, and targeted
  decomposition/martingale declarations in the `BF4ExactSlabFixedSpatial*`,
  `SU2Quaternion*` and `QuaternionHaar*` families.

The all-other-coordinate condition P_i(nu*q_i)=0 is explicit in
`actual_marginal_dual_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:274`.
It is not automatically the nested-filtration centering of ordinary Doob
differences. A proposed martingale construction must verify this condition,
not silently substitute a different conditioning algebra.

All physical statements retain 0<w<1 and K>=headCutoff(w), and name width,
depth, seeds and degrees. h and U depend on nome; no beta-uniform positive
mass margin is claimed. There is no proof here of spatial determinant
decay, terminal-message locality, controlled continuum passage, complete
same-theory QFT, finite positive physical mass or the every-group extension.

## Verification boundary

Four final focused checks passed, serialized through the monitored launcher
with one worker and a 20 GiB ceiling. Fresh process/swap checks found no
competing compiler/runner; swap stayed about 6645 MiB. All 11+9+9+12 gates
lie within {propext, Quot.sound}; two generic sum definitions are axiom-free.
Final logs contain no errors, warnings or sorryAx. Independent reviews
checked the two diagonal factorizations, full signed sum, fringe treatment,
same nu and lack of any claimed decomposition or uniform remainder bound.

No sorry, axiom, canonical frontier field, guard, CI configuration or memory
limit changed. Local 800000 heartbeat allowances were used on three family
proofs; the machine-safety settings stayed fixed. Four root imports added;
root/full-tree/full-audit/guard checks were NOT run. No literature scan.

| Log under `/tmp/` | SHA-256 |
|---|---|
| `ym-family-square-20260917.log` | `3f9a7f8273ebd7016b3f9d4efd5339017de43a50e26a54fbc93fafcc87835fe2` |
| `ym-diagonal-cost-20260917.log` | `3b62cc6b9fea5a3331e4bddd287e01f93343ac382bd2b8cb51d30afe5328f87b` |
| `ym-fringe-cross-20260917.log` | `eb1484188f8960651f989b4a6fbd3dd0d63e35020f39d4d0f91379479d2ec7c5` |
| `ym-family-cost-20260917.log` | `7eeca88245b405c2b1389acaf2a8e6bbdcb2442effed515c6fd8f927c27dd015` |
