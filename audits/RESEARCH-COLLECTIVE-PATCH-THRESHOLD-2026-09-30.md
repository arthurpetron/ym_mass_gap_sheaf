# Collective patch route: quantitative entry test

Source baseline: `d2cfea5`. Reviewed 2026-09-30 UTC. This is mathematical
analysis and source review, NOT a new Lean theorem or a closed frontier.
No Lean files, axioms, sorrys, or canonical chart states are changed.

Later scope refinement: 18/L-3/L^2 is sufficient for THIS unweighted
overlap argument, not a necessary threshold for all collective methods.
Refined inverse-square criteria and their quantitative/applicability limits
are reviewed in `RESEARCH-DEFECT-RETAINING-COLLECTIVE-ROUTE-2026-09-30.md`.
No such criterion has been transferred to the original completed carrier.

Subsequent result: the unchanged conservative `supportRatio(w,4*L^4)`
cannot clear this test at any L>=1. That scalar comparison is now checked;
see `audits/AUDIT-PATCH-COLLAR-BUDGET-2026-09-30.md`. The patch-overlap
derivation in this report remains unformalized, and the actual patch gap
remains unbounded by that obstruction.

## Actual missing input and consumer

The missing estimate is on a justified scaling family, not the already proved
small-nome regime. The latter has an original-action all-state square-energy
bound in `lean/YMGap/Continuum/BF4ExactSlabConditionalGeneratorLowerBound.lean:94`,
`conditionalGenerator_square_lower`, with a positive pilot instance at line
104, `existingNome_generator_square_lower`.

Keep the SAME full-action completion and its conditional projections P_i.
Write R_i = I-P_i, H = sum_i R_i, and E(x) = <Hx,x>.
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:68`,
`conditionalGenerator_square`, decomposes ||Hx||^2 into E, signed neighboring
pairs, and nonnegative commuting remote pairs. The possible new producer is
a lower bound for a SUM of residuals in an overlapping patch, not another
universal shared-factor pair coefficient.

The eventual consumer is
`lean/YMGap/Continuum/BF4ExactSlabChebyshevCovarianceBound.lean:102`,
`finiteCovariance_sq_bound`: reverse energy on its actual second auxiliary
component. An all-state H-square bound is a stronger sufficient route, not a
necessary replacement for that narrower obligation.

## Finite algebra: unequal overlaps need an explicit penalty

This paragraph is an unformalized derivation. Choose finitely many patches
A_t of the existing physical link indices. Put H_t = sum_{i in A_t} R_i.
Suppose every index occurs m>0 times, and let c_ij be the number of patches
containing both indices. Assume c_ij <= m, as holds for such a cover. Write
e_i = ||R_i x||^2 and q_ij = <R_i x,R_j x>. Then

    S(x) := sum_t ||H_t x||^2
          = m E(x) + sum_{i != j} c_ij q_ij.

For remote indices the existing commutation identity makes q_ij
nonnegative. For a neighboring unordered pair, the elementary square
||R_i x + R_j x||^2 >= 0 gives -2 q_ij <= e_i+e_j. Thus

    S(x) - m ||Hx||^2 <= b E(x),
    b >= max_i sum_{j != i, near i j} (m-c_ij).

If, on the SAME state x, every patch satisfies

    ||H_t x||^2 >= lambda <H_t x,x>,

then summing gives the precise sufficient estimate

    ||Hx||^2 >= (lambda-b/m) E(x).

The test is lambda > b/m, not merely lambda>0. The patch inequality has to
hold on every state needed by the subsequent descent; a check only on the
initial observable does not establish an all-state generator bound.

## Concrete four-dimensional box calculation

The following counting argument is also NOT yet a Lean theorem. Embed the
natural-coordinate link bases into Z^4 for indexing patches, and take all
translated boxes t+{0,...,L-1}^4, L>=1. A patch contains exactly the original
physical links whose BASE lies in that box. Include negative box origins;
otherwise boundary links would not have the same multiplicity. Only finitely
many of these boxes meet a fixed finite slab. Never replace their conditional
operators by those of an isolated box with its incident action deleted.

Every physical link occurs m=L^4 times. If its base differs from another by
d, their joint count is c_ij=product_r max(L-|d_r|,0). In a plaquette sharing
the link (z,mu), for each nu != mu the possible distinct neighbors are

    mu-links: z+e_nu, z-e_nu;
    nu-links: z, z+e_mu, z-e_nu, z+e_mu-e_nu.

The per-nu sum of deficits m-c_ij is 6L^3-L^2. Missing physical boundary
faces only remove neighbors. Thus b <= 18L^3-3L^2, giving the concrete test

    lambda > 18/L - 3/L^2.

The enumeration is derived from
`lean/YMGap/Continuum/ClusterCount4DProgress.lean:147`, `edgesOf`, and the
common-face characterization
`lean/YMGap/Continuum/BF4ExactSlabWardStarGeometry.lean:44`, `near_iff`.
Their existing formal row bound is 25; this report does NOT claim that a
formal 18-neighbor or patch-overlap theorem already exists.

## What is already available, and what is not

- `lean/YMGap/Continuum/BF4ExactSlabLocalSupportCoercivity.lean:136`,
  `dense_local_coercivity`, controls centered, literally supported inputs.
  `lean/YMGap/Continuum/BF4ExactSlabCompletedLocalSupportCoercivity.lean:53`,
  `completed_local_coercivity`, requires an explicit termwise-local Cauchy
  representative. Neither is the all-state conditional-patch square bound
  above. Subtracting a scalar mean does not remove exterior-dependent patch
  fixed states. The actual block projection fixes exterior polynomials by
  `lean/YMGap/Continuum/BF4ExactSlabBlockConditionalProjection.lean:137`,
  `conditionalProjection_fix_exterior_polynomial`.
- `lean/YMGap/Continuum/BF4ExactSlabLocalAuxiliaryCoercivity.lean:74`,
  `auxiliary_coercivity`, supplies a genuine bound on the actual recurrence
  output, but its support budget grows with recurrence order. Gauge-sector
  preservation alone supplies no improvement of this coefficient.
- The constructive square-energy-to-coercivity argument already exists:
  `lean/YMGap/Continuum/GNSResidualGeneratorDescent.lean:112`,
  `energy_contract`, and line 175, `step_telescope`, followed by
  `lean/YMGap/Continuum/RCDescentCoercivity.lean:67`, `descent_coercivity`.
  The needed positive finite-volume baseline is proved in
  `lean/YMGap/Continuum/BF4ExactSlabCompletedFiniteVolumeCoercivity.lean:211`,
  `completed_centered_coercivity`.
- `lean/YMGap/Continuum/BF4ExactSlabSmallNomeUniformCoercivity.lean:62`,
  `volume_uniform_centered_coercivity`, already composes that argument for
  the small-nome margin. It is NOT an existing theorem parameterized by an
  arbitrary new patch margin. The same generic argument would need to be
  instantiated with a newly proved margin and its explicit iteration rate.
  A gauge-sector-only estimate would also require a restricted descent
  argument and sector preservation for its actual generator iterates; the
  present generic square-energy hypotheses quantify over all completed states.
- `lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:156`,
  `reverse_energy_of_coercivity_at_balanced`, is the existing final algebraic
  join to reverse energy. No spectral theorem is needed for this join.

## Literature scope and execution decision

[Lemm, arXiv:1902.07141v1, sections 3-4](https://arxiv.org/html/1902.07141v1)
uses subsystem squares and a Cauchy-Schwarz correction for unequal pair
counts. Its nearest-neighbor spin theorem has threshold 1/n+2/n^2. It assumes
a finite-dimensional tensor-product spin system with periodic global
geometry; its general finite-range theorem is stated in dimension three.
These hypotheses do not identify our weighted completion and boundary
operators. Reuse the elementary algebra, not the paper's numerical threshold
or an unproved spectral identification. This targeted lookup is not a new
math-ph listing scan.

Next decision: seek an actual original-action patch estimate, retaining the
exterior conditioning and all incident action factors, and compare its
explicit lambda with the overlap penalty BEFORE implementing a patch
compiler. No adequate lambda on a justified scaling family was produced in
this review. A finite matrix truncation alone is not an all-degree bound;
any computational certificate must include a proved tail/complement estimate
and be independently checked in Lean. Alternatively prove the narrower
reverse-energy bound directly on the actual auxiliary states. Do not add a
bundle that merely assumes either missing estimate.

Independent Sol review checked the anchored-box enumeration, penalty sign
and factor, and the existing constructive descent route. Luna reviewed the
local-support versus all-state hypotheses and the already proved small-nome
case. Neither review is kernel verification of the proposed patch argument.

Even success here would concern conditional-link dynamics and finite
correlations. Same-theory OS passage, nontrivial continuum survival, spacing
and physical mass calibration, QFT axioms and every compact simple group
remain separate open requirements of the unchanged Clay goal.
