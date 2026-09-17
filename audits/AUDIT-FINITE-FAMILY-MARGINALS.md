# Full-family original-energy marginal estimate

Date: 2026-09-17 UTC. Base revision: `b8e2620daad340c7c8df93ad6546925f79253f09`.

Whole-project goal: for every compact simple G, construct nontrivial continuum
Yang--Mills on R^4 with same-theory QFT axioms, isolated vacuum and positive
finite physical Hamiltonian mass gap, inside the constructive axiom gate.
That target remains OPEN. This increment is a finite SU(2) identity and
energy estimate, not a new uniform spectral gap or continuum construction.

## Checked mathematical increment

Write g=T^n1, a=Vg, t=Tg and nu=a*t. Let d_i and d_ij be the original
one-/two-factor-erased messages, with the entire a retained. Inactive
coordinates occur as unit factors, so erasing their label removes no heat
factor. For supported r_i with P_i(a*r_i)=0, set

    L = sum_i H[a*d_i*f*r_i],
    C = sum_i H[a*d_i*r_i^2] + 2h*sum_{i<j} H[a*d_ij*r_i*r_j].

The original doubled-carrier flow and cost obey

    flowPair = 2L,       signedCost = 2C.

The previous edge inequality h*flowPair^2 <= (2*energy(g,f))*signedCost
therefore gives, after cancelling four,

    h*L^2 <= energy(g,f)*C.

All cross terms remain signed, including active--fringe and fringe--fringe
terms. Each pair occurs once, not twice. f needs support but no conditional
centering. There is no explicit family-size coefficient; this does NOT say
that C has a width/depth/cutoff-uniform upper bound.

### Source map

| Declaration | Source | Checked content |
|---|---|---|
| `singleCuts`, `pairCuts` | `lean/YMGap/Continuum/QuaternionHaarFamilyErasure.lean:30`, `:35` | Positional erasures, preserving repeated entries. |
| `flow_expansion` | `lean/YMGap/Continuum/QuaternionHaarFamilyErasure.lean:168` | Complete one-erasure polynomial flow. |
| `cost_expansion` | `lean/YMGap/Continuum/QuaternionHaarFamilyErasure.lean:207` | Diagonal plus signed, ordered-once pair terms. |
| `labels_nodup` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyErasure.lean:62` | Constructively duplicate-free retained labels. |
| `family_eq_indexed` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyErasure.lean:75` | Existing physical family unchanged. |
| `product_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyErasure.lean:102` | Units removed, all remaining original heat factors kept. |
| `single_remaining_perm`, `pair_remaining_perm` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyErasure.lean:177`, `:191` | Filtered remainder is the existing canonical erasure list, also for fringe labels. |
| `marginalFlow`, `marginalDiagonal`, `marginalCross`, `marginalCost` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:107`, `:111`, `:116`, `:121` | Actual one-/two-erasure marginal sums. |
| `flowPair_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:188` | flowPair=2L. |
| `signedCost_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:270` | signedCost=2C, retaining every cross term. |
| `original_family_marginal_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:303` | h*L^2<=energy(g,f)*C. |
| `residualTests` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:338` | Explicit actual-nu residuals; polynomial reciprocals only on active links. |
| `residualTests_supported`, `residualTests_centered` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:344`, `:358` | Actual tests supply support and a-centering. |
| `actualResidual_family_energy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyMarginals.lean:374` | Instantiated finite-degree estimate without an assumed centering field. |

`erased_jump_pairing`,
`lean/YMGap/Continuum/SU2QuaternionWeightedProductDualEnergy.lean:242`,
is applied to each exact remainder. Both endpoint weights are retained and
the source polynomial remains V*T^n1. One centered test kills both mixed
endpoint terms by the existing slice symmetry; centering of f is unnecessary.

For arbitrary supported seeds, q_i=weightedResidual i nu seed_i. On active
links r_i=t*q_i*G_i,k, using the existing explicit polynomial reciprocal;
on fringe links r_i=q_i directly. These are actual finite polynomial tests,
not exact divisions and not a claim to span a prescribed centered f.

## Audit-driven next task: finite polynomials before inverse limits

The following is a source-reviewed algebraic proof plan, NOT a newly checked
family declaration or a supplied analytic bound. Avoid introducing rational
inverse observables just to express the next estimate.

For a common finite degree k, set v_i=d_i*G_i,k*q_i on active links, v_i=q_i
on fringe links, and S_k=sum_i v_i. (The checked tests also permit a separate
degree at each index.) The target division-free cost identity is

    C_k = h*H[nu*S_k^2] + D_k + 2h*R_k,
    D_k = sum_active H[nu*d_i*(t-h*d_i)*(q_i*G_i,k)^2]
          +(1-h)*sum_fringe H[nu*q_i^2],
    R_k = sum_active i<j H[nu*(t*d_ij-d_i*d_j)*q_i*q_j*G_i,k*G_j,k].

The active--active identity is already the two-test `dualTest_cross_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean:179`.
Canonical erasure plus `terminal_product`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeDual.lean:55`, supplies
the route to the fringe reductions. Their ordinary cross pairings do NOT
vanish; only their determinant correction is zero. The full family split
and its summed certificate are still to be implemented and checked.

The next diagonal comparison is supported by
`conditionalMessage_lowerCertificate` and `conditionalMessage_capCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:103`,
`:117`, and `multiplierSquareCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialErasedMessageInverse.lean:209`.
They suggest the finite bound

    0 <= D_k <= (U-h)*sum_active H[nu*v_i^2]
                  +(1-h)*sum_fringe H[nu*q_i^2].

D_k is a nonnegative COST. It cannot be discarded in an upper bound. In
formal ratio notation its diagonal coefficient would be lambda_i-h, not
lambda_i-2h. Controlling a sum of component norms does not control the norm
of their sum without a suitable decomposition; cancelling components show
why a bound for every decomposition is not the intended target.

The substantive next input is therefore a CONSTRUCTED approximation S_m to
Phi=Z*f-H[nu*f], Z=H[nu], with explicit moduli and an actual-action estimate

    D_m+2h*R_m <= B_0(w)*H[nu*Phi^2] + epsilon_m,

on that chosen decomposition, with B_0(w)>=0, nonnegative epsilon_m tending
to zero with an explicit modulus, and the required width/depth/late-cutoff
control. Neither the decomposition nor this estimate is supplied here.
The candidate coefficient after justified limit and rational order closure
is h/(h+B_0), not an already proved gap. The existing consumer remains
`clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
Its original mean and partition factors must be preserved.

No terminal-message locality, nonneighbor determinant vanishing, blanket
off-diagonal smallness, or decomposition of the whole centered sector is
assumed. The actual declarations quantify w, width, depth, cutoff and
tests; h=headFloor(w) remains nome-dependent, with K>=headCutoff(w).
There is no beta-uniform positive margin. The generic erasure algebra is
not a non-abelian mass-generation argument. Spatial/spacing control,
same-theory OS/QFT/Hamiltonian identification, finite positive physical mass
and every compact simple group remain open whole-project joins.

## Verification boundary

Three final focused checks passed through the monitored launcher, serialized
with one worker and a 20 GiB worker ceiling. Fresh process/swap preflights
found no competing compiler/runner; swap remained about 6645 MiB.
All 11+20+11 printed gates lie within {propext, Quot.sound}; five generic
definitions/product identity gates are axiom-free. Final logs contain no
errors, warnings or sorryAx. Independent source review checked constants,
pair counting, a-centering, the unchanged energy and the residual instance.

No sorry, new axiom, classical shortcut, canonical field or frontier guard
was changed. Local proof-heartbeat allowances of 800000 were used; worker
count, memory ceiling and safety thresholds were not raised. Three root
imports added; root/full-tree/full-audit/guard checks were NOT run. CI remains
unchanged and manual-only. No literature scan was run. Whole-project goal
mode remains active.

| Log under `/tmp/` | SHA-256 |
|---|---|
| `ym-family-erasure-20260917.log` | `1e5a721e8f2f0b9d3ac73ebb4d6ccaa9e2e68e78437416f8e6c5a868518a05e5` |
| `ym-physical-family-erasure-20260917.log` | `09ee891594e0f0aedabdaad716834c59733c32322f188cc2b18afa08870e540a` |
| `ym-physical-family-marginals-20260917.log` | `fa566081a1b24099651eaa387c8654f0f1dc910e75caee293170c50c7135cc18` |
