# Finite-family edge flow and actual fringe control

Date: 2026-09-17 UTC. Base revision: `71f1ea17d4991178992083b33d4ba13c717e2913`.

Whole-project goal: for every compact simple G, construct nontrivial continuum
Yang--Mills on R^4 with same-theory QFT axioms, isolated vacuum, and positive
finite physical Hamiltonian mass gap, inside the constructive axiom gate.
That target remains OPEN. This checkpoint supplies finite SU(2) estimates,
not an improved global spectral gap or continuum passage.

## What changed mathematically

The two-link positive cells now have a finite-family recurrence, so the
energy comparison itself does not require adding pairwise inequalities.
For a list of factors A_i>=h>=0 and signed polynomial tests x_i, define

    P_empty=1, L_empty=0, Q_empty=0,
    P_cons=A*P, L_cons=P*x+A*L,
    Q_cons=P*x^2+A*Q+2*h*x*L,
    F_list(z,b)=P*z^2+2*h*L*z*b+h*Q*b^2.

The exact identity is

    F_cons(z,b)=(A-h)*F_tail(z,b)+h*F_tail(z+x*b,b).

Both terms are certified positive by recursion, starting from z^2.
There is no commutation assumption beyond polynomial multiplication,
no inverse or square root, and no separate bound on any cross term.

Declarations in `lean/YMGap/Continuum/QuaternionHaarFiniteFamilyDual.lean`:

| Declaration | Line | Checked content |
|---|---:|---|
| `product` | 39 | Full original factor product P. |
| `flow` | 44 | One-erasure flow L, defined recursively. |
| `cost` | 49 | Signed quadratic cost Q, including cross terms. |
| `quadratic_cons` | 63 | Coefficientwise two-branch identity. |
| `quadraticCertificate` | 76 | Type-valued certificate for every finite list and supported z,b. |
| `finite_family_dual` | 165 | h*H[mu*L*z]^2 <= H[mu*P*z^2]*H[mu*Q], for h>0. |

The last theorem integrates the certificate with the original positive
background mu, uses signed rational scalings, applies one Cauchy--Schwarz
inequality and cancels only h>0. It includes the empty family and has no
explicit list-length coefficient. It does NOT bound H[mu*Q] by a variance.

## Original-kernel instance with every retained coordinate indexed

Write g=T^n1, a=Vg, t=Tg, nu=a*t. The physical instance takes mu=a(x)*a(y).
Active coordinates carry their actual heat factor and test jump; inactive
retained coordinates carry the polynomial factor 1 and their test jump.
The latter is not heatAt and uses no heat normalization identity.

Declarations in `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyFlow.lean`:

| Declaration | Line | Checked content |
|---|---:|---|
| `fringeBlocks` | 56 | Computed range of retained coordinates filtered by inactivity. |
| `fringeBlocks_mem_iff` | 59 | Membership exactly means valid and inactive. |
| `retained_coordinate_partition` | 70 | Exhaustive, disjoint active/fringe membership. |
| `family` | 85 | Actual active heat factors followed by fringe unit factors. |
| `family_product_pin` | 109 | Family product is coefficient-equivalent to unchanged kineticWeight. |
| `familyFloorCertificates` | 141 | All heat/unit floor certificates are constructed. |
| `family_tests_supported` | 158 | Support for every actual test jump. |
| `endpointWeight` | 169 | Both complete copies of V*T^n1, with nothing removed. |
| `flowPair` | 174 | H[mu*L*jump(f)] on the original doubled carrier. |
| `signedCost` | 179 | H[mu*Q], with all fringe and active cross terms retained. |
| `original_family_flow_energy` | 186 | h*flowPair^2 <= (2*energy(g,f))*signedCost. |

The exact 2 comes from `energy_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`.
Unit-factor positivity uses `headFloor_le_oneThirtySecond`,
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`, hence h<=1.
No fictitious dynamics, changed kinetic kernel, or deleted endpoint is used.

Certificate data is selected by explicit finite decidable search in the
private `mappedCertificates`, FamilyFlow:130. It does not eliminate the
Prop-level existential of List.mem_map into Type. The family theorem needs
support but no conditional centering; it remains a raw signed edge-flow
estimate, not yet the erased-marginal sum estimate needed downstream.

## Actual fringe residuals have coefficient-one energy control

For an inactive coordinate i<N, the literal terminal message is independent
of i. If q is the existing weightedResidual i nu s, then coefficientwise

    q = (weightedResidual i a s)*t,       P_i(a*q)=0.

This needs no reciprocal or division by t. Applying the old erased-jump
identity to the UNCHANGED active list gives mixed pairing 2*H[nu*f*q] and
test jump norm 2*H[nu*q^2]. Full-edge Cauchy--Schwarz and the original energy
identity cancel 4 exactly, giving

    H[nu*f*q]^2 <= energy(g,f)*H[nu*q^2].

Declarations in `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeDual.lean`:

| Declaration | Line | Checked content |
|---|---:|---|
| `terminal_product` | 55 | Literal t=productMap(active,a), not only a Haar pairing. |
| `terminal_inactive_independent` | 65 | Actual t has no inactive output coordinate. |
| `weightedResidual_independent_right` | 74 | Pull-through for any genuinely independent right factor. |
| `fringeResidual_centered` | 94 | Actual nu-residual is a-centered at the inactive coordinate. |
| `inactive_dual_energy` | 117 | Coefficient-one bound for any supported a-centered inactive test. |
| `fringeResidual_dual_energy` | 163 | The existing actual-marginal residual supplies that test. |

The complete family's common h bound is coarser than this individual
coefficient-one bound; neither statement identifies a decomposition.

## Exact remaining causal work

1. **Family pairing and cost identities.** Identify the raw flow as twice
   the sum of active erased-marginal pairings and fringe actual-marginal
   pairings under their actual a-centerings. Identify cost/2 as the full
   signed diagonal/cross Gram sum, retaining all fringe terms. These family
   declarations are not supplied by this checkpoint. The two-link identities
   remain available in `terminal_two_link_dual_energy` and `dualTest_cross_pin`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLinkDual.lean:78`, :179.
2. **Analytic signed budget.** Control the original action's determinant
   remainder t*d_ij-d_i*d_j, not the ordinary marginal cross pairing, with
   the required cutoff/depth/spatial dependence. No determinant sign,
   summability, nonneighbor vanishing, or terminal-message locality is proved
   here. The explicit recursive signedCost is not such a bound.
3. **Stable centered decomposition.** Construct the actual centered
   polynomial Z*f-H[nu*f], Z=H[nu], from supported active tests plus fringe
   contributions, with explicit approximation modulus and controlled total
   cost in the SAME nu-norm. Exhaustive coordinate indexing alone does not
   construct this. Necessary reciprocal cross-limits also remain open.
4. **Use the unchanged consumer.** These inputs must feed
   `clearedDefect_diagonal_nonnegative_iff`,
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`,
   retaining the original mean and partition factors. No improved global
   C_delta bound is claimed. Subsequent spatial/scaling, same-theory QFT and
   Hamiltonian, positive finite physical mass and every-group joins remain
   OPEN. The preserved fixed-small-nome completed gap does not remove them.

The physical theorems explicitly quantify 0<w<1, K>=headCutoff(w), width,
depth and supported tests. The family h depends on nome; the signed cost
depends on the full action, family and parameters. There is no beta-uniform
positive global margin. The generic positive recurrence supplies no
non-abelian mass-generation mechanism by itself.

## Verification boundary

Three final focused checks passed, serialized through the monitored launcher
with one worker and a 20 GiB worker ceiling. Fresh process/swap preflights
found no competing compiler/runner; swap decreased from 6669 to 6653 MiB.
The 6+6+12 printed gates use only {propext, Quot.sound}; the three generic
product/flow/cost definitions are axiom-free. Final logs contain no errors,
warnings or sorryAx. Namespace, parser and certificate-selection repairs
were completed before these final checks. Independent source reviews checked
the recurrence, actual kernel, fringe normalization and final data selection.

No new sorry, axiom, classical shortcut, frontier/guard change, resource-limit
increase or CI change. Three root imports added. Root/full-tree/full-audit/
guard checks were NOT run. The whole-project goal remains active and open.
No literature scan occurred.

| Log under `/tmp/` | SHA-256 |
|---|---|
| `ym-finite-family-dual-20260917.log` | `b1cf78667e858d7ee8e789c70366f559bfde68ed45c95060ff4585114290abb0` |
| `ym-fringe-dual-20260917.log` | `428a84e91ab3f1fb5aebb37d6b8830e93bd139793969c3e7a23b97b6f5407272` |
| `ym-physical-family-flow-20260917.log` | `9dfc8419397a06a49ad7c41343400e5037225bed940d838da4e4a5405f5b7e37` |
