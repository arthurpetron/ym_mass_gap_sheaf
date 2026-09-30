# Original chronological path-energy inequality

## Whole-project goal and scope

OPEN: constructive continuum Yang--Mills on R^4 for every compact simple
group, with SAME-theory QFT axioms, nontriviality and finite positive physical
Hamiltonian mass gap. This checkpoint is finite-cutoff SU(2) on ordinary
original-action weighted L2, not an OS transfer or physical-gap theorem.

Assume 0<w<1 and K>=headCutoff(w). Let N be the original slab-link count,
W the entire original action polynomial, Z=H[W], and
D(f)=Z*H[W*f^2]-H[W*f]^2. The observable is any supported original polynomial.

## Exact result

The following inequality is now kernel checked in CReal quotient order:

    2 D(f) <= N sum_{k=0}^{N-1} cost_k Z (E_k + E_k).

E_k is the existing completed conditional residual norm of the SAME input
at the actual next physical link in the chronological order. These norms
use the unnormalized original full-action form. The partition occurs once
per term, and the replica factor two is still explicit on both sides.

Let A_k be the already-selected block list, b_k its actual crossing-face
count, and d_k the actual next link's incident-face count. The code defines
ell_k=headFloor(w)^d_k, U_k=prefixCap(w)^d_k, and

    floor_k = (headFloor(w)^2)^b_k * ell_k^2,
    cost_k  = recipPos(floor_k) * (prefixCap(w)^2)^b_k * U_k^2,

with the numerator product parenthesized inside recipPos's multiplier.
Positivity of the denominator is proved. This cost has no K or observable
argument; nome, extent, selected cut and link dependence is explicit.
The checked geometry gives b_k<=12*(extent+1)^3 for EVERY k<N.

## Declaration-level causal joins

All paths below start at `lean/YMGap/Continuum/`.

| Declaration | File:line | Checked role |
| --- | --- | --- |
| `chronologicalBlocks_perm` | `BF4ExactSlabChronologicalLinkOrder.lean:89` | Actual original block permutation, sorted by physical link time |
| `prefixCut_time_bounds` | `BF4ExactSlabChronologicalLinkOrder.lean:164` | All strictly earlier-time physical links included; all later-time links excluded |
| `prefix_crossingCount_le_area` | `BF4ExactSlabChronologicalLinkOrder.lean:212` | Existing geometric area bound applies even inside a time layer |
| `ordered_increment_eq` | `SU2QuaternionOrderedReplicaPath.lean:230` | Actual next list entry gives the literal adjacent path increment |
| `ordered_weighted_increment_transport` | `SU2QuaternionOrderedReplicaPath.lean:254` | Exact original doubled-Haar change of variables, no dropped weight |
| `ordered_path_cauchy_certificate` | `SU2QuaternionOrderedReplicaPath.lean:299` | Explicit permutation has unchanged endpoint square and linear N cost |
| `cutSwap_selectedLinks` | `BF4ExactSlabOrderedPathCut.lean:70` | Arbitrary in-range block selection is the same physical-link cut |
| `original_selected_increment_bound` | `BF4ExactSlabOrderedPathCut.lean:86` | Reverse cut inequality pays actual crossing faces |
| `stepFloor_positive` | `BF4ExactSlabOrderedPathEnergy.lean:55` | Positive denominator is constructed, not an analytic hypothesis |
| `stepCost` | `BF4ExactSlabOrderedPathEnergy.lean:66` | Explicit rational per-step cost, no hidden uniformity |
| `original_selected_increment_energy_bound` | `BF4ExactSlabOrderedPathEnergy.lean:121` | Original cut cost joins the already checked replacement-to-energy theorem |
| `original_ordered_path_variance_bound` | `BF4ExactSlabOrderedPathVariance.lean:59` | Same original variance determinant for every full block permutation |
| `chronological_cost_crossing_bound` | `BF4ExactSlabChronologicalPathSum.lean:95` | The crossing count inside the actual cost obeys the area bound |
| `chronological_increment_energy_bound` | `BF4ExactSlabChronologicalPathSum.lean:115` | Correct physical slot, fresh next link, same completed residual |
| `original_chronological_path_energy_bound` | `BF4ExactSlabChronologicalPathSum.lean:135` | Finite sum of the actual per-step payments bounds original variance |

`chronologicalEnergyTerm` at
`lean/YMGap/Continuum/BF4ExactSlabChronologicalPathSum.lean:107` is a total Nat
function: it is zero outside k<N, but the theorem sums exclusively over
`List.range N`. The branch does not omit any physical update. The terminal
prefix has no next increment; no terminal area guard is required.

## Verification and independent review

Six final focused checks passed with one worker, a 20 GiB compiler ceiling,
12 GiB OS reserve and automatic safety monitoring. All 44 printed gates are
within {propext, Quot.sound}. Every check completed within its initial call;
there was no long-running job to poll. Manual checks of any future live heavy
job remain spaced about five minutes apart. No full-root build/audit/guard.

Final logs:

- `/tmp/ym-ordered-replica-20260930.log` (21 gates)
- `/tmp/ym-chronological-link-order-20260930.log` (9 gates)
- `/tmp/ym-ordered-path-cut-20260930.log` (4 gates)
- `/tmp/ym-ordered-path-energy-20260930.log` (3 gates)
- `/tmp/ym-ordered-path-variance-20260930.log` (1 gate)
- `/tmp/ym-chronological-path-sum-20260930.log` (6 gates)

Sol handled ordering and generic path proofs independently; verification
remained serialized. Luna reviewed normalization, link identity, exact finite
sum scope and absence of an assumed gap. No issue found. No new sorry, axiom,
analytic hypothesis or weakened frontier statement was introduced.

## Remaining frontier

The simplified centered Dirichlet coefficient
N*(prefixCap/headFloor)^(2C+12), with C=12*(extent+1)^3, is NOT yet a theorem
of this checkpoint. Common-factor cancellation, the uniform-in-link cost
majorization and the join to the existing centered Dirichlet statement remain.
Those are finite arithmetic/normalization tasks, not new gap assumptions.

Even the proposed area-dependent coefficient is inadequate for the required
spatial/scaling control. Neither this finite inequality nor its expected
corollary supplies the missing signed collective estimate or identifies the
conditional-update dynamics with OS time. Continuum survival, finite physical
mass, full QFT and all compact simple groups remain open. The canonical chart
state is unchanged and was not reprinted.
